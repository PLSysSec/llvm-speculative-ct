//===-- Blade.cpp - -------------------------------------------------------===//
//
// Maximilian Gallup's Bachelor Project at Vrije Universiteit Amsterdam 2023.
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//


#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/IntrinsicsX86.h"
#include <queue>
#include <stack>
#include <iostream>

using namespace llvm;


#define DEBUG_TYPE "blade"
#define BLADE_DEBUG 1
#define E(X) errs() << "🔴 " << X << "\n"
#define D(X)   if(BLADE_DEBUG) errs() << "🟣 " << X << "\n"
#define S(X)   if(BLADE_DEBUG) errs() << "🟢 " << X << "\n"
#define N(X)   if(BLADE_DEBUG) errs() << "   " << X << "\n"
#define RAW(X) errs() << X

STATISTIC(NumTransient, "Number of transient Nodes added.");
STATISTIC(NumStable, "Number of stable Nodes added.");
STATISTIC(NumLeaks, "Total number of distinct paths that leak secrets.");
STATISTIC(NumCuts, "Total number of cuts resulting in a protect statement.");

typedef SmallVector<Instruction*, 16> InstVec1D;
typedef SmallVector<InstVec1D, 16> InstVec2D;
typedef int dag_type;

/// @brief Used internally to construct dependency graph of all leaky instructions
class BladeNode {
  public:
    int id = 0;
    Instruction* I;
    BladeNode* parent;
    SmallVector<BladeNode*, 16> *children;
    BladeNode(Instruction *newI, BladeNode *newParent) {
      I = newI;
      parent = newParent;
      children = new SmallVector<BladeNode*, 16>();
    };
};

/// @brief Blade uses either lfences or SLH underneath the protect statement.
enum ProtectType {
  FENCE,
  SLH
};

/// @brief Returns true if the instruction is marked as Stable.
bool isStableInstruction(Instruction *Inst) {
  return Inst->hasMetadata("BLADE-S");
}

/// @brief Returns true if the instruction is marked as Transient.
bool isTransientInstruction(Instruction *Inst) {
  return Inst->hasMetadata("BLADE-T");
}

/// @brief Mark instruction idempotently as Stable
void markInstructionStable(Instruction *Inst) {
  if (!Inst->hasMetadata("BLADE-S")) {
    LLVMContext& C = Inst->getContext();
    MDNode* N = MDNode::get(C, MDString::get(C, "Blade Stable"));
    Inst->setMetadata("BLADE-S", N);
    NumStable++;
  }
}

/// @brief Mark instruction idempotently as Transient.
void markInstructionTransient(Instruction *Inst) {
  if (!Inst->hasMetadata("BLADE-T")) {
    LLVMContext& C = Inst->getContext();
    MDNode* N = MDNode::get(C, MDString::get(C, "Blade Transient"));
    Inst->setMetadata("BLADE-T", N);
    NumTransient++;
  }
}

/// @brief Labels the instruction as Transient if it's a Load or Call.
/// If the instruction is used as an index for a load operation, it will be marked Stable.
void markInstruction(Instruction *I) {
  if (I->getOpcode() == Instruction::Load || I->getOpcode() == Instruction::Call) {
    markInstructionTransient(I);
  }
  for (User *U : I->users()) {
    if (Instruction *II = dyn_cast<Instruction>(U)) {
      if (II->getOpcode() == Instruction::Load) {
        markInstructionStable(I);
      }
    }
  }
}

/// @brief Mark the instructions that use a function's arguments as transient.
void markArgs(Function &F) {
  for (Argument &A : F.args()) {
    if (Value *transient_value = dyn_cast<Value>(&A)) {
      for (User *U : transient_value->users()) {
        if (Instruction *I = dyn_cast<Instruction>(U)) {
          markInstructionTransient(I);
        }
      }
    }
  }
}

/// @brief Traverse graph in Post-Order and delete (free) all nodes to prevent a memory leak.
/// @param B Root node of graph.
void freeBladeNodes(BladeNode *B) {
  if (B->children->empty()) {
    delete(B->children);
    delete(B);
    return;
  }

  for (BladeNode *node : *B->children) {
    freeBladeNodes(node);
  }

  delete(B->children);
  delete(B);
  return;
}

/// @brief [UNUSED] Builds the DAG of BladeNodes that make up all Def-Use chains throughout the program,
/// we then save the stable leaf BladeNodes into a vector so that we can construct the correct
/// def-use chain going bottom up. This function works recursively.
/// @param I Instruction whose users will turn into children.
/// @param parent Pointer to parent instruction, starting transient instruction has NULL.
/// @param stable_insts Collection of stable instruction leaf nodes that we are interested in.
void findStableRec(Instruction *I, BladeNode *parent, SmallVector<BladeNode*, 16> *stable_insts) {
  for (User *U : I->users()) {
    if (Instruction *current_inst = dyn_cast<Instruction>(U)) {
      // Here we connect the new node to its parent via the constructor, and we make sure that
      // the parent is connected to its child via the `children` vector.
      auto new_node = new BladeNode(current_inst, parent);
      parent->children->push_back(new_node);

      // If we encounter a stable instruction, there is a leak. We can simply save this node into
      // a vector and then traverse the graph bottom up via the `parent` pointer to know the exact
      // def-use chain of the leak.
      if (isStableInstruction(current_inst)) {
        stable_insts->push_back(new_node);
      }

      // Recursive call with next instruction and the new node as the parent.
      findStableRec(current_inst, new_node, stable_insts);
    }
  }
}

/// @brief [UNUSED] Builds the DAG of BladeNodes that make up all Def-Use chains throughout the program,
/// we then save the stable leaf BladeNodes into a vector so that we can construct the correct
/// def-use chain going bottom up. This function works iteratively.
/// @param I Instruction whose users will turn into children.
/// @param parent Pointer to parent instruction, starting transient instruction has NULL.
/// @param stable_insts Collection of stable instruction leaf nodes that we are interested in.
void findStableIteratively(Instruction *start, BladeNode *parent, SmallVector<BladeNode*, 16> *stable_insts) {
  auto current_parent = parent;

  // We use a stack of iterators, so that we can make a Pre-Order graph traversal.
  // Increasing the iterator (iters.top()++) is the same as moving to the next
  // child of a given node.
  std::stack<llvm::Value::user_iterator> iters;
  iters.push(start->users().begin());

  while (true) {

    // Once all nodes have been visited, the stack will be empty, and we are finished.
    if (iters.size() == 0) {
      break;
    }

    if (iters.top().atEnd()) {
      // Looked at all children of a node so go up one node
      current_parent = current_parent->parent;
      iters.pop();

      // Check if we are already finished.
      if (iters.size() == 0) {
        break;
      }

      iters.top()++;
      continue;
    }
    auto user = *iters.top();

    if (Instruction* current_inst = dyn_cast<Instruction>(user)) {
      // Insert a node into the graph, if it's a stable instruction,
      // save it so that we can find the exact path later (by traversing the parents)
      auto new_node = new BladeNode(current_inst, current_parent);
      current_parent->children->push_back(new_node);
      if (isStableInstruction(current_inst)) {
        stable_insts->push_back(new_node);
      }

      if (current_inst->users().empty()) {
        // This node has no more users so we check the next child and going right.
        iters.top()++;
      } else {
        // There are still nodes to traverse so we go down.
        iters.push(current_inst->users().begin());
        current_parent = new_node;
      }
    }
  }
}

/// @brief [UNUSED] Walks through the Def-Use chain of the given instruction to identify all paths
/// from T->S. A path is given by a vector of instructions from stable instruction to
/// transient. These vectors are then collected into a 2D vector.
/// @param I The transient instruction to start looking from.
/// @param leaky_paths Collection of all secret leaking paths.
void gatherLeaks(Instruction *I, InstVec2D *leaky_paths) {
  // Since a leak can only come from a transient instruction, we can ignore all others
  if (isTransientInstruction(I)) {
    // For this instruction we will save all paths (made up via BladeNodes) that end
    // in a stable instruction.
    auto stable_instructions = SmallVector<BladeNode*, 16>();
    auto start = new BladeNode(I, NULL);
    // findStableRec(I, start, &stable_instructions);
    findStableIteratively(I, start, &stable_instructions);

    // Since we store the parent of each BladeNode, we can traverse the graph bottom
    // up from the stable instruction to the start, leaving us with only those instructions
    //  directly part of the def-use chain. This is necessary to prevent duplicates.
    for (BladeNode *B : stable_instructions) {
      auto a_leaky_path = InstVec1D();
      BladeNode* current = B;
      while (current->parent) {
        a_leaky_path.push_back(current->I);
        current = current->parent;
      }
      a_leaky_path.push_back(I);
      leaky_paths->push_back(a_leaky_path);
      NumLeaks++;
    }

    // Since we've accumulated all BladeNodes on the heap and we've alread saved the leaky path
    // of instructions, we must free all nodes in Post-Order traversal.
    freeBladeNodes(start);

  }
}

/// @brief Pretty print all instructions that make up the leaky paths.
/// @param leaky_paths 2D Vector of instruction pointers where the stable instrction comes first.
void printLeakyPaths(InstVec2D *leaky_paths) {
  int count = 1;
  for (InstVec1D S : *leaky_paths) {
    S("\tLeak " << count);
    for (Instruction* I : S) {
      D("\t\t" << *I);
    }
    count++;
  }
}

/// @brief Pretty print useful statistics summarizing overall analysis.
void printSummary() {
  S("--- Summary ---");
  N("\tTransient Marks: " << NumTransient);
  N("\tStable Marks: " << NumStable);
  N("\tTotal Leaks: " << NumLeaks);
  N("\tTotal Cuts: " << NumCuts);
}

/// @brief Used for command line data collection
void printSummaryData() {
  RAW("🟢 BladeSummaryData:" << NumTransient << "," << NumStable << "," << NumCuts << "\n");
}

/// @brief Print all instructions that make up the cutset.
void printCutSet(SmallSetVector<Instruction*, 16> *cutset) {
  S("--- Cutset ---");
  for (auto I : *cutset) {
    N("\t" << *I);
  }
}

/// @brief Frees a 2D array of ints by freeing each row first.
void freeGraph(dag_type **graph, int length) {
  for (int i = 0; i < length; i++) {
    free(graph[i]);
  }
  free(graph);
}

/// @brief Look up the the index of a given instruction within the set. This is
/// used to uniquely ID each instruction in the dependency graph.
int getInstructionIndex(SmallSetVector<Instruction*, 16> *set, Instruction *I) {
  // Number of instructions start counting from 1, so that we can add a Source Node
  // at index 0 of the final graph (and a sink node appended to the end as well).
  int index = 1;
  for (auto inst : *set) {
    if (inst == I) {
      return index;
    }
    index++;
  }
  return -1;
}

/// @brief Look up the the index of a given instruction within the set. This is
/// used to uniquely ID each instruction in the dependency graph.
int getInstructionIndex(InstVec1D &vec, Instruction *I) {
  // Number of instructions start counting from 1, so that we can add a Source Node
  // at index 0 of the final graph (and a sink node appended to the end as well).
  int index = 1;
  for (auto inst : vec) {
    if (inst == I) {
      return index;
    }
    index++;
  }
  return -1;
}

/// @brief Pretty print Matrix representation of graph.
void printGraph(dag_type **graph, int size) {
  for (int row = 0; row < size; row++) {
    RAW(row << ":\t[");
    for (int col = 0; col < size; col++) {
      RAW(graph[row][col] << ", ");
    }
    RAW("]\n");
  }
}

/// @brief Pretty print Matrix representation of graph, highlighting visited nodes.
void printGraph(dag_type **graph, bool visited[], int size) {
  for (int row = 0; row < size; row++) {
    if (visited[row]) {
      RAW("\033[31;1;4m" << row << ":\t[");
    } else {
      RAW(row << ":\t[");
    }
    for (int col = 0; col < size; col++) {
      RAW(graph[row][col] << ", ");
    }
    RAW("]\n\033[0m");
  }
}

/// @brief Traverses each leaky path in reverse order so that transient instructions come first
/// and stable instructions come last. The index of each instruction is its ID.
SmallSetVector<Instruction*, 16> aggregateInstructions(InstVec2D *leaky_paths) {
  // Iterate over each path in reverse order since sources (T) are at the back and
  // accumulate all instructions into a set and create Instruction -> ID mapping.
  auto mappings = SmallSetVector<Instruction*, 16>();
  for (InstVec1D path : *leaky_paths) {
    for (InstVec1D::reverse_iterator it = path.rbegin(); it != path.rend(); ++it) {
      auto I = *it;
      mappings.insert(I);
    }
  }

  return mappings;
}

/// @brief This data structure must be freed, use calloc to allocate a 2D array.
dag_type **allocateGraphDS(int num_vertices) {
  // D("\t\t Allocating " << num_vertices * sizeof(dag_type*) + num_vertices * sizeof(dag_type) << " bytes");
  dag_type **graph = (dag_type **)calloc(num_vertices, sizeof(dag_type *));
  for (int i = 0; i < num_vertices; i++) {
    graph[i] = (dag_type *)calloc(num_vertices, sizeof(dag_type));
  }
  return graph;
}

/// @brief [UNUSED] Iterates over all all leaky paths and builds matrix representation of dependency chain.
/// It also extends replaces each vertex X with vertex (X_i, X_o) where X_i is a vertex that keeps
/// all incoming edges and vertex X_o keeps all outgoing edges. There is a single edge between vertex
/// X_i and X_o in order for the Min Cut Algorithm to correctly identify the minimum cut. This leads
/// to a Matrix that is twice the size as the original.
void populateGraph(InstVec2D *leaky_paths, SmallSetVector<Instruction*, 16> *mappings, dag_type **graph, int num_vertices, int og_num_vertices) {
  // Internal to this function, we first make a matrix representation without changing each
  // vertex X to (X_i, X_o) - this graph must be freed before the function returns.
  dag_type **og_graph = allocateGraphDS(og_num_vertices);

  for (InstVec1D path : *leaky_paths) {
    for (int i = path.size() - 1; i >= 1; i--) {
      Instruction *current_instruction = path[i];
      Instruction *next_instruction = path[i-1];
      int current_index = getInstructionIndex(mappings, current_instruction);
      int next_index = getInstructionIndex(mappings, next_instruction);
      og_graph[current_index][next_index] = 1;
    }
  }

  for (Instruction *I : *mappings) {
    // Link the source node to all transient instructions and the sink node to all stable instructions.
    if (isTransientInstruction(I)) {
      auto i = getInstructionIndex(mappings, I);
      og_graph[0][i] = 1;
    } else if (isStableInstruction(I)) {
      auto i = getInstructionIndex(mappings, I);
      og_graph[i][og_num_vertices - 1] = 1;
    }
  }

  // At this point `og_graph` is an N x N matrix representation of the dependency graph with source
  // and sink node. However, now we need to extend this graph to be a 2N x 2N matrix where each vertex
  // X becomes (X_i, X_o) with X_i having all incoming edges of X and X_o having all outgoing edges.
  // We need to skip the source node, hence start at index 1.
  for (int row = 1; row < og_num_vertices - 1; row++) {
    int target_row = (row * 2) - 1;
    graph[target_row][target_row + 1] = 1; // Link X_i to X_o

    // Modify the index of all outgoing edges of the current vertex to be (index * 2) - 1.
    for (int col = 0; col < og_num_vertices; col++) {
      if (og_graph[row][col] == 1) {
        graph[target_row + 1][(col * 2) - 1] = 1;
      }
    }
  }

  // Update the source node's edges (index 0) to point to correct locations.
  for (int col = 0; col < og_num_vertices - 1; col++) {
    if (og_graph[0][col] == 1) {
      graph[0][(col * 2) - 1] = 1;
    }
  }

  freeGraph(og_graph, og_num_vertices);
}

/// @brief Iterates over all all leaky paths and builds matrix representation of dependency chain.
/// It also extends replaces each vertex X with vertex (X_i, X_o) where X_i is a vertex that keeps
/// all incoming edges and vertex X_o keeps all outgoing edges. There is a single edge between vertex
/// X_i and X_o in order for the Min Cut Algorithm to correctly identify the minimum cut. This leads
/// to a Matrix that is twice the size as the original.
void populateGraph(InstVec1D &insts, dag_type **graph, int num_vertices, int og_num_vertices) {
  // Internal to this function, we first make a matrix representation without changing each
  // vertex X to (X_i, X_o) - this graph must be freed before the function returns.
  dag_type **og_graph = allocateGraphDS(og_num_vertices);

  for (Instruction *I : insts) {
    if (I->hasNUsesOrMore(1)) {
      for (User *U : I->users()) {
        if (Instruction *II = dyn_cast<Instruction>(U)) {
          auto row = getInstructionIndex(insts, I);
          auto col = getInstructionIndex(insts, II);
          if (row == -1 || col == -1) {
            continue;
          }
          og_graph[row][col] = 1;
        }
      }
    }
  }

  for (Instruction *I : insts) {
    if (isTransientInstruction(I)) {
      auto i = getInstructionIndex(insts, I);
      og_graph[0][i] = 1;
    } else if (isStableInstruction(I)) {
      auto i = getInstructionIndex(insts, I);
      og_graph[i][og_num_vertices - 1] = 1;
    }
  }

  for (int row = 1; row < og_num_vertices - 1; row++) {
    int target_row = (row * 2) - 1;
    graph[target_row][target_row + 1] = 1; // Link X_i to X_o

    // Modify the index of all outgoing edges of the current vertex to be (index * 2) - 1.
    for (int col = 0; col < og_num_vertices; col++) {
      if (og_graph[row][col] == 1) {
        graph[target_row + 1][(col * 2) - 1] = 1;
      }
    }
  }

  // Update the source node's edges (index 0) to point to correct locations.
  for (int col = 0; col < og_num_vertices - 1; col++) {
    if (og_graph[0][col] == 1) {
      graph[0][(col * 2) - 1] = 1;
    }
  }
  // printGraph(og_graph, og_num_vertices);
  freeGraph(og_graph, og_num_vertices);

}

/// @brief Performs Breadth-First-Search on residual graph
/// @returns whether or not target can be reached
bool bfs(dag_type **residual_graph, int s, int t, int parent[], int num_vertices) {
  bool *visited = (bool*) calloc(num_vertices, sizeof(bool));
  std::queue<int> traversed_so_far;
  traversed_so_far.push(s);
  visited[s] = true;
  parent[s] = -1;

  while (!traversed_so_far.empty()) {
    int current = traversed_so_far.front();
    traversed_so_far.pop();

    for (int v = 0; v < num_vertices; v++) {
      if (visited[v]==false && residual_graph[current][v] > 0){
        traversed_so_far.push(v);
        parent[v] = current;
        visited[v] = true;
      }
    }
  }

  auto res = visited[t] == true;
  free(visited);

  return res;
}

/// @brief Performs Deapth-First-Search recursively on residual graph and updates
/// visited[] array where the indices of visited allign with the IDs of instructions
void dfs(dag_type **residual_graph, int s, bool visited[], int num_vertices) {
  visited[s] = true;
  for (int i = 0; i < num_vertices; i++) {
    if (residual_graph[s][i] && !visited[i]) {
      dfs(residual_graph, i, visited, num_vertices);
    }
  }
}

/// @brief Performs a customized version of Ford Fulkerson's Max Flow Min Cut Algorithm
/// to find the minimal cuts of the dependency graph.
SmallSetVector<int, 16> minCut(dag_type **graph, int source, int sink, int num_vertices) {
  int u, v;
  dag_type **residual_graph = allocateGraphDS(num_vertices);
  for (u = 0; u < num_vertices; u++) {
    for (v = 0; v < num_vertices; v++) {
      residual_graph[u][v] = graph[u][v];
    }
  }

  // Keep track of the parent when performing Breadth-First-Search to build the residual graph.
  // However, potentially unnecessary due to the fact that resulting residual graph is equivalent
  // to the transpose of the original graph.
  int *parent = (int*) calloc(num_vertices, sizeof(int));
  while (bfs(residual_graph, source, sink, parent, num_vertices)) {
    dag_type path_flow = INT_MAX;
    for (v = sink; v != source; v = parent[v]) {
      u = parent[v];
      path_flow = std::min(path_flow, residual_graph[u][v]);
    }

    // Update residual capacities and reverse the direction of the edges.
    for (v = sink; v != source; v=parent[v]) {
      u = parent[v];
      residual_graph[u][v] -= path_flow;
      residual_graph[v][u] += path_flow;
    }
  }

  free(parent);

  // Perform a Depth-First-Search on residual garph and keep track of which nodes are reachable.
  bool *visited = (bool*) calloc(num_vertices, sizeof(bool));
  dfs(residual_graph, source, visited, num_vertices);

  auto cutset_ids = SmallSetVector<int, 16>();

  // Within the following loop, i and j will represent two vertices that form a leak. We are
  // interested in the node that is represented by j, since it is the instruction that needs
  // to be protected.
  for (int i = 0; i < num_vertices; i++) {
    for (int j = 0; j < num_vertices; j++) {
        if (visited[i] && !visited[j] && graph[i][j]) {
          // Since each vertex previously turned into two, the index of an instruction at vertex
          // X_o corresponds to to index / 2.
          cutset_ids.insert(((int)j) / 2);
        }
    }
  }

  // printGraph(graph, num_vertices);

  free(visited);
  freeGraph(residual_graph, num_vertices);

  return cutset_ids;
}

/// @brief Runs a slimmed down version of Ford-Fulkerson's Max Flow Min Cut Algorithm to find optimal cuts.
/// @return The set of instructions where a protect statement must be place infront of to prevent secret leaks.
SmallSetVector<Instruction*, 16> findCutSet(InstVec2D *leaky_paths) {
  // We accumulate all instructions into a set and assign them a
  // unique ID based on their index position within the set.
  // D("\tAggregating Instructions");
  SmallSetVector<Instruction*, 16> mappings = aggregateInstructions(leaky_paths);

  // The total number of vertices in the graph will be `size + 2` because of the
  // Source and Sink node that get added. We differentiate between the "original"
  // number of vertices, and those that we perform the min cut algorithm on, since
  // we require each vertex to be extended with an artifical dummy vertex making
  // the total amount of vertices (size * 2) + 2;
  int og_num_vertices = mappings.size() + 2;
  int num_vertices = (mappings.size() * 2) + 2;

  // We represent the graph in the form of a matrix where a 1 in row i and column j
  // indicates there is an edge from vertex i to vertex j.
  dag_type **graph = allocateGraphDS(num_vertices);
  // D("\tPopulating Graph");
  populateGraph(leaky_paths, &mappings, graph, num_vertices, og_num_vertices);

  // Run Ford-Fulkerson's Max Flow Min Cut algorithm to find which instructions need
  // to be protected to prevent leaks.
  auto cutset_ids = minCut(graph, 0, num_vertices - 1, num_vertices);
  auto cutset = SmallSetVector<Instruction*, 16>();

  for (auto n : cutset_ids) {
    cutset.insert(mappings[n]);
    NumCuts++;
  }

  freeGraph(graph, num_vertices);

  return cutset;
}

/// @brief Builds a matrix representation of the program's dependency chain and
/// runs Ford-Fulkerson's Max-Flow Min-Cut Algorithm over it to find the cutset.
SmallSetVector<Instruction*, 16> findCutSet(Function &F) {
  int num_instructions = F.getInstructionCount();

  auto table = InstVec1D();
  table.resize(num_instructions);

  auto cutset = SmallSetVector<Instruction*, 16>();
  if (num_instructions == 0) {
    return cutset;
  }

  auto current_inst = 0;
  for (BasicBlock &BB : F) {
    for (Instruction &I : BB) {
      // super weird bug during compilation
      if (current_inst == num_instructions) {
        break;
      }
      table[current_inst] = &I;
      current_inst++;
    }
  }

  int og_num_vertices = num_instructions + 2;
  int num_vertices = (num_instructions * 2) + 2;
  dag_type **graph = allocateGraphDS(num_vertices);

  populateGraph(table, graph, num_vertices, og_num_vertices);

  auto cutset_ids = minCut(graph, 0, num_vertices - 1, num_vertices);


  for (auto n : cutset_ids) {
    cutset.insert(table[n]);
    NumCuts++;
  }

  freeGraph(graph, num_vertices);

  return cutset;
}

/// @brief Inserts protections right after leaky instructions given by cutset to defend
/// against speculative leaks.
/// @param prot see enum ProtectType
bool insertProtections(Function &F, SmallSetVector<Instruction*, 16> *cutset, ProtectType prot) {
  if (prot == FENCE) {
    for (Instruction *I : *cutset) {
      Function *fence_fn = Intrinsic::getDeclaration(F.getParent(), Intrinsic::x86_sse2_lfence);
      CallInst *fence_call = CallInst::Create(fence_fn);
      fence_call->insertAfter(I);
    }
    return true;
  } else if (prot == SLH) {
    E("Blade-SLH not yet implemented");
  }
  return false;
}

/// @brief Inserts protections right after leaky instructions given by cutset to defend
/// against speculative leaks.
/// @param prot see enum ProtectType
bool insertProtectionsBefore(Function &F, SmallSetVector<Instruction*, 16> *cutset, ProtectType prot) {
  if (prot == FENCE) {
    for (Instruction *I : *cutset) {
      Function *fence_fn = Intrinsic::getDeclaration(F.getParent(), Intrinsic::x86_sse2_lfence);
      CallInst *fence_call = CallInst::Create(fence_fn);
      fence_call->insertBefore(I);
    }
    return true;
  } else if (prot == SLH) {
    E("Blade-SLH not yet implemented");
  }
  return false;
}

/// @brief Marks all transient and stable instructions in a given function.
void placeMarkings(Function &F) {
  for (BasicBlock &BB : F) {
    for (Instruction &I : BB) {
      markInstruction(&I);
    }
  }
  markArgs(F);
}

/// @brief Wrapper that makes it easier to change implementations of the leaky-gathering method.
void gatherLeaksWrapper(Function &F, InstVec2D *leaky_paths) {
  for (BasicBlock &BB : F) {
    for (Instruction &I : BB) {
      gatherLeaks(&I, leaky_paths);
    }
  }
}

/// @brief Performs the full Blade algorithm within the scope of a single function.
void runBlade(Function &F) {
  if (F.size() < 1) {
    return;
  }

  placeMarkings(F);

  // use this to show leaky paths in paper
  // auto leaky_paths = InstVec2D();
  // gatherLeaksWrapper(F, &leaky_paths);
  // printLeakyPaths(&leaky_paths);
  // auto cutset = findCutSet(&leaky_paths);

  auto cutset = findCutSet(F);

  insertProtections(F, &cutset, FENCE);
}

/// @brief Naively places fences to all transient instructions to prevent speculative leaks.
void runFenceEverywhere(Function &F) {
  if (F.size() < 1) {
    return;
  }
  placeMarkings(F);
  auto cutset = SmallSetVector<Instruction*, 16>();
  for (BasicBlock &BB : F) {
    for (Instruction &I : BB) {
      if (isStableInstruction(&I)) {
        cutset.insert(&I);
        NumLeaks++;
      }
    }
  }
  NumCuts += cutset.size();
  insertProtectionsBefore(F, &cutset, FENCE);
}


namespace {
  struct BladePass : public PassInfoMixin<BladePass> {

    PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM) {
      runBlade(F);
      // printSummary();
      // printSummaryData();
      return PreservedAnalyses::all();
    }
  };
} // namespace



PassPluginLibraryInfo getPassPluginInfo() {
  const auto callback = [](PassBuilder &PB) {
      PB.registerOptimizerLastEPCallback([&](ModulePassManager &MPM, auto) {
        MPM.addPass(createModuleToFunctionPassAdaptor(BladePass()));

        return true;
      });
  };

  return {LLVM_PLUGIN_API_VERSION, "Blade", "0.0.1", callback};
}

extern "C" LLVM_ATTRIBUTE_WEAK PassPluginLibraryInfo llvmGetPassPluginInfo() {
  return getPassPluginInfo();
}
