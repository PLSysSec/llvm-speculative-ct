//===-- Blade.cpp - -------------------------------------------------------===//
//
// Maximilian Gallup's Bachelor Project at Vrije Universiteit Amsterdam 2023.
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "Blade.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/DirectedGraph.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/IntrinsicsX86.h"
#include "llvm/Support/Casting.h"
#include <queue>
#include <stack>
#include <iostream>

using namespace llvm;

#define DEBUG_TYPE "matt"
#define D(X) DEBUG_WITH_TYPE("matt", errs() << X)

STATISTIC(NumTransient, "Number of transient Nodes added.");
STATISTIC(NumStable, "Number of stable Nodes added.");
STATISTIC(NumLeaks, "Total number of distinct paths that leak secrets.");
STATISTIC(NumCuts, "Total number of cuts resulting in a protect statement.");

typedef SmallVector<Instruction*> InstVec1D;
typedef SmallVector<InstVec1D> InstVec2D;
typedef int dag_type;

bool BladeEdge::operator==(const BladeEdge other) const {
  return *(other.target) == *target;
}

bool BladeEdge::operator<(const BladeEdge& other) const {
  return *target < *(other.target);
}

bool OldBladeNode::operator==(const OldBladeNode& other) const {
  return isEqual(other);
}

bool OldBladeNode::operator<(const OldBladeNode& other) const {
  if (getKind() != other.getKind()) {
    return getKind() < other.getKind();
  } else {
    return this->isLessThan(other);
  }
}

void OldBladeNode::addEdge(BladeEdge edge) {
  edges.insert(edge);
}

void OldBladeNode::removeEdge(BladeEdge edge) {
  edges.erase(edge);
}

bool OldBladeNode::hasEdgeTo(const OldBladeNode &other) const {
  for (BladeEdge edge : edges) {
    if (*(edge.target) == other) {
      return true;
    }
  }
  return false;
}

void OldBladeNode::outputEdges(raw_ostream& os) const {
  for (BladeEdge edge : this->edges) {
    if (edge.weight > 0) {
      os << *this << " -> " << *(edge.target) << ";\n";
    }
  }
}

class DistinguishedNode : public OldBladeNode {
public:
  unsigned int id;

  DistinguishedNode(unsigned int id)
    : OldBladeNode(BNK_DistinguishedNode),
      id(id) {}

  static bool classof(const OldBladeNode *node) {
    return node->getKind() == BNK_DistinguishedNode;
  }

  bool isEqual(const OldBladeNode& other) const {
    if (auto* cast_other = dyn_cast<DistinguishedNode>(&other)) {
      return id == cast_other->id;
    } else {
      return false;
    }
  }

  bool isLessThan(const OldBladeNode& other) const {
    if (auto* cast_other = dyn_cast<DistinguishedNode>(&other)) {
      return id < cast_other->id;
    } else {
      return false;
    }
  }

  raw_ostream& outputNode(raw_ostream& os) const {
    return os << id;
  }
};

class OldValueDefNode : public OldBladeNode {
public:
  Instruction* inst;

  OldValueDefNode(Instruction* inst)
    : OldBladeNode(BNK_ValueDefNode), inst(inst) {}

  static bool classof(const OldBladeNode *node) {
    return node->getKind() == BNK_ValueDefNode;
  }

  bool isEqual(const OldBladeNode& other) const {
    if (auto* cast_other = dyn_cast<OldValueDefNode>(&other)) {
      return inst == cast_other->inst;
    } else {
      return false;
    }
  }

  bool isLessThan(const OldBladeNode& other) const {
    if (auto* cast_other = dyn_cast<OldValueDefNode>(&other)) {
      return inst < cast_other->inst;
    } else {
      return false;
    }
  }

  raw_ostream& outputNode(raw_ostream& os) const {
    return os << '"' << "defn: " << *inst << '"';
  }
};

class InstSinkNodeOld : public OldBladeNode {
public:
  Instruction* inst;

  InstSinkNodeOld(Instruction* inst)
    : OldBladeNode(BNK_InstSinkNode), inst(inst) {}

  static bool classof(const OldBladeNode *node) {
    return node->getKind() == BNK_InstSinkNode;
  }

  bool isEqual(const OldBladeNode& other) const {
    if (auto* cast_other = dyn_cast<InstSinkNodeOld>(&other)) {
      return inst == cast_other->inst;
    } else {
      return false;
    }
  }

  bool isLessThan(const OldBladeNode& other) const {
    if (auto* cast_other = dyn_cast<InstSinkNodeOld>(&other)) {
      return inst < cast_other->inst;
    } else {
      return false;
    }
  }

  raw_ostream& outputNode(raw_ostream& os) const {
    return os << '"' << "sink: " << *inst << '"';
  }
};

// struct BladeNodePtrComp
// {
//   bool operator()(const BladeNode* &lhs, const BladeNode* &rhs) const {
//     return *lhs < *rhs;
//   }
// };

class BladeNode {
public:
  virtual size_t index(ValueMap<Instruction*, size_t> &instruction_to_index) const = 0;
  virtual raw_ostream& outputNode(raw_ostream& os) const = 0;
  friend raw_ostream& operator<<(raw_ostream& os, BladeNode const &node) {
    return node.outputNode(os);
  }
};

class SourceNode : public BladeNode {
public:
  size_t source_index;

  SourceNode(size_t source_index)
    : source_index(source_index) {}

  size_t index(ValueMap<Instruction*, size_t> &instruction_to_index) const {
    return source_index;
  }

  raw_ostream& outputNode(raw_ostream& os) const {
    return os << "source";
  }
};

class SinkNode : public BladeNode {
public:
  size_t sink_index;

  SinkNode(size_t sink_index)
    : sink_index(sink_index) {}

  size_t index(ValueMap<Instruction*, size_t> &instruction_to_index) const {
    return sink_index;
  }

  raw_ostream& outputNode(raw_ostream& os) const {
    return os << "sink";
  }
};

class ValueDefNode : public BladeNode {
public:
  Instruction* inst;

  ValueDefNode(Instruction* inst)
    : inst(inst) {}

  size_t index(ValueMap<Instruction*, size_t> &instruction_to_index) const {
    return instruction_to_index[inst] * 2;
  }

  raw_ostream& outputNode(raw_ostream& os) const {
    return os << '"' << "defn: " << *inst << '"';
  }
};

class InstSinkNode : public BladeNode {
public:
  Instruction* inst;

  InstSinkNode(Instruction* inst)
    : inst(inst) {}

  size_t index(ValueMap<Instruction*, size_t> &instruction_to_index) const {
    return instruction_to_index[inst] * 2 + 1;
  }

  raw_ostream& outputNode(raw_ostream& os) const {
    return os << '"' << "sink: " << *inst << '"';
  }
};

class NewBladeGraph {
public:
  using edge_iterator = typename std::vector<bool>::iterator;

private:
  std::vector<bool> edges;
  ValueMap<Instruction*, size_t> instruction_to_index;
  std::vector<Instruction*> index_to_instruction;

  size_t num_nodes;
  SourceNode source_node = SourceNode(0);
  SinkNode sink_node = SinkNode(0);

public:
  NewBladeGraph(Function &F) {
    size_t num_insts = 0;
    for (BasicBlock &BB : F) {
      for (Instruction &I : BB) {
        num_insts++;
      }
    }
    num_nodes = num_insts * 2 + 2;
    edges.reserve(num_nodes * num_nodes);
    std::fill_n(std::back_inserter(edges), num_nodes * num_nodes, 0);
    source_node = SourceNode(num_nodes - 2);
    sink_node = SinkNode(num_nodes - 1);
    index_to_instruction.reserve(num_insts);

    size_t ii = 0;
    for (BasicBlock &BB : F) {
      for (Instruction &I : BB) {
        index_to_instruction.push_back(&I);
        instruction_to_index[&I] = ii;
        ii++;
      }
    }
  }

  size_t nodeIndex(const BladeNode &node) {
    return node.index(instruction_to_index);
  }

  edge_iterator edgesBegin(const BladeNode &node) {
    return edges.begin() + (nodeIndex(node) * num_nodes);
  }

  edge_iterator edgesEnd(const BladeNode &node) {
    return edges.begin() + (nodeIndex(node) * num_nodes) + num_nodes;
  }

  bool getEdge(const BladeNode &from, const BladeNode &to) {
    return *(edgesBegin(from) + nodeIndex(to));
  }

  void addEdge(const BladeNode &from, const BladeNode &to) {
    *(edgesBegin(from) + nodeIndex(to)) = 1;
  }

  void markAsSource(Instruction* inst) {
    addEdge(source_node, ValueDefNode(inst));
  }

  void markAsSink(Instruction* inst) {
    addEdge(InstSinkNode(inst), sink_node);
  }

  raw_ostream& outputGraph(raw_ostream& os) {
    os << "digraph {" << '\n';

    for (Instruction* from_inst : index_to_instruction) {
      for (Instruction* to_inst : index_to_instruction) {
        ValueDefNode fromDef = ValueDefNode(from_inst);
        InstSinkNode fromSink = InstSinkNode(from_inst);
        ValueDefNode toDef = ValueDefNode(to_inst);
        InstSinkNode toSink = InstSinkNode(to_inst);
        for (auto from : std::initializer_list<BladeNode*>{&fromDef, &fromSink}) {
          for (auto to : std::initializer_list<BladeNode*>{&toDef, &toSink}) {
            if (getEdge(*from, *to)) {
              os << *from << " -> " << *to << ';' << '\n';
            }
          }
        }
      }
    }
    for (Instruction* node_inst : index_to_instruction) {
      ValueDefNode nodeDef = ValueDefNode(node_inst);
      InstSinkNode nodeSink = InstSinkNode(node_inst);
      for (auto node : std::initializer_list<BladeNode*>{&nodeDef, &nodeSink}) {
        if (getEdge(source_node, *node)) {
          os << source_node << " -> " << *node << ';' << '\n';
        }
        if (getEdge(sink_node, *node)) {
          os << sink_node << " -> " << *node << ';' << '\n';
        }
        if (getEdge(*node, source_node)) {
          os << *node << " -> " << source_node << ';' << '\n';
        }
        if (getEdge(*node, sink_node)) {
          os << *node << " -> " << sink_node << ';' << '\n';
        }
      }
    }
    if (getEdge(source_node, sink_node)) {
      os << source_node << " -> " << sink_node << ';' << '\n';
    }
    if (getEdge(sink_node, source_node)) {
      os << sink_node << " -> " << source_node << ';' << '\n';
    }


    return os << '}';
  }

  friend raw_ostream& operator<<(raw_ostream& os, NewBladeGraph &graph) {
    return graph.outputGraph(os);
  }
};

class BladeGraph {
private:
  SmallVector<OldBladeNode*> nodes;
  DistinguishedNode source_node;
  DistinguishedNode sink_node;

public:
  using iterator = typename SmallVector<OldBladeNode*>::iterator;
  using const_iterator = typename SmallVector<OldBladeNode*>::const_iterator;
  using reverse_iterator = typename SmallVector<OldBladeNode*>::reverse_iterator;
  using const_reverse_iterator = typename SmallVector<OldBladeNode*>::const_reverse_iterator;


public:
  BladeGraph()
    : nodes(SmallVector<OldBladeNode*>()),
      source_node(DistinguishedNode(0)),
      sink_node(DistinguishedNode(1))
  {
    addNode(source_node);
    addNode(sink_node);
  }

  // ~BladeGraph() {
  //   for (BladeNode* node : nodes) {
  //     delete node;
  //   }
  // }

  void addEdge(OldBladeNode &from, OldBladeNode &to) {
    addEdge(from, to, 1);
  }

  void addEdge(OldBladeNode &from, OldBladeNode &to, unsigned int weight) {
    iterator from_ptr = findNode(from);
    assert((from_ptr != end()) && "from node missing");
    (*from_ptr)->addEdge(BladeEdge(weight, &to));
  }

  void addEdge(iterator from, iterator to) {
    addEdge(from, to, 1);
  }

  void addEdge(iterator from, iterator to, unsigned int weight) {
    (*from)->addEdge(BladeEdge(weight, *to));
  }

  // INVARIANT: don't add nodes multiple times
  void addNode(OldBladeNode &node) {
    if (findNode(node) == end()) {
      nodes.push_back(&node);
    }
  }

  // std::pair<iterator, iterator> findNodes(const BladeNode &node1, const BladeNode &node2) {
  //   iterator first = end();
  //   iterator second = end();
  //   for (iterator node = begin(); node != end(); ++node) {
  //     if (**node == node1 && first == end()) {
  //       first = node;
  //     }
  //     if (**node == node2 && second == end()) {
  //       second = node;
  //     }
  //     if (first != end() && second != end()) {
  //       break;
  //     }
  //   }
  //   return std::pair<>(first, second);
  // }

  iterator findNode(const OldBladeNode &node) {
    return find_if(nodes, [&node](const OldBladeNode *other) { return *other == node; });
  }

  const_iterator findNode(const OldBladeNode &node) const {
    return const_cast<iterator>(static_cast<const BladeGraph &>(*this).findNode(node));
  }

  void addDefinitionNode(Instruction* inst) {
    OldValueDefNode* value_def_node = new OldValueDefNode(inst);
    addNode(*value_def_node);
  }

  InstSinkNodeOld* addInstSinkNode(Instruction* inst) {
    InstSinkNodeOld* inst_sink_node = new InstSinkNodeOld(inst);
    addNode(*inst_sink_node);
    addEdge(*inst_sink_node, sink_node);
    return inst_sink_node;
  }

  void addEdgeFromValueToNode(Instruction* value_inst, OldBladeNode* blade_node) {
    OldBladeNode** value_node = findNode(OldValueDefNode(value_inst));
    if (value_node != end()) {
      addEdge(**value_node, *blade_node);
    }
  }

  void addEdgeFromValueToValue(Instruction* from_inst, Instruction* to_inst) {
    OldBladeNode** from_node = findNode(OldValueDefNode(from_inst));
    if (from_node != end()) {
      OldBladeNode** to_node = findNode(OldValueDefNode(to_inst));
      if (to_node != end()) {
        addEdge(from_node, to_node);
      }
    }
  }

  void markAsSource(Instruction* value_inst) {
    OldBladeNode** value_node = findNode(OldValueDefNode(value_inst));
    if (value_node != end()) {
      addEdge(source_node, **value_node);
    }
  }

    // /// Mark the given `Value` as a source.
    // fn mark_as_source(&mut self, src: Value) {
    //     let node = self.bladenode_to_node_map[&BladeNode::ValueDef(src)];
    //     self.graph.add_edge(self.source_node, node);
    // }

    // /// Add an edge from the given `Node` to the given `Value`
    // fn add_edge_from_node_to_value(&mut self, from: Node<usize>, to: Value) {
    //     let value_node = self.bladenode_to_node_map[&BladeNode::ValueDef(to)];
    //     self.graph.add_edge(from, value_node);
    // }

    // /// Add an edge from the given `Value` to the given `Node`
    // fn add_edge_from_value_to_node(&mut self, from: Value, to: Node<usize>) {
    //     let value_node = self.bladenode_to_node_map[&BladeNode::ValueDef(from)];
    //     self.graph.add_edge(value_node, to);
    // }

    // /// Add a new sink node for the given `inst`
    // fn add_sink_node_for_inst(&mut self, inst: Inst) -> Node<usize> {
    //     let inst_sink_node = self.graph.add_node();
    //     self.node_to_bladenode_map
    //         .insert(inst_sink_node, BladeNode::Sink(inst));
    //     self.bladenode_to_node_map
    //         .insert(BladeNode::Sink(inst), inst_sink_node);
    //     self.graph.add_edge(inst_sink_node, self.sink_node);
    //     inst_sink_node
    // }

  iterator begin() {
    return nodes.begin();
  }

  const_iterator begin() const {
    return nodes.begin();
  }

  iterator end() {
    return nodes.end();
  }

  const_iterator end() const {
    return nodes.end();
  }

  reverse_iterator rbegin() {
    return nodes.rbegin();
  }

  const_reverse_iterator rbegin() const {
    return nodes.rbegin();
  }

  reverse_iterator rend() {
    return nodes.rend();
  }

  const_reverse_iterator rend() const {
    return nodes.rend();
  }

  friend raw_ostream& operator<<(raw_ostream& os, BladeGraph const &graph) {
    os << "digraph {" << '\n';
    for (const_iterator node = graph.begin(); node != graph.end(); ++node) {
      os << **node << ';' << '\n';
    }

    for (const_iterator node = graph.begin(); node != graph.end(); ++node) {
      (*node)->outputEdges(os);
    }

    return os << '}';
  }
};

/// @brief Blade uses either lfences or SLH underneath the protect statement.
enum ProtectType {
  FENCE,
  // SLH
};

/// @brief Pretty print useful statistics summarizing overall analysis.
void printSummary() {
  // S("--- Summary ---");
  // N("\tTransient Marks: " << NumTransient);
  // N("\tStable Marks: " << NumStable);
  // N("\tTotal Leaks: " << NumLeaks);
  // N("\tTotal Cuts: " << NumCuts);
}

/// @brief Used for command line data collection
void printSummaryData() {
  D("BladeSummaryData: " << "{" << "NumTransient: " << NumTransient << ", " << "NumStable: " << NumStable << ", " << "NumCuts: " << NumCuts << "}" << "\n");
}

/// @brief Print all instructions that make up the cutset.
void printCutSet(SmallSetVector<Instruction*, 16> *cutset) {
  // S("--- Cutset ---");
  // for (auto I : *cutset) {
  //   N("\t" << *I);
  // }
}

/// @brief Pretty print Matrix representation of graph.
void printGraph(dag_type **graph, int size) {
  // RAW("digraph {\n");

  // for (int row = 0; row < size; row++) {
  //   for (int col = 0; col < size; col++) {
  //     if (graph[row][col] > 0) {
  //       RAW(row << " -> " << col <<";" << " ");
  //     }
  //   }
  // }
  // RAW("}\n");
}

/// @brief Pretty print Matrix representation of graph, highlighting visited nodes.
void printGraph(dag_type **graph, bool visited[], int size) {
  // for (int row = 0; row < size; row++) {
  //   if (visited[row]) {
  //     RAW("\033[31;1;4m" << row << ":\t[");
  //   } else {
  //     RAW(row << ":\t[");
  //   }
  //   for (int col = 0; col < size; col++) {
  //     RAW(graph[row][col] << ", ");
  //   }
  //   RAW("]\n\033[0m");
  // }
}

struct BladeGraphInsertVisitor : public InstVisitor<BladeGraphInsertVisitor> {
  NewBladeGraph &graph;

  BladeGraphInsertVisitor(NewBladeGraph &graph)
    : graph(graph) {}

  void handlePointerOperationAsSink(Instruction &I, Value* pointer_operand) {
    graph.markAsSink(&I);

    if (auto *pointer_inst = dyn_cast<Instruction>(pointer_operand)) {
      graph.addEdge(ValueDefNode(pointer_inst), InstSinkNode(&I));
    }
  }

  void handleAllOperandsAsSink(Instruction &I) {
    graph.markAsSink(&I);

    for (Use* operand = I.op_begin(); operand != I.op_end(); ++operand) {
      if (auto *operand_inst = dyn_cast<Instruction>(operand)) {
        graph.addEdge(ValueDefNode(operand_inst), InstSinkNode(&I));
      }
    }
  }

  void visitLoadInst(LoadInst &I) {
    // loads are both sources (their loaded values) and sinks (their addresses)
    // except for fills, which don't have sinks

    Value* pointer_operand = I.getPointerOperand();

    // handle load as a source
    if (!isa<Constant>(pointer_operand)) {
      graph.markAsSource(&I);
    }

    handlePointerOperationAsSink(I, pointer_operand);
  }

  void visitStoreInst(StoreInst &I) {
    // stores are just sinks
    // TODO: handle the `if store_values_are_sinks` from wasmtime-blade

    handlePointerOperationAsSink(I, I.getPointerOperand());
  }

  void visitAtomicCmpXchgInst(AtomicCmpXchgInst &I) {
    handlePointerOperationAsSink(I, I.getPointerOperand());
  }

  void visitAtomicRMWInst(AtomicRMWInst &I) {
    handlePointerOperationAsSink(I, I.getPointerOperand());
  }

  // void visitSelectInst(SelectInst &I) {
  // }

  // void visitMemSetInst(MemSetInst &I) {
  // }

  // void visitMemSetInlineInst(MemSetInlineInst &I) {
  // }

  // void visitMemCpyInst(MemCpyInst &I) {
  // }

  // void visitMemCpyInlineInst(MemCpyInlineInst &I) {
  // }

  // void visitMemMoveInst(MemMoveInst &I) {
  // }

  // void visitMemTransferInst(MemTransferInst &I) {
  // }

  // void visitMemIntrinsic (MemIntrinsic &I) {
  // }

  // void visitIntrinsicInst(IntrinsicInst &I) {
  // }

  void visitReturnInst(ReturnInst &I) {
    handleAllOperandsAsSink(I);
  }

  void visitBranchInst(BranchInst &I) {
    if (I.isConditional()) {
      handleAllOperandsAsSink(I);
    }
  }

  void visitSwitchInst(SwitchInst &I) {
    handleAllOperandsAsSink(I);
  }

  void visitIndirectBrInst(IndirectBrInst &I) {
    handleAllOperandsAsSink(I);
  }

  void visitCallBase(CallBase &I) {
    handleAllOperandsAsSink(I);
  }

  // void visitInstruction(Instruction &I) {
  // }
};


NewBladeGraph* buildBladeGraph(Function &F) {
  NewBladeGraph* graph = new NewBladeGraph(F);

  BladeGraphInsertVisitor insertVisitor = BladeGraphInsertVisitor(*graph);
  insertVisitor.visit(F);

  // add def-use edges
  for (BasicBlock &BB : F) {
    for (Instruction &I : BB) {
      for (User *U : I.users()) {
        if (auto *user_inst = dyn_cast<Instruction>(U)) {
          graph->addEdge(ValueDefNode(&I), ValueDefNode(user_inst));
        }
      }
    }
  }

  return graph;
}

/// @brief Iterates over all all leaky paths and builds matrix representation of dependency chain.
/// It also extends replaces each vertex X with vertex (X_i, X_o) where X_i is a vertex that keeps
/// all incoming edges and vertex X_o keeps all outgoing edges. There is a single edge between vertex
/// X_i and X_o in order for the Min Cut Algorithm to correctly identify the minimum cut. This leads
/// to a Matrix that is twice the size as the original.
// void populateGraph(InstVec1D &insts, dag_type **graph, int num_vertices, int og_num_vertices) {
//   // Internal to this function, we first make a matrix representation without changing each
//   // vertex X to (X_i, X_o) - this graph must be freed before the function returns.
//   dag_type **og_graph = allocateGraphDS(og_num_vertices);

//   for (Instruction *I : insts) {
//     for (User *U : I->users()) {
//       if (Instruction *II = dyn_cast<Instruction>(U)) {
//         auto row = getInstructionIndex(insts, I);
//         auto col = getInstructionIndex(insts, II);
//         if (row == -1 || col == -1) continue;

//         og_graph[row][col] = 1;
//       }
//     }
//   }

//   for (Instruction *I : insts) {
//     if (isTransientInstruction(I)) {
//       auto i = getInstructionIndex(insts, I);
//       og_graph[0][i] = 1;
//     } else if (isStableInstruction(I)) {
//       auto i = getInstructionIndex(insts, I);
//       og_graph[i][og_num_vertices - 1] = 1;
//     }
//   }

//   printGraph(og_graph, og_num_vertices); N("");
//   bool *visited = (bool*) calloc(og_num_vertices, sizeof(bool));
//   printGraph(og_graph, visited, og_num_vertices); N("");
//   free(visited);

//   for (int row = 1; row < og_num_vertices - 1; row++) {
//     int target_row = (row * 2) - 1;
//     graph[target_row][target_row + 1] = 1; // Link X_i to X_o

//     // Modify the index of all outgoing edges of the current vertex to be (index * 2) - 1.
//     for (int col = 0; col < og_num_vertices; col++) {
//       if (og_graph[row][col] == 1) {
//         graph[target_row + 1][(col * 2) - 1] = 1;
//       }
//     }
//   }

//   // Update the source node's edges (index 0) to point to correct locations.
//   for (int col = 0; col < og_num_vertices - 1; col++) {
//     if (og_graph[0][col] == 1) {
//       graph[0][(col * 2) - 1] = 1;
//     }
//   }

//   for (Instruction *I : insts) {
//     auto row = getInstructionIndex(insts, I);
//     if (row != -1) {
//       // N((row * 2) - 1 << ": " << *I);
//       N(row << ": " << *I);
//     }
//   }

//   freeGraph(og_graph, og_num_vertices);
// }

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

SmallSet<Instruction*, 16> minCut(BladeGraph &graph) {
  SmallSet<Instruction*, 16> cutset;

  std::queue<OldBladeNode*> queue;
  std::vector<OldBladeNode*> preds;

  return cutset;
}

/// @brief Performs a customized version of Ford Fulkerson's Max Flow Min Cut Algorithm
/// to find the minimal cuts of the dependency graph.
// SmallSetVector<int, 16> minCut(dag_type **graph, int source, int sink, int num_vertices) {
//   int u, v;
//   dag_type **residual_graph = allocateGraphDS(num_vertices);
//   for (u = 0; u < num_vertices; u++) {
//     for (v = 0; v < num_vertices; v++) {
//       residual_graph[u][v] = graph[u][v];
//     }
//   }

//   // Keep track of the parent when performing Breadth-First-Search to build the residual graph.
//   // However, potentially unnecessary due to the fact that resulting residual graph is equivalent
//   // to the transpose of the original graph.
//   int *parent = (int*) calloc(num_vertices, sizeof(int));
//   while (bfs(residual_graph, source, sink, parent, num_vertices)) {
//     dag_type path_flow = INT_MAX;
//     for (v = sink; v != source; v = parent[v]) {
//       u = parent[v];
//       path_flow = std::min(path_flow, residual_graph[u][v]);
//     }

//     // Update residual capacities and reverse the direction of the edges.
//     for (v = sink; v != source; v=parent[v]) {
//       u = parent[v];
//       residual_graph[u][v] -= path_flow;
//       residual_graph[v][u] += path_flow;
//     }
//   }


//   free(parent);

//   // Perform a Depth-First-Search on residual graph and keep track of which nodes are reachable.
//   bool *visited = (bool*) calloc(num_vertices, sizeof(bool));
//   // printGraph(residual_graph, visited, num_vertices); N("");
//   // printGraph(graph, num_vertices); N("");
//   dfs(residual_graph, source, visited, num_vertices);
//   // printGraph(residual_graph, visited, num_vertices); N("");

//   auto cutset_ids = SmallSetVector<int, 16>();

//   // Within the following loop, i and j will represent two vertices that form a leak. We are
//   // interested in the node that is represented by j, since it is the instruction that needs
//   // to be protected.
//   for (int i = 0; i < num_vertices; i++) {
//     for (int j = 0; j < num_vertices; j++) {
//         if (visited[i] && !visited[j] && graph[i][j]) {
//           // Since each vertex previously turned into two, the index of an instruction at vertex
//           // X_o corresponds to to index / 2.
//           cutset_ids.insert(((int)j) / 2);
//         }
//     }
//   }

//   free(visited);
//   freeGraph(residual_graph, num_vertices);

//   return cutset_ids;
// }


bool insertFences(Function &F, SmallSet<Instruction*, 16> &cutset) {
  for (Instruction *I : cutset) {
    Function* fence_fn = Intrinsic::getDeclaration(F.getParent(), Intrinsic::x86_sse2_lfence);
    CallInst* fence_call = CallInst::Create(fence_fn);
    fence_call->insertAfter(I);
  }
  return true;
}

/// @brief Inserts protections right after leaky instructions given by cutset to defend
/// against speculative leaks.
/// @param prot see enum ProtectType
bool insertProtections(Function &F, SmallSet<Instruction*, 16> &cutset, ProtectType prot) {
  switch (prot) {
  case FENCE: return insertFences(F, cutset);
  }
  return false;
}


/// @brief Performs the full Blade algorithm within the scope of a single function.
void runBlade(Function &F) {
  if (F.size() < 1) {
    return;
  }

  NewBladeGraph* graph = buildBladeGraph(F);
  D(F << "\n\n");
  D(*graph << "\n\n");
  // auto cutset = minCut(graph);

  delete graph;

  // insertProtections(F, cutset, FENCE);
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
