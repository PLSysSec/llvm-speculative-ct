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
#include "llvm/IR/InstVisitor.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/IntrinsicsX86.h"
#include "llvm/Support/Casting.h"
#include <queue>
#include <stack>
#include <iostream>

#include <chrono>

using namespace llvm;

#define DEBUG_TYPE "blade"
#define D(X) DEBUG_WITH_TYPE(DEBUG_TYPE, errs() << X)

STATISTIC(NumCuts, "Total number of cuts resulting in a protect statement.");

typedef SmallVector<Instruction*> InstVec1D;
typedef SmallVector<InstVec1D> InstVec2D;
typedef int dag_type;

class BladeNode {
public:
  /// Discriminator for LLVM-style RTTI (dyn_cast<> et al.)
  enum BladeNodeKind {
    BNK_SourceNode,
    BNK_SinkNode,
    BNK_InstructionNode,
    BNK_ValueDefNode,
    BNK_InstSinkNode
  };

public:
  virtual size_t index(ValueMap<Instruction*, size_t> &instruction_to_index) const = 0;
  virtual raw_ostream& outputNode(raw_ostream& os) const = 0;
  friend raw_ostream& operator<<(raw_ostream& os, BladeNode const &node) {
    return node.outputNode(os);
  }

private:
  const BladeNodeKind kind;

public:
  BladeNodeKind getKind() const { return kind; }
  BladeNode(BladeNodeKind kind) : kind(kind) {}

  static bool classof(const BladeNode* node);
};

class SourceNode : public BladeNode {
public:
  size_t source_index;

  SourceNode(size_t source_index)
    : BladeNode(BNK_SourceNode), source_index(source_index) {}

  size_t index(ValueMap<Instruction*, size_t> &instruction_to_index) const {
    return source_index;
  }

  SourceNode& operator=(SourceNode&& other) noexcept {
    if (this == &other) {
      return *this;
    }

    source_index = other.source_index;
    return *this;
  }

  static bool classof(const BladeNode *node) {
    return node->getKind() == BNK_SourceNode;
  }

  raw_ostream& outputNode(raw_ostream& os) const {
    return os << "source";
  }
};

class SinkNode : public BladeNode {
public:
  size_t sink_index;

  SinkNode(size_t sink_index)
    : BladeNode(BNK_SinkNode), sink_index(sink_index) {}

  size_t index(ValueMap<Instruction*, size_t> &instruction_to_index) const {
    return sink_index;
  }

  SinkNode& operator=(SinkNode&& other) noexcept {
    if (this == &other) {
      return *this;
    }

    sink_index = other.sink_index;
    return *this;
  }

  static bool classof(const BladeNode *node) {
    return node->getKind() == BNK_SinkNode;
  }

  raw_ostream& outputNode(raw_ostream& os) const {
    return os << "sink";
  }
};

class InstructionNode : public BladeNode {
public:
  Instruction* inst;

  InstructionNode(BladeNodeKind kind, Instruction* inst)
    : BladeNode(kind), inst(inst) {}

  static bool classof(const BladeNode *node) {
    return node->getKind() >= BNK_SinkNode
      && node->getKind() <= BNK_InstSinkNode;
  }
};

class ValueDefNode : public InstructionNode {
public:
  ValueDefNode(Instruction* inst)
    : InstructionNode(BNK_ValueDefNode, inst) {}

  size_t index(ValueMap<Instruction*, size_t> &instruction_to_index) const {
    return instruction_to_index[inst] * 2;
  }

  static bool classof(const BladeNode *node) {
    return node->getKind() == BNK_ValueDefNode;
  }

  raw_ostream& outputNode(raw_ostream& os) const {
    return os << '"' << "defn: " << *inst << '"';
  }
};

class InstSinkNode : public InstructionNode {
public:
  InstSinkNode(Instruction* inst)
    : InstructionNode(BNK_InstSinkNode, inst) {}

  size_t index(ValueMap<Instruction*, size_t> &instruction_to_index) const {
    return instruction_to_index[inst] * 2 + 1;
  }

  static bool classof(const BladeNode *node) {
    return node->getKind() == BNK_InstSinkNode;
  }

  raw_ostream& outputNode(raw_ostream& os) const {
    return os << '"' << "sink: " << *inst << '"';
  }
};

struct BladeEdge {
public:
  int flow;
  int capacity;

  BladeEdge()
    : flow(0), capacity(0) {}

  BladeEdge(int capacity)
    : flow(0), capacity(capacity) {}
};

class BladeGraph {
public:
  using edge_iterator = typename std::vector<BladeEdge>::iterator;

private:
  std::vector<BladeEdge> edges;
  ValueMap<Instruction*, size_t> instruction_to_index;
  std::vector<Instruction*> index_to_instruction;

  size_t num_nodes;
  SourceNode source_node = SourceNode(0);
  SinkNode sink_node = SinkNode(0);

public:
  BladeGraph(Function &F) {
    size_t num_insts = 0;
    for (BasicBlock &BB : F) {
      for (Instruction &I : BB) {
        num_insts++;
      }
    }
    num_nodes = num_insts * 2 + 2;
    edges.resize(num_nodes * num_nodes, BladeEdge());
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

  Instruction* nodeIndexToInstruction(size_t index) {
    return index_to_instruction[index / 2];
  }

  // TODO: this leaks memory
  BladeNode* nodeIndexToBladeNode(size_t index) {
    if (index == nodeIndex(source_node)) {
      return &source_node;
    } else if (index == nodeIndex(sink_node)) {
      return &sink_node;
    }
    Instruction* inst = nodeIndexToInstruction(index);
    if (index % 2 == 0) {
      auto result_node = new ValueDefNode(inst);
      return result_node;
    } else {
      auto result_node = new InstSinkNode(inst);
      return result_node;
    }
  }

  edge_iterator edgesBegin(const BladeNode &node) {
    return edges.begin() + (nodeIndex(node) * num_nodes);
  }

  edge_iterator edgesEnd(const BladeNode &node) {
    return edges.begin() + (nodeIndex(node) * num_nodes) + num_nodes;
  }

  edge_iterator edgesBegin(size_t node_index) {
    return edges.begin() + (node_index * num_nodes);
  }

  edge_iterator edgesEnd(size_t node_index) {
    return edges.begin() + (node_index * num_nodes) + num_nodes;
  }

  BladeEdge &getEdge(const BladeNode &from, const BladeNode &to) {
    return edgesBegin(from)[nodeIndex(to)];
  }

  BladeEdge &getEdge(size_t from_index, size_t to_index) {
    return edgesBegin(from_index)[to_index];
  }

  bool hasEdge(const BladeNode &from, const BladeNode &to) {
    return getEdge(from, to).capacity;
  }

  bool hasEdge(size_t from_index, size_t to_index) {
    return getEdge(from_index, to_index).capacity;
  }

  void addEdge(const BladeNode &from, const BladeNode &to) {
    getEdge(from, to) = BladeEdge(1);
  }

  void markAsSource(Instruction* inst) {
    addEdge(source_node, ValueDefNode(inst));
  }

  void markAsSink(Instruction* inst) {
    addEdge(InstSinkNode(inst), sink_node);
  }

  void debugParents(std::vector<size_t> &parents) {
    size_t node_index = nodeIndex(sink_node);
    while (node_index != nodeIndex(source_node)) {
      debugNodeIndex(node_index);
      size_t parent_index = parents[node_index];
      node_index = parent_index;
      D("\n");
    }
    debugNodeIndex(node_index);
    D("\n\n");
  }

  void pushRelabelPush(size_t source_index, size_t target_index, std::vector<int> &excess_flow) {
    BladeEdge &edge = getEdge(source_index, target_index);
    int flow = std::min(excess_flow[source_index], edge.capacity - edge.flow);
    edge.flow += flow;
    getEdge(target_index, source_index).flow -= flow;
    excess_flow[source_index] -= flow;
    excess_flow[target_index] += flow;
  }

  void pushRelabelRelabel(size_t node_index, std::vector<int> &heights) {
    int min_height = INT_MAX;
    for (int other_index = 0; other_index < num_nodes; other_index++) {
      BladeEdge &edge = getEdge(node_index, other_index);
      if (edge.capacity - edge.flow > 0) {
        min_height = std::min(min_height, heights[other_index]);
        heights[node_index] = min_height + 1;
      }
    }
  }

  void pushRelabelDischarge(size_t node_index, std::vector<int> &heights, std::vector<int> &excess_flow, std::vector<int> &seen) {
    while (excess_flow[node_index] > 0) {
      if (seen[node_index] < num_nodes) {
        size_t other_index = seen[node_index];
        BladeEdge &edge = getEdge(node_index, other_index);
        if ((edge.capacity - edge.flow > 0) && (heights[node_index] > heights[other_index])) {
          pushRelabelPush(node_index, other_index, excess_flow);
          debugPushRelabel(heights, excess_flow);
        } else {
          seen[node_index] += 1;
        }
      } else {
        pushRelabelRelabel(node_index, heights);
        debugPushRelabel(heights, excess_flow);
        seen[node_index] = 0;
      }
    }
  }

  // void pushRelabelPreflow(std::vector<int> &heights, std::vector<int> &excess_flow) {
  //   heights.resize(num_nodes, 0);
  //   heights[nodeIndex(source_node)] = num_nodes;

  //   excess_flow.resize(num_nodes, 0);

  //   for (size_t node_index = 0; node_index < num_nodes; node_index++) {
  //     BladeEdge &edge = getEdge(nodeIndex(source_node), node_index);

  //     if (edge.flow == edge.capacity) { // this also captures skipping if an edge doesn't exist
  //       continue;
  //     }

  //     int flow = std::min(edge.capacity - edge.flow, excess_flow[nodeIndex(source_node)]);

  //     edge.flow += flow;
  //     getEdge(node_index, nodeIndex(source_node)).flow -= flow;
  //     excess_flow[nodeIndex(source_node)] -= flow;
  //     excess_flow[node_index] += flow;
  //   }
  // }

  // size_t findOverflowNode(std::vector<int> &excess_flow) {
  //   for (size_t ii = 0; ii < num_nodes; ii++) {
  //     if (excess_flow[ii] > 0) {
  //       return ii;
  //     }
  //   }

  //   return -1;
  // }

  // bool pushRelabelPush(size_t node_index, std::vector<int> &heights, std::vector<int> &excess_flow) {
  //   for (size_t adjacent_index = 0; adjacent_index < num_nodes; adjacent_index++) {
  //     BladeEdge &edge = getEdge(node_index, adjacent_index);
  //     if (edge.flow == edge.capacity) { // this also captures skipping if an edge doesn't exist
  //       continue;
  //     }

  //     if (heights[node_index] > heights[adjacent_index]) {
  //       int flow = std::min(edge.capacity - edge.flow, excess_flow[node_index]);

  //       edge.flow += flow;
  //       getEdge(adjacent_index, node_index).flow -= flow;
  //       excess_flow[node_index] -= flow;
  //       excess_flow[adjacent_index] += flow;

  //       return true;
  //     }
  //   }
  //   return false;
  // }

  // void pushRelabelRelabel(size_t node_index, std::vector<int> &heights) {
  //   int min_height = INT_MAX;

  //   for (size_t other_index = 0; other_index < num_nodes; other_index++) {
  //     auto edge = getEdge(node_index, other_index);
  //     if (edge.flow == edge.capacity) { // this also captures skipping if an edge doesn't exist
  //       continue;
  //     }

  //     if (heights[other_index] < min_height) {
  //       min_height = heights[other_index];
  //       heights[node_index] = min_height + 1;
  //     }
  //   }
  // }

  SmallVector<std::pair<BladeNode*, BladeNode*>> minCut() {
    SmallVector<std::pair<BladeNode*, BladeNode*>> cutset;

    auto original_edges = edges;

    std::vector<int> heights;
    heights.resize(num_nodes, 0);
    std::vector<int> excess_flow;
    excess_flow.resize(num_nodes, 0);

    size_t source_index = nodeIndex(source_node);

    std::list<size_t> todo_list;
    for (size_t node_index; node_index < num_nodes; node_index++) {
      if (node_index != source_index && node_index != nodeIndex(sink_node)) {
        todo_list.push_back(node_index);
      }
    }

    debugPushRelabel(heights, excess_flow);

    heights[source_index] = num_nodes;
    for (size_t other_index; other_index < num_nodes; other_index++) {
      BladeEdge &edge = getEdge(source_index, other_index);
      int flow = edge.capacity - edge.flow;
      edge.flow += flow;
      getEdge(other_index, source_index).flow -= flow;
      excess_flow[other_index] += flow;
    }

    debugPushRelabel(heights, excess_flow);

    std::vector<int> seen;
    seen.resize(num_nodes - 2, 0);

    auto place = todo_list.begin();
    while (place != todo_list.end()) {
      size_t node_index = *place;
      int old_height = heights[node_index];
      pushRelabelDischarge(node_index, heights, excess_flow, seen);
      if (heights[node_index] > old_height) {
        todo_list.erase(place);
        todo_list.push_front(node_index);
        place = todo_list.begin();
      } else {
        place++;
      }
    }


    // pushRelabelPreflow(heights, excess_flow);
    // debugPushRelabel(0, heights, excess_flow);

    // int iterations = 0;
    // auto overflow_node_index = findOverflowNode(excess_flow);
    // while (overflow_node_index != -1) {
    //   iterations++;
    //   // errs() << "overflow_node_index = " << overflow_node_index << "\n";
    //   if (!pushRelabelPush(overflow_node_index, heights, excess_flow)) {
    //     // errs() << "relabeling\n";
    //     pushRelabelRelabel(overflow_node_index, heights);
    //   } else {
    //     // errs() << "pushing\n";
    //   }
    //   debugPushRelabel(iterations, heights, excess_flow);
    //   overflow_node_index = findOverflowNode(excess_flow);
    // }

    std::vector<bool> visited;
    visited.resize(num_nodes, false);

    flowDfs(nodeIndex(source_node), visited);

    edges = original_edges;

    for (size_t node_index = 0; node_index < num_nodes; node_index++) {
      for (int other_index = 0; other_index < num_nodes; other_index++) {
        if (visited[node_index] && !visited[other_index] && hasEdge(node_index, other_index)) {
          cutset.push_back({nodeIndexToBladeNode(node_index), nodeIndexToBladeNode(other_index)});
        }
      }
    }

    return cutset;
  }

  SmallVector<std::pair<BladeNode*, BladeNode*>> minCutEdmondsKarp() {
    SmallVector<std::pair<BladeNode*, BladeNode*>> cutset;

    auto original_edges = edges;

    std::vector<size_t> parents;
    parents.resize(num_nodes);

    // auto t1 = std::chrono::high_resolution_clock::now();
    // int iterations = 0;
    while (flowBfs(parents)) {
      // iterations++;
      int path_flow = 1;
      size_t node_index = nodeIndex(sink_node);
      while (node_index != nodeIndex(source_node)) {
        size_t parent_index = parents[node_index];
        path_flow = std::min(path_flow, getEdge(parent_index, node_index).flow);
        node_index = parent_index;
      }

      node_index = nodeIndex(sink_node);
      while (node_index != nodeIndex(source_node)) {
        size_t parent_index = parents[node_index];
        getEdge(parent_index, node_index).flow = getEdge(parent_index, node_index).flow - path_flow;
        getEdge(node_index, parent_index).flow = getEdge(node_index, parent_index).flow + path_flow;
        node_index = parent_index;
      }
    }
    // auto t2 = std::chrono::high_resolution_clock::now();
    // auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(t2-t1).count();
    // if (duration > 1000) {
    //   errs() << iterations << " building residual: " << duration << "\n";
    // }

    std::vector<bool> visited;
    visited.resize(num_nodes, false);

    // t1 = std::chrono::high_resolution_clock::now();
    flowDfs(nodeIndex(source_node), visited);
    // t2 = std::chrono::high_resolution_clock::now();
    // duration = std::chrono::duration_cast<std::chrono::milliseconds>(t2-t1).count();
    // if (duration > 1000) {
    //   errs() << " flow dfs: " << duration << "\n";
    // }

    edges = original_edges;

    // t1 = std::chrono::high_resolution_clock::now();
    for (size_t node_index = 0; node_index < num_nodes; node_index++) {
      for (int other_index = 0; other_index < num_nodes; other_index++) {
        if (visited[node_index] && !visited[other_index] && hasEdge(node_index, other_index)) {
          cutset.push_back({nodeIndexToBladeNode(node_index), nodeIndexToBladeNode(other_index)});
        }
      }
    }
    // t2 = std::chrono::high_resolution_clock::now();
    // duration = std::chrono::duration_cast<std::chrono::milliseconds>(t2-t1).count();
    // if (duration > 1000) {
    //   errs() << " building cutset: " << duration << "\n";
    // }

    return cutset;
  }

  bool flowBfs(std::vector<size_t> &parents) {
    std::vector<bool> visited;
    visited.resize(num_nodes, false);
    std::queue<size_t> traversed;
    size_t source_index = nodeIndex(source_node);

    traversed.push(source_index);
    visited[source_index] = true;

    while (!traversed.empty()) {
      size_t current_index = traversed.front();
      traversed.pop();

      for (int neighbor_index = 0; neighbor_index < num_nodes; neighbor_index++) {
        if (!visited[neighbor_index] && hasEdge(current_index, neighbor_index)) {
          traversed.push(neighbor_index);
          parents[neighbor_index] = current_index;
          visited[neighbor_index] = true;
        }
      }
    }

    return visited[nodeIndex(sink_node)];
  }

  void flowDfs(size_t start_index, std::vector<bool> &visited) {
    visited[start_index] = true;
    for (size_t node_index = 0; node_index < num_nodes; node_index++) {
      if (!visited[node_index] && hasEdge(start_index, node_index)) {
        flowDfs(node_index, visited);
      }
    }
  }

  // TODO: protect type
  void debugNodeIndex(size_t node_index) {
    if (node_index == nodeIndex(source_node)) {
      D("source");
    } else if (node_index == nodeIndex(sink_node)) {
      D("sink");
    } else {
      D(*nodeIndexToInstruction(node_index));
    }
  }

  void debugPushRelabelIndex(size_t node_index) {
    if (node_index == nodeIndex(source_node)) {
      errs() << "source";
    } else if (node_index == nodeIndex(sink_node)) {
      errs() << "sink";
    } else {
      errs() << node_index;
    }
  }

  void debugPushRelabel(std::vector<int> &heights, std::vector<int> &excess_flow) {
    // errs() << "digraph " << " {" << "\n";

    for (size_t source_index = 0; source_index < num_nodes; source_index++) {
      errs() << source_index << "["
             << "label = " << '"';
      debugPushRelabelIndex(source_index);
      errs() << ": excess = " << excess_flow[source_index] << ", " << "height = " << heights[source_index] << '"'
             << "];\n";
      for (size_t target_index = 0; target_index < num_nodes; target_index++) {
        auto edge = getEdge(source_index, target_index);
        if (edge.capacity || edge.flow) {
          errs() << source_index << " -> " << target_index
                 << "["
                 << "label = " << '"' << edge.flow << "/" << edge.capacity << '"'
                 << "]"
                 << ";\n";
        }
      }
    }

    errs() << "\n\n";
    // errs() << "}\n\n";
  }

  raw_ostream& outputGraph(raw_ostream& os) {
    // os << "    ";
    // for (size_t ii = 0; ii < num_nodes; ii++) {
    //   if (ii < 10) {
    //     os << "0";
    //   }
    //   os << ii << " ";
    // }
    // os << "\n";
    // for (size_t ii = 0; ii < num_nodes; ii++) {
    //   if (ii < 10) {
    //     os << "0";
    //   }
    //   os << ii << ": ";
    //   for (size_t jj = 0; jj < num_nodes; jj++) {
    //     os << " " << edges[ii * num_nodes + jj] << " ";
    //   }
    //   if (ii == nodeIndex(source_node)) {
    //     os << "source";
    //   } else if (ii == nodeIndex(sink_node)) {
    //     os << "sink";
    //   } else {
    //     os << *nodeIndexToInstruction(ii);
    //   }
    //   os << "\n";
    // }
    // os << "\n";

    os << "digraph {" << '\n';

    os << "node[shape=rectangle];\n";

    for (Instruction* from_inst : index_to_instruction) {
      for (Instruction* to_inst : index_to_instruction) {
        ValueDefNode fromDef = ValueDefNode(from_inst);
        InstSinkNode fromSink = InstSinkNode(from_inst);
        ValueDefNode toDef = ValueDefNode(to_inst);
        InstSinkNode toSink = InstSinkNode(to_inst);
        for (auto from : std::initializer_list<BladeNode*>{&fromDef, &fromSink}) {
          for (auto to : std::initializer_list<BladeNode*>{&toDef, &toSink}) {
            if (hasEdge(*from, *to)) {
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
        if (hasEdge(source_node, *node)) {
          os << source_node << " -> " << *node << ';' << '\n';
        }
        if (hasEdge(sink_node, *node)) {
          os << sink_node << " -> " << *node << ';' << '\n';
        }
        if (hasEdge(*node, source_node)) {
          os << *node << " -> " << source_node << ';' << '\n';
        }
        if (hasEdge(*node, sink_node)) {
          os << *node << " -> " << sink_node << ';' << '\n';
        }
      }
    }
    if (hasEdge(source_node, sink_node)) {
      os << source_node << " -> " << sink_node << ';' << '\n';
    }
    if (hasEdge(sink_node, source_node)) {
      os << sink_node << " -> " << source_node << ';' << '\n';
    }

    os << "node[shape=none, width=0, height=0, label=\"\"];\n";

    int ii = 0;
    os << "{" << "rank=same; " << ii << " -> " << source_node << "[style=invis]" << "}\n";
    ii++;
    for (Instruction* inst : index_to_instruction) {
      ValueDefNode defNode = ValueDefNode(inst);
      InstSinkNode sinkNode = InstSinkNode(inst);
      os << "{" << "rank=same; " << ii << " -> " << defNode << " -> " << sinkNode << "[style=invis]" << "}\n";
      ii++;
    }
    os << "{" << "rank=same; " << ii << " -> " << sink_node << "[style=invis];" << "}\n";
    ii++;
    for (ii = 0; ii < index_to_instruction.size() + 1; ii++) {
      os << ii << " -> " << ii + 1 << "[style=invis];";
    }

    os << '}';

    return os;
  }

  friend raw_ostream& operator<<(raw_ostream& os, BladeGraph &graph) {
    return graph.outputGraph(os);
  }
};

/// @brief Blade uses either lfences or SLH underneath the protect statement.
enum ProtectType {
  FENCE,
  // SLH
};

struct BladeGraphInsertVisitor : public InstVisitor<BladeGraphInsertVisitor> {
  BladeGraph &graph;

  BladeGraphInsertVisitor(BladeGraph &graph)
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

  void visitSelectInst(SelectInst &I) {
    graph.markAsSink(&I);

    if (auto *condition_inst = dyn_cast<Instruction>(I.getCondition())) {
      graph.addEdge(ValueDefNode(condition_inst), InstSinkNode(&I));
    }
  }

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

  // TODO(matt): does it make sense to skip past fences?
  void visitFenceInst(FenceInst &I) {
  }

  void visitInstruction(Instruction &I) {
    if (I.mayReadOrWriteMemory()) {
      errs() << "unknown instruction that touches memory: " << I << "\n";
      exit(1);
    }
  }
};


BladeGraph* buildBladeGraph(Function &F) {
  BladeGraph* graph = new BladeGraph(F);

  // auto t1 = std::chrono::high_resolution_clock::now();
  BladeGraphInsertVisitor insertVisitor = BladeGraphInsertVisitor(*graph);
  insertVisitor.visit(F);
  // auto t2 = std::chrono::high_resolution_clock::now();
  // auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(t2-t1).count();
  // if (duration > 1000) {
  //   errs() << F.getName() << "building graph: " << duration << "\n";
  // }


  // t1 = std::chrono::high_resolution_clock::now();
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
  // t2 = std::chrono::high_resolution_clock::now();
  // duration = std::chrono::duration_cast<std::chrono::milliseconds>(t2-t1).count();
  // if (duration > 1000) {
  //   errs() << F.getName() << "adding edges: " << duration << "\n";
  // }

  return graph;
}
CallInst* getFenceCall(Function &F) {
  Function* fence_fn = Intrinsic::getDeclaration(F.getParent(), Intrinsic::x86_sse2_lfence);
  return CallInst::Create(fence_fn);
}

void insertFenceAfter(Function &F, Instruction* inst) {
  CallInst* fence_call = getFenceCall(F);
  fence_call->insertAfter(inst);
}

void insertFenceBefore(Function &F, Instruction* inst) {
  CallInst* fence_call = getFenceCall(F);
  fence_call->insertBefore(inst);
}


bool insertFences(Function &F, SmallVector<std::pair<BladeNode*, BladeNode*>> &cutset) {
  for (auto &edge : cutset) {
    auto &src = edge.first;
    auto &end = edge.second;

    if (isa<SourceNode>(src)) {
      Instruction* inst = cast<ValueDefNode>(end)->inst;
      insertFenceAfter(F, inst);
    } else if (isa<SinkNode>(end)) {
      Instruction* inst = cast<InstSinkNode>(src)->inst;
      insertFenceBefore(F, inst);
    } else {
      Instruction* inst = cast<InstructionNode>(end)->inst;
      // find the end of a sequence of phi nodes. I believe this is valid
      if (isa<PHINode>(inst)) {
        while (isa<PHINode>(inst)) {
          inst = inst->getNextNonDebugInstruction();
          if (inst == nullptr) {
            errs() << "could not find end of phi node sequence";
            exit(1);
          }
        }
      }
      insertFenceBefore(F, inst);
    }
  }
  return true;
}

/// @brief Inserts protections right after leaky instructions given by cutset to defend
/// against speculative leaks.
/// @param prot see enum ProtectType
bool insertProtections(Function &F, SmallVector<std::pair<BladeNode*, BladeNode*>> &cutset, ProtectType prot) {
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

  BladeGraph* graph = buildBladeGraph(F);
  // D(F << "\n\n");
  // D(*graph << "\n\n");
  auto t1 = std::chrono::high_resolution_clock::now();
  auto cutset = graph->minCut();
  auto t2 = std::chrono::high_resolution_clock::now();
  auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(t2-t1).count();
  if (duration > 1000) {
    errs() << F.getName() << " min cut: " << duration << "\n";
  }

  D("cutset" << "\n");
  for (auto cut : cutset) {
    D(cut.first << " -> " << cut.second << "\n");
  }

  // t1 = std::chrono::high_resolution_clock::now();
  insertProtections(F, cutset, FENCE);
  // t2 = std::chrono::high_resolution_clock::now();
  // duration = std::chrono::duration_cast<std::chrono::milliseconds>(t2-t1).count();
  // if (duration > 1000) {
  //   errs() << F.getName() << "protections: " << duration << "\n";
  // }

  delete graph;
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
