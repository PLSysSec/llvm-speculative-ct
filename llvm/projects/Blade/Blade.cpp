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
#include "llvm/ADT/DenseSet.h"
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


class Graph {
public:
  using Edge = int;
  using edge_iterator = typename std::vector<Edge>::iterator;

protected:
  std::vector<Edge> edges;

public:
  size_t num_nodes;

  Graph() {}

  Graph(const Graph &graph) {
    num_nodes = graph.num_nodes;
    std::copy(graph.edges.begin(), graph.edges.end(), std::back_inserter(edges));
  }

  Graph(size_t num_nodes, Edge init_edge)
    : num_nodes(num_nodes)
  {
    edges.resize(num_nodes * num_nodes, init_edge);
  }

  edge_iterator edgesBegin(size_t node_index) {
    return edges.begin() + (node_index * num_nodes);
  }

  edge_iterator edgesEnd(size_t node_index) {
    return edges.begin() + (node_index * num_nodes) + num_nodes;
  }

  Edge &getEdge(size_t from_index, size_t to_index) {
    return edgesBegin(from_index)[to_index];
  }

  bool hasEdge(size_t from_index, size_t to_index) {
    return getEdge(from_index, to_index) > 0;
  }

  DenseSet<size_t> reachable(size_t from) {
    DenseSet<size_t> reachable_set;
    reachableDFS(from, reachable_set);
    return reachable_set;
  }

  void reachableDFS(size_t from, DenseSet<size_t> &reachable_set) {
    reachable_set.insert(from);
    for (size_t node = 0; node < num_nodes; node++) {
      if (!reachable_set.contains(node) && hasEdge(from, node)) {
        reachableDFS(node, reachable_set);
      }
    }
  }

  friend raw_ostream& operator<<(raw_ostream& os, Graph &graph) {
    return graph.outputGraph(os);
  }

  raw_ostream &outputGraph(raw_ostream& os) {
    os << "digraph " << " {" << "\n";

    for (size_t source = 0; source < num_nodes; source++) {
      for (size_t target = 0; target < num_nodes; target++) {
        if (hasEdge(source, target)) {
          os << source << " -> " << target << ";" << "\n";
        }
      }
    }

    os << "}";
    return os;
  }
};

class MinCut {
public:
  virtual SmallVector<std::pair<size_t, size_t>> minCut() = 0;
};

class MinCutEdmondsKarp : public MinCut {
private:
  Graph &g;
  size_t source;
  size_t sink;

  Graph residual;

public:
  MinCutEdmondsKarp(Graph &g, size_t source, size_t sink)
    : g(g), source(source), sink(sink) {}

  SmallVector<std::pair<size_t, size_t>> minCut() {
    residual = Graph(g);

    std::vector<size_t> parents;
    parents.resize(g.num_nodes);

    while (flowBfs(parents)) {
      int path_flow = 1; // TODO(matt): did I special case this?
      size_t node = sink;
      while (node != source) {
        size_t parent = parents[node];
        path_flow = std::min(path_flow, residual.getEdge(parent, node));
        node = parent;
      }

      node = sink;
      while (node != source) {
        size_t parent = parents[node];
        residual.getEdge(parent, node) -= path_flow;
        residual.getEdge(node, parent) += path_flow;
        node = parent;
      }
    }

    // errs() << residual << "\n\n";

    auto reachable = residual.reachable(source);
    SmallVector<std::pair<size_t, size_t>> cutset;
    for (size_t node = 0; node < residual.num_nodes; node++) {
      for (int other = 0; other < residual.num_nodes; other++) {
        if (reachable.contains(node) && !reachable.contains(other) && g.hasEdge(node, other)) {
          cutset.push_back({node, other});
        }
      }
    }

    return cutset;
  }

  bool flowBfs(std::vector<size_t> &parents) {
    std::vector<bool> visited;
    visited.resize(residual.num_nodes, false);
    std::queue<size_t> traversed;

    traversed.push(source);
    visited[source] = true;

    while (!traversed.empty()) {
      size_t current = traversed.front();
      traversed.pop();

      for (int neighbor = 0; neighbor < residual.num_nodes; neighbor++) {
        if (!visited[neighbor] && residual.hasEdge(current, neighbor)) {
          traversed.push(neighbor);
          parents[neighbor] = current;
          visited[neighbor] = true;
        }
      }
    }

    return visited[sink];
  }
};

class MinCutPushRelabel : public MinCut {
private:
  Graph &g;
  size_t source;
  size_t sink;

  Graph residual;
  std::vector<int> heights;
  std::vector<int> excess_flow;
  std::vector<int> seen;

  std::vector<size_t> relevant_nodes;

public:
  MinCutPushRelabel(Graph &g, size_t source, size_t sink)
    : g(g), source(source), sink(sink) {}

  void preflow() {
    heights.resize(g.num_nodes, 0);
    excess_flow.resize(g.num_nodes, 0);
    residual = Graph(g);

    // errs() << *this << "\n\n";

    for (size_t from = 0; from < g.num_nodes; from++) {
      for (size_t to = 0; to < g.num_nodes; to++) {
        if (g.hasEdge(from, to) || g.hasEdge(to, from)) {
          relevant_nodes.push_back(from);
          break;
        }
      }
    }

    heights[source] = relevant_nodes.size();

    for (auto other : relevant_nodes) {
      int flow = g.getEdge(source, other);
      residual.getEdge(other, source) = flow;
      residual.getEdge(source, other) = 0;
      excess_flow[other] += flow;
    }
  }

  void discharge(size_t node) {
    // while (excess_flow[node] > 0) {
    //   if (seen[node] < residual.num_nodes) {
    //     size_t other = seen[node];
    //     Graph::Edge &edge = residual.getEdge(node, other);
    //     if ((edge > 0) && (heights[node] > heights[other])) {
    //       push(node, other);
    //     } else {
    //       seen[node] += 1;
    //     }
    //   } else {
    //     relabel(node);
    //     seen[node] = 0;
    //   }
    // }
  }

  void push(size_t from, size_t to) {
    Graph::Edge &edge = residual.getEdge(from, to);
    int flow = std::min(excess_flow[from], edge);
    edge -= flow;
    residual.getEdge(to, from) += flow;
    excess_flow[from] -= flow;
    excess_flow[to] += flow;
    // errs() << *this << "\n\n";
  }

  void relabel(size_t node) {
    int min_height = INT_MAX;
    for (auto other : relevant_nodes) {
      Graph::Edge &edge = residual.getEdge(node, other);
      if (edge > 0) {
        min_height = std::min(min_height, heights[other]);
        heights[node] = min_height + 1;
      }
    }
    // errs() << *this << "\n\n";
  }

  bool test_discharge() {
    std::vector<size_t> todo_list;
    for (auto node : relevant_nodes) {
      if (node != source && node != sink) {
        todo_list.push_back(node);
      }
    }
    for (auto node : todo_list) {
      if (excess_flow[node] > 0) {
        for (auto other : relevant_nodes) {
          if ((heights[node] == heights[other] + 1) && residual.hasEdge(node, other)) {
            // errs() << "labelloc=" << '"' << "t" << '"' << ";" << "\n";
            // errs() << "label=" << '"' << "pushing " << node << " -> " << other << '"' << ";" << "\n";
            push(node, other);
            return true;
          }
        }
      }
    }
    for (auto node : todo_list) {
      if (excess_flow[node] > 0) {
        for (auto other : relevant_nodes) {
          if (residual.hasEdge(node, other)) {
            // errs() << "labelloc=" << '"' << "t" << '"' << ";" << "\n";
            // errs() << "label=" << '"' << "relabeling " << node << '"' << ";" << "\n";
            relabel(node);
            return true;
          }
        }
      }
    }
    return false;
  }

  SmallVector<std::pair<size_t, size_t>> minCut() {
    preflow();
    // errs() << *this << "\n\n";

    // std::list<size_t> todo_list;
    // for (size_t node = 0; node < residual.num_nodes; node++) {
    //   if (node != source && node != sink) {
    //     todo_list.push_back(node);
    //   }
    // }
    // seen.resize(residual.num_nodes - 2, 0);

    while (true) {
      if (!test_discharge()) {
        break;
      }
    }

    // auto place = todo_list.begin();
    // while (place != todo_list.end()) {
    //   size_t node = *place;
    //   int old_height = heights[node];
    //   discharge(node);
    //   if (heights[node] > old_height) {
    //     todo_list.erase(place);
    //     todo_list.push_front(node);
    //     place = todo_list.begin();
    //   } else {
    //     place++;
    //   }
    // }

    errs() << residual << "\n\n";

    auto reachable = residual.reachable(source);
    SmallVector<std::pair<size_t, size_t>> cutset;
    for (auto node : relevant_nodes) {
      for (auto other : relevant_nodes) {
        if (reachable.contains(node) && !reachable.contains(other) && g.hasEdge(node, other)) {
          cutset.push_back({node, other});
        }
      }
    }

    return cutset;
  }

  void debugNode(raw_ostream &os, size_t node) {
    if (node == source) {
      os << "source";
    } else if (node == sink) {
      os << "sink";
    } else {
      os << node;
    }
  }

  friend raw_ostream& operator<<(raw_ostream& os, MinCutPushRelabel &cutter) {
    // os << "digraph " << " {" << "\n";

    for (size_t from = 0; from < cutter.residual.num_nodes; from++) {
      bool has_edge = false;
      for (size_t other = 0; other < cutter.residual.num_nodes; other++) {
        if (cutter.g.hasEdge(from, other) || cutter.g.hasEdge(other, from)) {
          has_edge = true;
          break;
        }
      }
      if (has_edge) {
        os << from << "["
          << "label = " << '"';
        cutter.debugNode(os, from);
        os << ": excess = " << cutter.excess_flow[from] << ", " << "height = " << cutter.heights[from] << '"'
          << "];\n";
      }
      for (size_t to = 0; to < cutter.residual.num_nodes; to++) {
        auto edge = cutter.residual.getEdge(from, to);
        if (edge != 0) {
          os << from << " -> " << to << ";" << "\n";
        }
      }
    }

    os << "\n\n";
    // os << "}\n\n";

    return os;
  }
};

class BladeGraph : public Graph {
private:
  ValueMap<Instruction*, size_t> instruction_to_index;
  std::vector<Instruction*> index_to_instruction;

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
    edges.resize(num_nodes * num_nodes, 0);
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
    return Graph::edgesBegin(nodeIndex(node));
  }

  edge_iterator edgesEnd(const BladeNode &node) {
    return Graph::edgesEnd(nodeIndex(node));
  }

  Edge &getEdge(const BladeNode &from, const BladeNode &to) {
    return Graph::getEdge(nodeIndex(from), nodeIndex(to));
  }

  bool hasEdge(const BladeNode &from, const BladeNode &to) {
    return Graph::hasEdge(nodeIndex(from), nodeIndex(to));
  }

  void addEdge(const BladeNode &from, const BladeNode &to) {
    getEdge(from, to) = 1;
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

  void markAsSource(Instruction* inst) {
    addEdge(source_node, ValueDefNode(inst));
  }

  void markAsSink(Instruction* inst) {
    addEdge(InstSinkNode(inst), sink_node);
  }

  SmallVector<std::pair<BladeNode*, BladeNode*>> minCut() {
    MinCutPushRelabel cutter = MinCutPushRelabel(*this, nodeIndex(source_node), nodeIndex(sink_node));
    // MinCutEdmondsKarp cutter = MinCutEdmondsKarp(*this, nodeIndex(source_node), nodeIndex(sink_node));
    auto cutset_indices = cutter.minCut();

    SmallVector<std::pair<BladeNode*, BladeNode*>> cutset;
    for (auto indices : cutset_indices) {
      cutset.push_back({nodeIndexToBladeNode(indices.first), nodeIndexToBladeNode(indices.second)});
    }

    errs() << "cutset:" << "\n";
    for (auto cut : cutset) {
      errs() << *(cut.first) << " -> " << *(cut.second) << "\n";
    }
    errs() << "\n";

    return cutset;
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
