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

class BladeGraph {
public:
  using edge_iterator = typename std::vector<bool>::iterator;
  using edge_ref = typename std::vector<bool>::iterator::reference;

private:
  std::vector<bool> edges;
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
    edges.resize(num_nodes * num_nodes, false);
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

  edge_ref getEdge(const BladeNode &from, const BladeNode &to) {
    return edgesBegin(from)[nodeIndex(to)];
  }

  edge_ref getEdge(size_t from_index, size_t to_index) {
    return edgesBegin(from_index)[to_index];
  }

  bool hasEdge(const BladeNode &from, const BladeNode &to) {
    return getEdge(from, to);
  }

  bool hasEdge(size_t from_index, size_t to_index) {
    return getEdge(from_index, to_index);
  }

  void addEdge(const BladeNode &from, const BladeNode &to) {
    getEdge(from, to) = 1;
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

  SmallVector<std::pair<BladeNode*, BladeNode*>> minCut() {
    SmallVector<std::pair<BladeNode*, BladeNode*>> cutset;

    std::vector<bool> original_edges = edges;

    std::vector<size_t> parents;
    parents.resize(num_nodes);

    while (flowBfs(parents)) {
      bool path_flow = 1;
      size_t node_index = nodeIndex(sink_node);
      while (node_index != nodeIndex(source_node)) {
        size_t parent_index = parents[node_index];
        path_flow = std::min(path_flow, hasEdge(parent_index, node_index)); // NOTE: not strictly necessary since weights are boolean but easy future proofing
        node_index = parent_index;
      }

      node_index = nodeIndex(sink_node);
      while (node_index != nodeIndex(source_node)) {
        size_t parent_index = parents[node_index];
        getEdge(parent_index, node_index) = getEdge(parent_index, node_index) - path_flow;
        getEdge(node_index, parent_index) = getEdge(node_index, parent_index) + path_flow;
        node_index = parent_index;
      }
    }

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

    // os << "digraph {" << '\n';

    // os << "node[shape=rectangle];\n";

    // for (Instruction* from_inst : index_to_instruction) {
    //   for (Instruction* to_inst : index_to_instruction) {
    //     ValueDefNode fromDef = ValueDefNode(from_inst);
    //     InstSinkNode fromSink = InstSinkNode(from_inst);
    //     ValueDefNode toDef = ValueDefNode(to_inst);
    //     InstSinkNode toSink = InstSinkNode(to_inst);
    //     for (auto from : std::initializer_list<BladeNode*>{&fromDef, &fromSink}) {
    //       for (auto to : std::initializer_list<BladeNode*>{&toDef, &toSink}) {
    //         if (hasEdge(*from, *to)) {
    //           os << *from << " -> " << *to << ';' << '\n';
    //         }
    //       }
    //     }
    //   }
    // }
    // for (Instruction* node_inst : index_to_instruction) {
    //   ValueDefNode nodeDef = ValueDefNode(node_inst);
    //   InstSinkNode nodeSink = InstSinkNode(node_inst);
    //   for (auto node : std::initializer_list<BladeNode*>{&nodeDef, &nodeSink}) {
    //     if (hasEdge(source_node, *node)) {
    //       os << source_node << " -> " << *node << ';' << '\n';
    //     }
    //     if (hasEdge(sink_node, *node)) {
    //       os << sink_node << " -> " << *node << ';' << '\n';
    //     }
    //     if (hasEdge(*node, source_node)) {
    //       os << *node << " -> " << source_node << ';' << '\n';
    //     }
    //     if (hasEdge(*node, sink_node)) {
    //       os << *node << " -> " << sink_node << ';' << '\n';
    //     }
    //   }
    // }
    // if (hasEdge(source_node, sink_node)) {
    //   os << source_node << " -> " << sink_node << ';' << '\n';
    // }
    // if (hasEdge(sink_node, source_node)) {
    //   os << sink_node << " -> " << source_node << ';' << '\n';
    // }

    // os << "node[shape=none, width=0, height=0, label=\"\"];\n";

    // int ii = 0;
    // os << "{" << "rank=same; " << ii << " -> " << source_node << "[style=invis]" << "}\n";
    // ii++;
    // for (Instruction* inst : index_to_instruction) {
    //   ValueDefNode defNode = ValueDefNode(inst);
    //   InstSinkNode sinkNode = InstSinkNode(inst);
    //   os << "{" << "rank=same; " << ii << " -> " << defNode << " -> " << sinkNode << "[style=invis]" << "}\n";
    //   ii++;
    // }
    // os << "{" << "rank=same; " << ii << " -> " << sink_node << "[style=invis];" << "}\n";
    // ii++;
    // for (ii = 0; ii < index_to_instruction.size() + 1; ii++) {
    //   os << ii << " -> " << ii + 1 << "[style=invis];";
    // }

    // os << '}';

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


BladeGraph* buildBladeGraph(Function &F) {
  BladeGraph* graph = new BladeGraph(F);

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
      ValueDefNode* end_def_node = cast<ValueDefNode>(end);
      insertFenceAfter(F, end_def_node->inst);
    } else if (isa<SinkNode>(end)) {
      InstSinkNode* source_sink_node = cast<InstSinkNode>(src);
      insertFenceBefore(F, source_sink_node->inst);
    } else {
      InstructionNode* inst_end_node = cast<InstructionNode>(end);
      insertFenceBefore(F, inst_end_node->inst);
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
  auto cutset = graph->minCut();
  insertProtections(F, cutset, FENCE);

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
