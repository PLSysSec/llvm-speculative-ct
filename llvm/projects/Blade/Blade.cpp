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
#include <boost/graph/graph_traits.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/boykov_kolmogorov_max_flow.hpp>
#include <boost/graph/filtered_graph.hpp>
#include <boost/graph/depth_first_search.hpp>
#include <queue>
#include <stack>
#include <iostream>

#include <chrono>

using namespace llvm;

#define DEBUG_TYPE "blade"
#define D(X) DEBUG_WITH_TYPE(DEBUG_TYPE, errs() << X)

STATISTIC(NumCuts, "Total number of cuts resulting in a protect statement.");

struct BladeNode;
struct BladeEdge;

typedef boost::adjacency_list<boost::setS, boost::vecS, boost::bidirectionalS, BladeNode, BladeEdge> Graph;
typedef typename boost::graph_traits<Graph>::vertex_descriptor Vertex;
typedef typename boost::graph_traits<Graph>::edge_descriptor Edge;
typedef typename boost::graph_traits<Graph>::out_edge_iterator out_edge_iterator;

enum NodeType {
  DEFAULTNODE,
  SOURCENODE,
  SINKNODE,
  VALUEDEFNODE,
  INSTSINKNODE
};

struct BladeNode {
  NodeType node_type;
  Instruction* inst;

  BladeNode()
    : node_type(DEFAULTNODE), inst(nullptr) {}

  BladeNode(NodeType node_type, Instruction* inst)
    : node_type(node_type), inst(inst) {}

  friend raw_ostream& operator<<(raw_ostream& os, BladeNode const &node) {
    switch (node.node_type) {
    case SOURCENODE:
      return os << "source";
    case SINKNODE:
      return os << "sink";
    case VALUEDEFNODE:
      return os << "value: " << *(node.inst);
    case INSTSINKNODE:
      return os << "sink: " << *(node.inst);
    case DEFAULTNODE:
      return os;
    default:
      return os;
    }
  }
};

struct BladeEdge {
  int capacity;
  int residual_capacity;
  Edge reverse_edge;

  BladeEdge(int capacity)
    : capacity(capacity) {}
};

const BladeNode SourceNode() {
  return BladeNode(SOURCENODE, nullptr);
}

const BladeNode SinkNode() {
  return BladeNode(SINKNODE, nullptr);
}

BladeNode ValueDefNode(Instruction* inst) {
  return BladeNode(VALUEDEFNODE, inst);
}

BladeNode InstSinkNode(Instruction* inst) {
  return BladeNode(INSTSINKNODE, inst);
}

// typedef boost::adjacency_list<boost::vecS, boost::vecS, boost::bidirectionalS, BladeNode, BladeEdge> Graph;
// typedef typename boost::graph_traits<Graph>::vertex_descriptor Vertex;
// typedef typename boost::graph_traits<Graph>::edge_descriptor Edge;
// typedef typename boost::graph_traits<Graph>::out_edge_iterator out_edge_iterator;

class BladeGraph {
private:
  using Vertex = typename boost::graph_traits<Graph>::vertex_descriptor;

  Graph graph;
  ValueMap<Instruction*, std::pair<Vertex, Vertex>> instruction_to_vertex; // ValueDefNode, InstSinkNode

  Vertex source_vertex;
  Vertex sink_vertex;
  const BladeNode source_node = SourceNode();
  const BladeNode sink_node = SinkNode();

  size_t edge_index = 0;

public:
  BladeGraph(Function &F) {
    for (BasicBlock &BB : F) {
      for (Instruction &I : BB) {
        Vertex value_def_vertex = boost::add_vertex(ValueDefNode(&I), graph);
        Vertex inst_sink_vertex = boost::add_vertex(InstSinkNode(&I), graph);
        instruction_to_vertex[&I] = {value_def_vertex, inst_sink_vertex};
      }
    }
    source_vertex = boost::add_vertex(source_node, graph);
    sink_vertex = boost::add_vertex(sink_node, graph);
  }

  Vertex nodeIndex(const BladeNode &node) {
    switch (node.node_type) {
    case SOURCENODE:
      return source_vertex;
    case SINKNODE:
      return sink_vertex;
    case VALUEDEFNODE:
      return instruction_to_vertex[node.inst].first;
    case INSTSINKNODE:
      return instruction_to_vertex[node.inst].second;
    case DEFAULTNODE:
      assert(false && "should never see a default node");
      exit(1);
    default:
      exit(1);
    }
  }

  void addEdge(const BladeNode &source, const BladeNode &target) {
    boost::add_edge(nodeIndex(source), nodeIndex(target), BladeEdge(1), graph);
  }

  void markAsSource(Instruction* inst) {
    addEdge(source_node, ValueDefNode(inst));
  }

  void markAsSink(Instruction* inst) {
    addEdge(InstSinkNode(inst), sink_node);
  }

private:
  struct PositiveResidual {
    Graph *g;
    PositiveResidual() {}
    PositiveResidual(Graph *g)
      : g(g) {}
    bool operator()(const Edge &edge) const {
      return (*g)[edge].residual_capacity > 0;
    }
  };

  template<class G>
  DenseSet<size_t> reachable(Vertex from, G &g) {
    DenseSet<size_t> reachable_set;
    reachableDFS<G>(from, reachable_set);
    return reachable_set;
  }

  template<class G>
  void reachableDFS(Vertex from, DenseSet<size_t> &reachable_set, G &g) {
    size_t from_index = boost::get(boost::get(boost::vertex_index, g), from);
    reachable_set.insert(from_index);

    typename boost::graph_traits<G>::out_edge_iterator out_edge, out_end;
    for (std::tie(out_edge, out_end) = boost::out_edges(from, g); out_edge != out_end; out_edge++) {
      Vertex target = boost::target(*out_edge, g);
      size_t target_index = boost::get(boost::get(boost::vertex_index, g), target);
      if (!reachable_set.contains(target_index)) {
        reachableDFS<G>(target, reachable_set, g);
      }
    }
  }

public:
  SmallVector<std::pair<BladeNode, BladeNode>> minCut() {
    boost::graph_traits<Graph>::edge_iterator edge, edges_end;
    for (std::tie(edge, edges_end) = boost::edges(graph); edge != edges_end; edge++) {
      Edge rev_edge;
      bool has_rev_edge;
      Vertex source = boost::source(*edge, graph);
      Vertex target = boost::target(*edge, graph);
      std::tie(rev_edge, has_rev_edge) = boost::edge(target, source, graph);
      if (!has_rev_edge) {
        rev_edge = boost::add_edge(target, source, BladeEdge(0), graph).first;
      }
    }

    for (std::tie(edge, edges_end) = boost::edges(graph); edge != edges_end; edge++) {
      Vertex source = boost::source(*edge, graph);
      Vertex target = boost::target(*edge, graph);
      Edge rev_edge = boost::edge(target, source, graph).first;
      graph[*edge].reverse_edge = rev_edge;
      graph[rev_edge].reverse_edge = *edge;
    }

    boost::boykov_kolmogorov_max_flow(graph,
                                      boost::get(&BladeEdge::capacity, graph),
                                      boost::get(&BladeEdge::residual_capacity, graph),
                                      boost::get(&BladeEdge::reverse_edge, graph),
                                      boost::get(boost::vertex_index, graph),
                                      source_vertex, sink_vertex);

    boost::filtered_graph<Graph, PositiveResidual> filtered_residual_graph = boost::filtered_graph(graph, PositiveResidual(&graph));

    DenseSet<size_t> reachable_set;
    reachableDFS<boost::filtered_graph<Graph, PositiveResidual>>(source_vertex, reachable_set, filtered_residual_graph);

    auto vertices = boost::vertices(graph).first;
    SmallVector<std::pair<BladeNode, BladeNode>> cutset;
    for (size_t ii = 0; ii < boost::num_vertices(graph); ii++) {
      if (reachable_set.contains(ii)) {
        Vertex source = vertices[ii];
        out_edge_iterator out_edge, out_end;
        for (std::tie(out_edge, out_end) = boost::out_edges(source, graph); out_edge != out_end; out_edge++) {
          Vertex target = boost::target(*out_edge, graph);
          size_t target_index = boost::get(boost::get(boost::vertex_index, graph), target);
          if (!reachable_set.contains(target_index) && graph[*out_edge].capacity > 0) {
            cutset.push_back({graph[source], graph[target]});
          }
        }
      }
    }

    // errs() << "cutset:" << "\n";
    // for (auto cut : cutset) {
    //   errs() << cut.first << " -> " << cut.second << "\n";
    // }
    // errs() << "\n";

    return cutset;
  }

  friend raw_ostream& operator<<(raw_ostream& os, BladeGraph &graph) {
    os << "digraph " << " {" << "\n";

    boost::graph_traits<Graph>::edge_iterator edge, end;
    for (std::tie(edge, end) = boost::edges(graph.graph); edge != end; edge++) {
      os << '"' << graph.graph[boost::source(*edge, graph.graph)] << '"'
        << " -> "
        << '"' << graph.graph[boost::target(*edge, graph.graph)] << '"'
        << ";\n";
    }

    os << "}";
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


bool insertFences(Function &F, SmallVector<std::pair<BladeNode, BladeNode>> &cutset) {
  for (auto &edge : cutset) {
    auto &src = edge.first;
    auto &end = edge.second;

    if (src.node_type == SOURCENODE) {
      insertFenceAfter(F, end.inst);
    } else if (end.node_type == SINKNODE) {
      insertFenceBefore(F, src.inst);
    } else {
      Instruction* inst = end.inst;
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

// @brief Inserts protections right after leaky instructions given by cutset to defend
// against speculative leaks.
// @param prot see enum ProtectType
bool insertProtections(Function &F, SmallVector<std::pair<BladeNode, BladeNode>> &cutset, ProtectType prot) {
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
