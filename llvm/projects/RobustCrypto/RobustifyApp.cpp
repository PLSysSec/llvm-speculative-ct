#include "llvm/ADT/SCCIterator.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include <llvm/IR/DebugInfoMetadata.h>
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Linker/Linker.h"
#include "llvm/Pass.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include <algorithm>
#include <fstream>
#include <map>
#include <queue>
#include <set>
#include <sstream>
#include <vector>
#include "AliasAnalysisVisitor.h"
#include "BaseContext.h"
#include "GlobalVisitor.h"
#include "ModifyVisitor.h"
#include "TaintAnalysisVisitor.h"
#include "Utils.h"

using namespace llvm;

void replaceRuntime(Module &M) {
    auto &ctx = M.getContext();
    auto voidty = Type::getVoidTy(ctx);
    auto int8ptrty = Type::getInt8PtrTy(ctx);
    auto int64ty = Type::getInt64Ty(ctx);

    auto freefunc = M.getFunction("free");
    // auto freetype = TypeBuilder<void(int8_t*), false>::get(M.getContext());
    auto freetype = FunctionType::get(voidty, {int8ptrty}, false);
    auto mfreefunc = M.getOrInsertFunction("m_free", freetype);
    if (freefunc)
        freefunc->replaceAllUsesWith(mfreefunc.getCallee());

    // auto mallocfunc = M.getFunction("malloc");
    // auto malloctype = TypeBuilder<int8_t*(int64_t), false>::get(M.getContext());
    // auto umallocfunc = M.getOrInsertFunction("u_malloc", malloctype);
    // if (mallocfunc)
    //     mallocfunc->replaceAllUsesWith(umallocfunc);

    auto reallocfunc = M.getFunction("realloc");
    // auto realloctype = TypeBuilder<int8_t*(int8_t*, int64_t), false>::get(M.getContext());
    auto realloctype = FunctionType::get(int8ptrty, {int8ptrty, int64ty}, false);
    auto mreallocfunc = M.getOrInsertFunction("m_realloc", realloctype);
    if (reallocfunc)
        reallocfunc->replaceAllUsesWith(mreallocfunc.getCallee());
}

void initValueUid(Module &M, Globals &globals) {
  std::size_t cnt = 0xdeadbeef00000000;
  for (auto &F : M) {
    globals.ValueUidMap[&F] = cnt;
    // dbgs() << &F << "\n";
    cnt++;
    for (auto &BB : F) {
      globals.ValueUidMap[&BB] = cnt;
      // dbgs() << "  " << &BB << "\n";
      cnt++;
      for (auto &II : BB) {
        globals.ValueUidMap[&II] = cnt;
        // dbgs() << "    " << &II << " ";
        cnt++;
      }
    }
  }
}

// class RobustifyApp {
// private:
//   std::string EntryPointName;
//   Globals globals;

// public:
//   RobustifyApp(std::string EntryPointName)
//     : EntryPointName(EntryPointName) {}

//   ~RobustifyApp() {}

//   void init(Module &m) {
//     splitConstExpr(m);
//     initValueUid(m, globals);
//   }

//   bool runOnModule(Module &m) {
//     Function* func = m.getFunction(EntryPointName);
//     if (func) {
//       // this will trigger both points-to and taint analysis
//       start_analyze(m, *func);
//     }

//     replaceRuntime(m);
//     return true;
//   }

//   void start_analyze(Module &m, Function &entry) {
//     GlobalVisitor<AliasTaintContext> visitor(m, entry, globals);
//     visitor.addCallback<AliasAnalysisVisitor>();
//     visitor.addCallback<TaintAnalysisVisitor>();
//     visitor.analyze();
//     visitor.clearCallbacks();

//     // DEBUG_PASSENTRY(dbgs() << "ModifyVisitor analyze\n");
//     auto modifyvisitor = visitor.addCallback<ModifyCallbackVisitor>();
//     visitor.analyze();
//     modifyvisitor->run_modify();
//   }
// };

class RobustifyApp {
private:
  std::string EntryPointName;

public:
  RobustifyApp(std::string EntryPointName)
    : EntryPointName(EntryPointName) {}

  ~RobustifyApp() {}

  bool runOnModule(Module &m) {
    Function* func = m.getFunction(EntryPointName);
    if (func) {
      auto int8ptrty = Type::getInt8PtrTy(m.getContext());
      auto voidty = Type::getVoidTy(m.getContext());
      GlobalVariable* secure_stack_ptr = new GlobalVariable(m,
                                                            int8ptrty,
                                                            false,
                                                            GlobalValue::CommonLinkage,
                                                            ConstantPointerNull::get(int8ptrty),
                                                            "robust_crypto_stack_pointer");
      FunctionType* bashGetPageSig = FunctionType::get(int8ptrty, false);
      Function::Create(bashGetPageSig, Function::ExternalLinkage, "bash_get_page", m);

      FunctionType* get_robust_crypto_stack_pointer_sig = FunctionType::get(int8ptrty, false);
      Function* get_robust_crypto_stack_pointer = Function::Create(get_robust_crypto_stack_pointer_sig, Function::ExternalLinkage, "get_robust_crypto_stack_pointer", m);
      auto entryBB = BasicBlock::Create(m.getContext(), "entryBB", get_robust_crypto_stack_pointer, nullptr);

      IRBuilder<> stack_pointer_builder(entryBB);
      auto loaded_stack_ptr = stack_pointer_builder.CreateLoad(int8ptrty, secure_stack_ptr, "");
      stack_pointer_builder.CreateRet(loaded_stack_ptr);

      BasicBlock &eBB = func->getEntryBlock();
      Instruction *start_point = nullptr;
      for (Instruction &inst : eBB) {
        if (!isa<AllocaInst>(inst)) {
          start_point = &inst;
          break;
        }
      }

      IRBuilder<> builder(start_point);
      auto get_page = m.getFunction("bash_get_page");
      std::vector<Value*> gpargs;
      auto page = builder.CreateCall(get_page->getFunctionType(), get_page);

      // add (page_size * 2 - 8) to page addr as stack grows high to low addr
      // currently the value is hardcoded. TODO: change later
      auto asmtype = FunctionType::get(int8ptrty, {int8ptrty}, false);
      auto asminst = InlineAsm::get(asmtype, "add $$8176, $0\0A", "=r,0,~{dirflag},~{fpsr},~{flags}", true);
      page = builder.CreateCall(asminst, SmallVector<Value*, 1>{page});
      builder.CreateStore(page, secure_stack_ptr);
    }
    return true;
  }
};

class RobustifyAppPass : public PassInfoMixin<RobustifyAppPass> {
public:
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM) {
    std::string EntryPointName;
    const char *envVal = std::getenv("ROBUSTIFY_ENTRY_POINT");
    EntryPointName = envVal == nullptr ? "" : envVal;

    if (EntryPointName == "")
      return PreservedAnalyses::all();

    RobustifyApp RA(EntryPointName);
    return RA.runOnModule(M) ? PreservedAnalyses::none() : PreservedAnalyses::all();
  }
};

PassPluginLibraryInfo getPassPluginInfo() {
  const auto callback = [](PassBuilder &PB) {
    PB.registerPipelineStartEPCallback([&](ModulePassManager &MPM, auto) {
      MPM.addPass(RobustifyAppPass());
      return true;
    });
  };

  return {LLVM_PLUGIN_API_VERSION, "RobustifyApp", "0.0.1", callback};
};

extern "C" LLVM_ATTRIBUTE_WEAK PassPluginLibraryInfo llvmGetPassPluginInfo() {
  return getPassPluginInfo();
}
