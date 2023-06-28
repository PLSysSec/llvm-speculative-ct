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

struct SAAPass: public ModulePass {
    static char ID;

    SAAPass(): ModulePass(ID) {}

    ~SAAPass() {}

    static void init(Module &m) {
        splitConstExpr(m);
        initValueUid(m, Globals::ValueUidMap);
        DbgInfo::load(DbgBc);
        Globals::ExportLabel = std::move(ExportLabel);
        if (CreateLib != "") {
            std::ifstream ifile(CreateLib);
            std::string line;
            std::string word;
            std::string fn;
            // std::istringstream sline;

            while (std::getline(ifile, line)) {
                // check if the declassification information is given
                std::vector<std::string> apiInfo;
                std::istringstream iss{line};
                while(std::getline(iss, word, ' ')) {
                    apiInfo.push_back(word);
                }
                // dbgs() << "Printing the vector\n" ;
                // for (auto str: apiInfo) {
                //     dbgs() << str << "\n";
                // }
                // dbgs() << "Done printing the vector\n";

                Globals::DirFuncs[m.getFunction(apiInfo[0])] =  apiInfo;
            }
            ifile.close();
            Globals::IsLib = true;

            // static std::error_code EC;
            // static raw_fd_ostream Output(ApisReportFile, EC, sys::fs::OF_Append);
            // Globals::ApisReport = &Output;
        }
        // if (HotspotsFile != "") {
        //     std::ifstream ifile(HotspotsFile);
        //     std::string line;
        //     while (std::getline(ifile, line)) {
        //         Globals::Hotspots.insert(line);
        //     }
        //     ifile.close();
        // }
        if (SkipFile != "") {
            std::ifstream ifile(SkipFile);
            std::string line;
            while (std::getline(ifile, line)) {
                Globals::SkipFuncs.insert(line);
            }
            ifile.close();
        }
        static std::error_code EC;
        static raw_fd_ostream Output(TaintReportFile, EC, sys::fs::OF_Append);
        Globals::TaintReport = &Output;
        if (Threshold != "")
            Globals::Threshold = atof(Threshold.c_str());
    }

    bool runOnModule(Module &m) override {

        init(m);

        // Different logic for Library and the application client
        if (Globals::IsLib) {

            // Only library needs this
            linkMemModule(m);           // maybe should throw error if it can't link
            // Create a wrapper for the exported API functions
            lib_fn_wrapper(m);
            // Not planning to do any points-to and taint analysis here
            // We are going to assume that all the memory operation here
            // will happen in the Secure MPK domain. However we need to
            // change the dynamic memory allocation calls to mpk based allocs.
            replaceLibRuntime(m);
        } else {
            for (Function &func: m) {
                if (func.getName().str() == CheckFunctionName) {
                    errs() << "Entry Point Found!\n";
                    // this will trigger both points-to and taint analysis
                    start_analyze(m, func);
                    break;
                }
            }
            replaceRuntime(m);
        }

        // if (Globals::IsLib) {
        //    Globals::ApisReport->close();
        // }
        Globals::TaintReport->close();
        return true;
    }

    void getAnalysisUsage(AnalysisUsage &AU) const override {
        AU.setPreservesAll();
        AU.addRequired<LoopInfoWrapperPass>();
    }

    void start_analyze(Module &m, Function &entry) {
        GlobalVisitor<AliasTaintContext> visitor(m, entry);
        visitor.addCallback<AliasAnalysisVisitor>();
        visitor.addCallback<TaintAnalysisVisitor>();
        visitor.analyze();
        visitor.clearCallbacks();
        // DEBUG_PASSENTRY(dbgs() << "ModifyVisitor analyze\n");
        auto modifyvisitor = visitor.addCallback<ModifyCallbackVisitor>();
        visitor.analyze();
        modifyvisitor->run_modify();
    }
};



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


class RobustifyApp {
private:
  std::map<Function *, std::vector<std::string>> DirFuncs;
  std::set<Function *> ClonedDirFuncs;
  std::set<std::string> SkipFuncs;
  std::string ExportLabel;
  std::string EntryPointName;

  void lib_fn_wrapper(Module &m);

public:
  RobustifyApp(std::string EntryPointName)
    : EntryPointName(EntryPointName) {}

  ~RobustifyApp() {}

  void init(Module &m) {
    splitConstExpr(m);
  }

  bool runOnModule(Module &m) {
    Function* func = m.getFunction(EntryPointName);
    if (func) {
      // this will trigger both points-to and taint analysis
      start_analyze(m, func);
    }

    replaceRuntime(m);
    return true;
  }

  void start_analyze(Module &m, Function &entry) {
    GlobalVisitor<AliasTaintContext> visitor(m, entry);
    visitor.addCallback<AliasAnalysisVisitor>();
    visitor.addCallback<TaintAnalysisVisitor>();
    visitor.analyze();
    visitor.clearCallbacks();
    DEBUG_PASSENTRY(dbgs() << "ModifyVisitor analyze\n");
    auto modifyvisitor = visitor.addCallback<ModifyCallbackVisitor>();
    visitor.analyze();
    modifyvisitor->run_modify();
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
    RA.init(M);
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
