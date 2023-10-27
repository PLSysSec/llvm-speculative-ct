#include "Utils.h"
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
#include <llvm/IR/Metadata.h>
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

using namespace llvm;

void replaceLibRuntime(Module &m) {
    // replace malloc with mpk_malloc
    auto malloc_fn = m.getFunction("malloc");
    auto mpk_malloc_fn = m.getFunction("mpk_malloc");
    if (malloc_fn) {
        malloc_fn->replaceAllUsesWith(mpk_malloc_fn);
    }

    // replace realloc with mpk_realloc
    auto realloc_fn = m.getFunction("realloc");
    auto mpk_realloc_fn = m.getFunction("mpk_realloc");
    if (realloc_fn) {
        realloc_fn->replaceAllUsesWith(mpk_realloc_fn);
    }

    // replace free with mpk_free
    auto free_fn = m.getFunction("free");
    auto mpk_free_fn = m.getFunction("mpk_free");
    if (free_fn) {
        free_fn->replaceAllUsesWith(mpk_free_fn);
    }
}

void linkMemModule(Module &m) {
  /// SMDiagnostic Err;

  /// auto mod = parseIRFile("mem.ll", Err, m.getContext());
  /// if(!mod) {
  ///   Err.print("mem.ll", errs());
  ///   return;
  /// }

  /// bool result = Linker::linkModules(m, move(mod));
  /// if(result) {
  ///   errs() << "FAIL: Couldn't link the two modules\n";
  ///   return;
  /// }

  Type* unsignedIntType = Type::getInt64Ty(m.getContext());
  Type* voidPtrType = Type::getInt8PtrTy(m.getContext());
  Type* voidType = Type::getVoidTy(m.getContext());

  // void *mpk_malloc(unsigned int);
  FunctionType* mpkMallocSig = FunctionType::get(voidPtrType, {unsignedIntType}, false);
  // void mpk_free(void *);
  FunctionType* mpkFreeSig = FunctionType::get(voidType, {voidPtrType}, false);
  // void *bash_get_page();
  FunctionType* bashGetPageSig = FunctionType::get(voidPtrType, false);
  // void bash_free_page(void *);
  FunctionType* bashFreePageSig = FunctionType::get(voidType, {voidPtrType}, false);

  Function::Create(mpkMallocSig, Function::ExternalLinkage, "mpk_malloc", m);
  Function::Create(mpkFreeSig, Function::ExternalLinkage, "mpk_free", m);
  Function::Create(bashGetPageSig, Function::ExternalLinkage, "bash_get_page", m);
  Function::Create(bashFreePageSig, Function::ExternalLinkage, "bash_free_page", m);
}

class RobustifyLibrary {
private:
  std::map<Function *, std::vector<std::string>> DirFuncs;
  std::set<Function *> ClonedDirFuncs;
  std::set<std::string> SkipFuncs;
  std::string ExportLabel;
  std::string ApiFileName;

  void lib_fn_wrapper(Module &m);

public:
  RobustifyLibrary(std::string ApiFileName)
    : ApiFileName(ApiFileName) {}

  ~RobustifyLibrary() {}

  void init(Module &m) {
    splitConstExpr(m);

    std::ifstream ifile(ApiFileName);
    std::string line;
    std::string word;
    std::string fn;

    while (std::getline(ifile, line)) {
      // TODO(MATT): skip as "!" preceding name

      // check if the declassification information is given
      std::vector<std::string> apiInfo;
      std::istringstream iss{line};
      while (std::getline(iss, word, ' ')) {
        apiInfo.push_back(word);
      }

      if (apiInfo.empty()) {
        continue;
      }
      // dbgs() << "Printing the vector\n" ;
      // for (auto str: apiInfo) {
      //     dbgs() << str << "\n";
      // }
      // dbgs() << "Done printing the vector\n";

      /*
       * note to future users, declassify specifications take the following forms
       * - arg_index COPY_TYPE 0 constant_width
       * - arg_index COPY_TYPE 1 len_arg_index sizeof_underlying_arg_type
       *
       * COPY_TYPE ::= 0 (copy in, copy out)
       *            |  1 (copy out)
       */
      DirFuncs[m.getFunction(apiInfo[0])] = apiInfo;
    }
    ifile.close();
  }

  bool runOnModule(Module &m) {
    linkMemModule(m);           // maybe should throw error if it can't link
    // Create a wrapper for the exported API functions
    lib_fn_wrapper(m);
    // Not planning to do any points-to and taint analysis here
    // We are going to assume that all the memory operation here
    // will happen in the Secure MPK domain. However we need to
    // change the dynamic memory allocation calls to mpk based allocs.
    replaceLibRuntime(m);

    return true;
  }
};

// TODO(MATT): need to change references to separately compiled library
// functions to their proper internal version
void RobustifyLibrary::lib_fn_wrapper(Module &m) {
  auto &ctx = m.getContext();
  auto voidty = Type::getVoidTy(ctx); auto int8ptrty = Type::getInt8PtrTy(ctx);
  auto int64ty = Type::getInt64Ty(ctx); auto int32ty = Type::getInt32Ty(ctx);

  // LLVMContext context;
  SMDiagnostic Err;
  ValueToValueMapTy VMap;

  for (Function &func: m) {

    // skip the non-export functions
    if (DirFuncs.find(&func) == DirFuncs.end()) {
      continue;
    }

    // skip if the function is already wrapped
    if (ClonedDirFuncs.find(&func) != ClonedDirFuncs.end()) {
      continue;
    } else {
      // add it to the set
      ClonedDirFuncs.insert(&func);
    }

    auto cloned = CloneFunction(&func, VMap);
    auto cloned_name = func.getName().str() + "_robust_crypto_cloned";
    cloned->setName(cloned_name);
    cloned->addFnAttr(Attribute::NoInline);
    // cloned->print(errs(), nullptr);

    // Replace all the internal uses of this API call with the cloned function
    func.replaceAllUsesWith(cloned);

    bool has_declassify_arg = DirFuncs[&func].size() > 1;
    bool declassify_copy_in = false;
    bool declassify_copy_out = false;
    bool declassify_const_size;

    if (has_declassify_arg) {
      auto copy_type = stoi(DirFuncs[&func][2]);
      switch (copy_type) {
      case 0:
        declassify_copy_in = true;
        declassify_copy_out = true;
        break;
      case 1:
        declassify_copy_out = true;
        break;
      }

      auto width_type = stoi(DirFuncs[&func][3]);
      switch (width_type) {
      case 0:
        declassify_const_size = true;
        break;
      case 1:
        declassify_const_size = false;
        break;
      }
    }

    // Get the entry point to add instructions
    auto eBB = &func.getEntryBlock();

    auto entryBB = BasicBlock::Create(ctx, "entryBB", &func, eBB);
    IRBuilder<> builder(entryBB);

    int pkey = 1;
    int allow = 0;
    int disallow = 3;
    Value *zero = ConstantInt::get(int32ty, 0);
    Value *perm = ConstantInt::get(int32ty, allow << (2 * pkey));

    // insert privilege escalation code
    auto asmtype = FunctionType::get(voidty, {int32ty, int32ty, int32ty}, false);
    auto asminst = InlineAsm::get(asmtype, "wrpkru", "{ax},{cx},{dx}", true);
    builder.CreateCall(asminst, SmallVector<Value*, 3>{perm, zero, zero});

    // Copy the original arguments to cloned function arguments
    std::vector<Value*> cloned_args;
    for (auto& arg: func.args()) {
      cloned_args.push_back(&arg);
    }

    Value* declassify_arg = nullptr;
    CallInst* declassify_arg_malloc;
    Value* declassify_argsize = nullptr;

    // Create a protected memory version for declassified value
    // TODO: need to deal with many cases
    if (has_declassify_arg) {
      auto opInt = stoi(DirFuncs[&func][1]);
      auto fn_arg = func.arg_begin();
      fn_arg += opInt;
      // auto target = fn_arg->getType();
      // auto stripped = fn_arg->stripPointerCasts();
      auto mallocfunc = m.getFunction("mpk_malloc");

      // testing with static sizes
      // TODO: BASH deal with different cases
      // auto &dl = m.getDataLayout();
      // store the passed client declassified arg
      declassify_arg = cloned_args[opInt];    // declassify arg index

      // deal with Arg param for malloc len
      if (declassify_const_size) {
        declassify_argsize = ConstantInt::get(int64ty, stoi(DirFuncs[&func][4]));
      } else {
        auto len_arg_index = stoi(DirFuncs[&func][4]);
        auto len_arg_type = func.getFunctionType()->getParamType(len_arg_index);
        auto arg_sizeof = stoi(DirFuncs[&func][5]);
        if (isa<IntegerType>(len_arg_type)) {
          declassify_argsize = builder.CreateMul(ConstantInt::get(len_arg_type, arg_sizeof), cloned_args[len_arg_index]);
        } else if(isa<PointerType>(len_arg_type)) {
          auto arg_multiplicity = builder.CreateLoad(int64ty, cloned_args[len_arg_index], "");
          declassify_argsize = builder.CreateMul(ConstantInt::get(int64ty, arg_sizeof), arg_multiplicity);
        } else {
          errs() << "invalid type for declassify length argument" << "\n";
          exit(1);
        }
      }

      // create callinst
      std::vector<Value*> margs;
      margs.push_back(declassify_argsize);
      declassify_arg_malloc = builder.CreateCall(mallocfunc->getFunctionType(), mallocfunc, margs);

      if (declassify_copy_in) {
        // copy the client mem to protected lib mem
        builder.CreateMemCpy(declassify_arg_malloc, MaybeAlign(), declassify_arg, MaybeAlign(), declassify_argsize, false);
      }

      // replace the declassify arg with declassify_arg_malloc arg
      cloned_args[opInt] = declassify_arg_malloc;
    }

    // Get a page(mmap) for the stack frame
    auto get_page = m.getFunction("bash_get_page");
    std::vector<Value*> gpargs;
    for (auto& arg: get_page->args()) {
      gpargs.push_back(&arg);
    }
    auto page = builder.CreateCall(get_page->getFunctionType(), get_page, gpargs);
    auto page_addr_copy = page;

    // add (page_size * 2 - 8) to page addr as stack grows high to low addr
    // currently the value is hardcoded. TODO: change later
    asmtype = FunctionType::get(int8ptrty, {int8ptrty}, false);
    asminst = InlineAsm::get(asmtype, "add $$8176, $0\0A", "=r,0,~{dirflag},~{fpsr},~{flags}", true);
    page = builder.CreateCall(asminst, SmallVector<Value*, 1>{page});

    // store the current rsp
    asmtype = FunctionType::get(voidty, {int8ptrty}, false);
    asminst = InlineAsm::get(asmtype, "movq %rsp, $0\0A", "*m,~{dirflag},~{fpsr},~{flags}", true);
    auto movcall = builder.CreateCall(asminst, SmallVector<Value*, 1>{page});
    movcall->addParamAttr(0, Attribute::get(ctx, Attribute::ElementType, int8ptrty));

    // subtract 256 to give some space args on stack
    asmtype = FunctionType::get(int8ptrty, {int8ptrty}, false);
    asminst = InlineAsm::get(asmtype, "sub $$256, $0\0A", "=r,0,~{dirflag},~{fpsr},~{flags}", true);
    page = builder.CreateCall(asminst, SmallVector<Value*, 1>{page});

    // copying some stack mem from caller's stack to callee's stack
    Function *rsp_fun = Intrinsic::getDeclaration(&m, Intrinsic::read_register, builder.getIntPtrTy(m.getDataLayout()));
    auto metadata = llvm::MDNode::get(ctx, llvm::MDString::get(ctx, "rsp"));
    Value *rsp_args[] = {MetadataAsValue::get(ctx, metadata)};
    auto stack_addr_int = builder.CreateCall(rsp_fun, rsp_args);
    auto final_stack_addr = builder.CreateIntToPtr(stack_addr_int, int8ptrty);
    builder.CreateMemCpy(page, {}, final_stack_addr, {}, 248, true);

    // set the rsp to the addr in our page(s)
    asmtype = FunctionType::get(voidty, {int8ptrty}, false);
    asminst = InlineAsm::get(asmtype, "movq $0, %rsp\0A", "r,~{dirflag},~{fpsr},~{flags}", true);
    builder.CreateCall(asminst, SmallVector<Value*, 1>{page});

    // cloned function call
    CallInst* newcall;

    // Call the cloned(from original) function
    newcall = builder.CreateCall(cloned->getFunctionType(), cloned, cloned_args);

    // unwind the stack stuff
    asmtype = FunctionType::get(int8ptrty, {int8ptrty}, false);
    asminst = InlineAsm::get(asmtype, "add $$256, $0\0A", "=r,0,~{dirflag},~{fpsr},~{flags}", true);
    page = builder.CreateCall(asminst, SmallVector<Value*, 1>{page});

    //
    asmtype = FunctionType::get(voidty, {int8ptrty}, false);
    asminst = InlineAsm::get(asmtype, "movq $0, %rsp\0A", "r,~{dirflag},~{fpsr},~{flags}", true);
    builder.CreateCall(asminst, SmallVector<Value*, 1>{page});

    // pop the original rsp saved on page(s) into rsp register
    asmtype = FunctionType::get(voidty, {}, false);
    asminst = InlineAsm::get(asmtype, "popq %rsp", "~{dirflag},~{fpsr},~{flags}", true);
    builder.CreateCall(asminst, SmallVector<Value*, 1>{});

    // Release the page(unmap) used for the stack frame
    auto endF = m.getFunction("bash_free_page");
    std::vector<Value*> eargs;
    eargs.push_back(page_addr_copy);
    builder.CreateCall(endF->getFunctionType(), endF, eargs);

    if (has_declassify_arg) {
      if (declassify_copy_out) {
        // Copy back the results
        builder.CreateMemCpy(declassify_arg, MaybeAlign(), declassify_arg_malloc, MaybeAlign(), declassify_argsize, false);
      }

      if (!declassify_const_size) {
        // release the allocated memory
        auto freefunc = m.getFunction("mpk_free");
        std::vector<Value*> fargs;
        fargs.push_back(declassify_arg_malloc);
        builder.CreateCall(freefunc->getFunctionType(), freefunc, fargs);
      }
    }

    // insert privilege de-escalation code
    perm = ConstantInt::get(int32ty, disallow << (2 * pkey));
    asmtype = FunctionType::get(voidty, {int32ty, int32ty, int32ty}, false);
    asminst = InlineAsm::get(asmtype, "wrpkru", "{ax},{cx},{dx}", true);
    builder.CreateCall(asminst, SmallVector<Value*, 3>{perm, zero, zero});

    // Zero out the scratch registers / non callee saved  registers
    // TODO: a lot of duplicate code. make this is as a function later
    // rdi
    asmtype = FunctionType::get(voidty, {}, false);
    asminst = InlineAsm::get(asmtype, "xor %rdi, %rdi", "~{dirflag},~{fpsr},~{flags}", true);
    builder.CreateCall(asminst, SmallVector<Value*, 1>{});

    // rsi
    asmtype = FunctionType::get(voidty, {}, false);
    asminst = InlineAsm::get(asmtype, "xor %rsi, %rsi", "~{dirflag},~{fpsr},~{flags}", true);
    builder.CreateCall(asminst, SmallVector<Value*, 1>{});

    // rdx
    asmtype = FunctionType::get(voidty, {}, false);
    asminst = InlineAsm::get(asmtype, "xor %rdx, %rdx", "~{dirflag},~{fpsr},~{flags}", true);
    builder.CreateCall(asminst, SmallVector<Value*, 1>{});

    // rcx
    asmtype = FunctionType::get(voidty, {}, false);
    asminst = InlineAsm::get(asmtype, "xor %rcx, %rcx", "~{dirflag},~{fpsr},~{flags}", true);
    builder.CreateCall(asminst, SmallVector<Value*, 1>{});

    // r8
    asmtype = FunctionType::get(voidty, {}, false);
    asminst = InlineAsm::get(asmtype, "xor %r8, %r8", "~{dirflag},~{fpsr},~{flags}", true);
    builder.CreateCall(asminst, SmallVector<Value*, 1>{});

    // r9
    asmtype = FunctionType::get(voidty, {}, false);
    asminst = InlineAsm::get(asmtype, "xor %r9, %r9", "~{dirflag},~{fpsr},~{flags}", true);
    builder.CreateCall(asminst, SmallVector<Value*, 1>{});

    // r10
    asmtype = FunctionType::get(voidty, {}, false);
    asminst = InlineAsm::get(asmtype, "xor %r10, %r10", "~{dirflag},~{fpsr},~{flags}", true);
    builder.CreateCall(asminst, SmallVector<Value*, 1>{});

    // r11
    asmtype = FunctionType::get(voidty, {}, false);
    asminst = InlineAsm::get(asmtype, "xor %r11, %r11", "~{dirflag},~{fpsr},~{flags}", true);
    builder.CreateCall(asminst, SmallVector<Value*, 1>{});

    // rflags
    // TODO

    if (newcall->getType()->isVoidTy()) {
      // rax
      asmtype = FunctionType::get(voidty, {}, false);
      asminst = InlineAsm::get(asmtype, "xor %rax, %rax", "~{dirflag},~{fpsr},~{flags}", true);
      builder.CreateCall(asminst, SmallVector<Value*, 1>{});

      // Return instr
      builder.CreateRet(nullptr);
    } else {
      // Return the cloned function call return Value
      builder.CreateRet(newcall);
    }

    // Some sanity checks
    llvm::EliminateUnreachableBlocks(func);
    llvm::verifyFunction(func, &llvm::outs());
    llvm::verifyModule(m, &llvm::outs());
    // func.print(errs(), nullptr);
  }
}

class RobustifyLibraryPass : public PassInfoMixin<RobustifyLibraryPass> {
public:
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM) {
    std::string ApiFileName;
    const char *envVal = std::getenv("ROBUSTIFY_API_FILE");
    ApiFileName = envVal == nullptr ? "" : envVal;

    if (ApiFileName == "")
      return PreservedAnalyses::all();

    RobustifyLibrary RL(ApiFileName);
    RL.init(M);
    return RL.runOnModule(M) ? PreservedAnalyses::none() : PreservedAnalyses::all();
  }
};

PassPluginLibraryInfo getPassPluginInfo() {
  const auto callback = [](PassBuilder &PB) {
    PB.registerPipelineStartEPCallback([&](ModulePassManager &MPM, auto) {
      MPM.addPass(RobustifyLibraryPass());
      return true;
    });
  };

  return {LLVM_PLUGIN_API_VERSION, "RobustifyLibrary", "0.0.1", callback};
};

extern "C" LLVM_ATTRIBUTE_WEAK PassPluginLibraryInfo llvmGetPassPluginInfo() {
  return getPassPluginInfo();
}
