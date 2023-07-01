#ifndef MODIFYVISITOR_H
#define MODIFYVISITOR_H

#include "AliasTaintCtx.h"
#include "ModObject.h"
#include "Utils.h"
#include "VisitorCallback.h"
#include <llvm/Support/FormatVariadic.h>
#include <llvm/Transforms/Utils/Cloning.h>

struct ModifiedFunction : public FuncMod {
  Function *origfunc;
  size_t ctxhash;
  bool isentry, callerprotect, need_callerprotect;
  Function *newfunc;
  std::unique_ptr<ValueToValueMapTy> vmap;

  ModifiedFunction(Globals* ValueUidMap)
    : FuncMod(ValueUidMap), isentry(false), callerprotect(false), newfunc(nullptr)
  {}

  template <typename T> T *resolve_inst(T *val) {
    if (!vmap)
      return val;
    auto tmp = (*vmap)[val];
    if (!tmp)
      return val;
    auto ret = dyn_cast<T>(tmp);
    assert(ret);
    return ret;
  }
};

struct ModifiedFunctionList {
  std::map<std::pair<Function *, size_t>, ModifiedFunction> map;
  std::vector<ModifiedFunction *> list;

  ModifiedFunction *tryinsert(AliasTaintContext *ctx) {
    ModifiedFunction tmp = ModifiedFunction(&(ctx->globals));
    tmp.origfunc = ctx->func;
    tmp.fn_map = std::move(ctx->funcmod.fn_map);
    tmp.returnlist = std::move(ctx->funcmod.returnlist);
    tmp.ctxhash = tmp.calcHash();
    tmp.calledbyExportFn = ctx->funcmod.calledbyExportFn;
    tmp.isExportFn = ctx->funcmod.isExportFn;

    auto key = std::make_pair(tmp.origfunc, tmp.ctxhash);
    auto ins = map.emplace(key, std::move(tmp));
    auto modfunc = &(ins.first->second);
    if (ins.second)
      list.push_back(modfunc);
    else {
      modfunc->calledbyExportFn |= ctx->funcmod.calledbyExportFn;
      modfunc->isExportFn |= ctx->funcmod.isExportFn;
    }
    return modfunc;
  }
};

struct ModifyCallbackVisitor : public VisitorCallback<AliasTaintContext> {
  static ModifiedFunctionList newfunctions;
  static std::set<Function *> analyzed_functions;

  ModifyCallbackVisitor(AliasTaintContext *&ctx, Module &m)
      : VisitorCallback(ctx, m) {}

  virtual void visitAllocaInst(AllocaInst &I);
  virtual void visitLoadInst(LoadInst &I);
  virtual void visitStoreInst(StoreInst &I);
  virtual void visitMemTransferInst(MemTransferInst &I);
  virtual void visitMemSetInst(MemSetInst &I);
  virtual bool visitCallInst(CallInst &I, Function *func);
  virtual void visitReturnInst(ReturnInst &I);
  virtual void setupChildContext(CallInst &I, AliasTaintContext *child);
  virtual void stitchChildContext(CallInst &I, AliasTaintContext *child);

  void prestat();
  void poststat();
  void run_modify();

private:
  FuncMod *funcmod() { return &(currCtx->funcmod); }

  void visitLibFunction(CallInst &I, Function *func, InstMod *instmod);
};

#endif // MODIFYVISITOR_H
