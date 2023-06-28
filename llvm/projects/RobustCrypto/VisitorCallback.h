#ifndef VISITORCALLBACK_H
#define VISITORCALLBACK_H

#include <llvm/IR/Module.h>
#include <llvm/IR/Instructions.h>
#include "llvm/IR/IntrinsicInst.h"

using namespace llvm;

template<typename CtxClass>
struct VisitorCallback {
    CtxClass* &currCtx;
    Module &mod;
    bool enabled;

    VisitorCallback(CtxClass* &ctx, Module &m)
        : currCtx(ctx), mod(m), enabled(true) { }

    virtual ~VisitorCallback() { }

    virtual void visit(Instruction &I) { }

#define DEFINE_VISIT_FUNC(TYPE) \
    virtual void visit##TYPE(TYPE &I) { }
#include "Instruction.def"
#undef DEFINE_VISIT_FUNC

    virtual bool visitCallInst(CallInst &I, Function *targetFunction) {
        return !targetFunction->isDeclaration();
    }

    virtual void setupChildContext(CallInst &I, CtxClass *parentContext) { }
    virtual void stitchChildContext(CallInst &I, CtxClass *childContext) { }
};

#endif  // VISITORCALLBACK_H
