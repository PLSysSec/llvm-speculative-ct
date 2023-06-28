#ifndef TAINTVISITOR_H
#define TAINTVISITOR_H

#include "VisitorCallback.h"
#include "AliasTaintCtx.h"


struct TaintAnalysisVisitor: public VisitorCallback<AliasTaintContext> {
    TaintAnalysisVisitor(AliasTaintContext* &ctx, Module &m)
        : VisitorCallback(ctx, m) { }

    virtual void visitCastInst(CastInst &I);

    virtual void visitBinaryOperator(BinaryOperator &I);
    virtual void visitPHINode(PHINode &I);
    virtual void visitSelectInst(SelectInst &I);

    virtual void visitGetElementPtrInst(GetElementPtrInst &I);
    virtual void visitLoadInst(LoadInst &I);
    virtual void visitStoreInst(StoreInst &I);
    virtual void visitMemTransferInst(MemTransferInst &I);

    virtual void visitReturnInst(ReturnInst &I);
    virtual void visitLibFunctions(CallInst &I, Function *func);
    virtual bool visitCallInst(CallInst &I, Function *targetFunction);

    virtual void setupChildContext(CallInst &I, AliasTaintContext *parentContext);
    virtual void stitchChildContext(CallInst &I, AliasTaintContext *childContext);
};

#endif  // TAINTVISITOR_H
