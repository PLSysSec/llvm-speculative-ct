#ifndef ALIASVISITOR_H
#define ALIASVISITOR_H

#include "VisitorCallback.h"
#include "AliasTaintCtx.h"


struct AliasAnalysisVisitor: public VisitorCallback<AliasTaintContext> {
    AliasAnalysisVisitor(AliasTaintContext* &ctx, Module &m);

    virtual void visitAllocaInst(AllocaInst &I);
    virtual void visitCastInst(CastInst &I);

    virtual void visitBinaryOperator(BinaryOperator &I);
    virtual void visitPHINode(PHINode &I);
    virtual void visitSelectInst(SelectInst &I);

    virtual void visitGetElementPtrInst(GetElementPtrInst &I);
    virtual void visitLoadInst(LoadInst &I);
    virtual void visitStoreInst(StoreInst &I);
    virtual void visitMemTransferInst(MemTransferInst &I);

    virtual void visitReturnInst(ReturnInst &I);
    virtual bool visitCallInst(CallInst &I, Function *targetFunction);

    virtual void setupChildContext(CallInst &I, AliasTaintContext *parentContext);
    virtual void stitchChildContext(CallInst &I, AliasTaintContext *childContext);

private:
    void visitLibFunctions(CallInst &I, Function *targetFunction);
};

#endif  // ALIASVISITOR_H
