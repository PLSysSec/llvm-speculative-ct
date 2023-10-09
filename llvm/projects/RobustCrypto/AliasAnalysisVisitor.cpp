#include "AliasAnalysisVisitor.h"
#include "Utils.h"


AliasAnalysisVisitor::AliasAnalysisVisitor(AliasTaintContext* &ctx, Module &m)
        : VisitorCallback(ctx, m) {
    AliasTaintContext::setupGlobals(m);
}


void AliasAnalysisVisitor::visitAllocaInst(AllocaInst &I) {
    // DEBUG_LOADSTOR(dbgs() << "CreateRegMemPair: " << I << "\n");
    currCtx->createRegMemPair(&I);
}


void AliasAnalysisVisitor::visitCastInst(CastInst &I) {
    // TODO: Sanitize
    // some kinds of casts should not be allowed
    // e.g. struct to array
    auto op = I.getOpcode();
    if (op != Instruction::PtrToInt && op != Instruction::IntToPtr)
        return;
    auto src = I.getOperand(0);
    auto srcreg = currCtx->findOpReg(src);
    if (hasPointsTo(srcreg)) {
        // DEBUG_LOADSTOR(dbgs() << "Cast with points-to: " << I << "\n");
        auto dstreg = currCtx->getDestReg(&I);
        dstreg->mergePointsTo(srcreg, &I);
    }
}


void AliasAnalysisVisitor::visitBinaryOperator(BinaryOperator &I) {
    if (I.getOpcode() == Instruction::Mul) return;
    auto lhs = I.getOperand(0);
    auto rhs = I.getOperand(1);
    auto lreg = currCtx->findOpReg(lhs);
    auto rreg = currCtx->findOpReg(rhs);
    if (hasPointsTo(lreg)) {
        if (hasPointsTo(rreg)) {
            // DEBUG_LOADSTOR(dbgs() << "BinOp with double aliases: "
                                  // << I << "\n");
            // possibly calculating the offset between two pointers
            // ignore
        }
        auto dstreg = currCtx->getDestReg(&I);
        dstreg->mergePointsTo(lreg, &I);
    }
    if (hasPointsTo(rreg)) {
        auto dstreg = currCtx->getDestReg(&I);
        dstreg->mergePointsTo(rreg, &I);
    }
}


void AliasAnalysisVisitor::visitPHINode(PHINode &I) {
    RegObject *dst = nullptr;
    for (auto &use: I.incoming_values()) {
        auto reg = currCtx->findOpReg(use.get());
        if (hasPointsTo(reg)) {
            if (!dst) dst = currCtx->getDestReg(&I);
            dst->mergePointsTo(reg, &I);
        }
    }
}


void AliasAnalysisVisitor::visitSelectInst(SelectInst &I) {
    auto lhs = I.getTrueValue();
    auto rhs = I.getFalseValue();
    auto lreg = currCtx->findOpReg(lhs);
    auto rreg = currCtx->findOpReg(rhs);
    auto dstreg = currCtx->getDestReg(&I);
    if (hasPointsTo(lreg)) dstreg->mergePointsTo(lreg, &I);
    if (hasPointsTo(rreg)) dstreg->mergePointsTo(rreg, &I);
}


void AliasAnalysisVisitor::visitGetElementPtrInst(GetElementPtrInst &I) {
    if (I.hasAllZeroIndices()) return;
    unsigned offset = getGEPOffset(I, mod.getDataLayout());
    auto val = I.getPointerOperand();
    auto srcreg = currCtx->findOpReg(val);
    if (hasPointsTo(srcreg)) {
        auto dstreg = currCtx->getDestReg(&I);
        for (auto &pt: srcreg->pointsto) {
            // DEBUG_LOADSTOR(dbgs() << "Gep Offset: " << pt.dstoff+offset << " "<< I << "\n");
            dstreg->addPointsTo(pt.target, pt.dstoff+offset, &I);
        }
    }
}


void AliasAnalysisVisitor::visitLoadInst(LoadInst &I) {
    auto src = I.getPointerOperand();
    auto srcreg = currCtx->findOpReg(src);
    if (!hasPointsTo(srcreg)) return;
    // whether 2nd-level points-to should be ensured
    bool ensure2Lpt = I.getType()->isPointerTy()
        && (isa<GlobalObject>(src) || !currCtx->inside_loop);
    RegObject *dstreg = nullptr;
    AliasObject *newobj = nullptr;
    for (auto &pt: srcreg->pointsto) {
        // load 1st-level points-to
        auto fieldobj = pt.target->getFieldObj(pt.dstoff);
        if (hasPointsTo(fieldobj)) {
            // copy 2nd-level points-to
            if (!dstreg) dstreg = currCtx->getDestReg(&I);
            dstreg->mergePointsTo(fieldobj, &I);
        } else if (ensure2Lpt) {
            // create new 2nd-level points-to
            // DEBUG_LOADSTOR(dbgs() << "Load pointer failed: " << I << "\n");
            if (!newobj) newobj = currCtx->createRegMemPair(&I, true).second;
            fieldobj->addPointsTo(newobj, 0, nullptr);
        }
    }
}


void AliasAnalysisVisitor::visitStoreInst(StoreInst &I) {
    // where to store
    auto dstptr = I.getPointerOperand();
    auto dstreg = currCtx->findOpReg(dstptr);

    //TODO: Should we addpointsto if the destreg
    // doesn't have pointsto info already??
    if (!hasPointsTo(dstreg)) {
        assert(false);
        return;
    }
    // what to store
    auto srcval = I.getValueOperand();
    auto srcreg = currCtx->findOpReg(srcval);
    if (!hasPointsTo(srcreg)) return;
    // action
    for (auto &pt: dstreg->pointsto) {
        auto fieldobj = pt.target->getFieldObj(pt.dstoff);
        assert(fieldobj != nullptr);
        fieldobj->mergePointsTo(srcreg, &I);
    }
}


void AliasAnalysisVisitor::visitMemTransferInst(MemTransferInst &I) {
    auto len = I.getOperand(2);
    auto src = I.getOperand(1);
    auto dst = I.getOperand(0);
    auto srcreg = currCtx->findOpReg(src);
    auto dstreg = currCtx->findOpReg(dst);
    if (!hasPointsTo(srcreg) || !hasPointsTo(dstreg)) {
        assert(false);
        return;
    }
    // collect fields to transfer
    std::vector<std::pair<FieldIdTy, FieldObject*> > tmp;
    auto lenint = dyn_cast<ConstantInt>(len);
    auto length = lenint ? lenint->getZExtValue() : 1;
    for (auto &pt: srcreg->pointsto) {
        auto &fmap = pt.target->fieldmap;
        auto baseoff = pt.dstoff;
        auto end = fmap.lower_bound(baseoff + length);
        for (auto it = fmap.lower_bound(baseoff); it != end; ++it) {
            auto offset = it->first - baseoff;
            auto field = &(it->second);
            if (hasPointsTo(field))
                tmp.push_back(std::make_pair(offset, field));
        }
    }
    // transfer collected fields
    if (tmp.size()) {
        // errs() << I << "\n";
        for (auto &pt: dstreg->pointsto) {
            for (auto &fp: tmp) {
                auto offset = pt.dstoff + fp.first;
                auto field = pt.target->getFieldObj(offset);
                field->mergePointsTo(fp.second, &I);
            }
        }
    }
}


void AliasAnalysisVisitor::visitReturnInst(ReturnInst &I) {
    auto retval = I.getReturnValue();
    if (!retval) return;
    currCtx->retval.insert(retval);
}


void AliasAnalysisVisitor::visitLibFunctions(CallInst &I, Function *func) {
    // TODO: realloc should create new object if 1st arg has no pointsto
    static const char* copy1starg[] = {
        "realloc",
        "strcpy", "strncpy",
        "strcat", "strncat",
        "strchr", "strrchr",
    };
    // DEBUG_CALLINST(dbgs() << "Function with no definition: "
                          // << func->getName() << "\n");
    for (auto sample: copy1starg) {
        if (func->getName().equals(sample)) {
            // retval must alias with 1st arg
            auto arg = I.getArgOperand(0);
            auto argreg = currCtx->findOpReg(arg);
            if (hasPointsTo(argreg)) {
                auto dstreg = currCtx->getDestReg(&I);
                dstreg->mergePointsTo(argreg, &I);
            }
            return;
        }
    }

    // default
    if (I.getType()->isPointerTy()) {
        // DEBUG_LOADSTOR(dbgs() << "CreateRegMemPair: " << I << "\n");
        currCtx->createRegMemPair(&I);
    }
}


bool AliasAnalysisVisitor::visitCallInst(CallInst &I, Function *targetFunction) {
    if (targetFunction->isDeclaration()) {
        visitLibFunctions(I, targetFunction);
        return false;
    }
    return true;
}


void AliasAnalysisVisitor::setupChildContext(CallInst &I, AliasTaintContext *parentContext) {
    for (auto &arg: currCtx->func->args()) {
        auto operand = I.getArgOperand(arg.getArgNo());
        auto srcreg = parentContext->findOpReg(operand);
        // DEBUG_LOADSTOR(dbgs() << "setupChildContext: " << arg.getArgNo() << " " << hasPointsTo(srcreg) << "\n");
        if (hasPointsTo(srcreg)) {
            auto dstreg = currCtx->getDestReg(&arg);
            dstreg->mergePointsTo(srcreg, nullptr);
        }
    }
}


void AliasAnalysisVisitor::stitchChildContext(CallInst &I, AliasTaintContext *childContext) {
    RegObject *dstreg = nullptr;
    for (auto val: childContext->retval) {
        auto srcreg = childContext->findOpReg(val);
        if (hasPointsTo(srcreg)) {
            if (!dstreg) dstreg = currCtx->getDestReg(&I);
            // dstreg->mergePointsTo(srcreg, &I);
            for (auto &item: srcreg->pointsto) {
                if (!item.target->fake) {
                    auto tmp = item;
                    tmp.propagator = &I;
                    dstreg->pointsto.insert(tmp);
                }
            }
        }
    }
}
