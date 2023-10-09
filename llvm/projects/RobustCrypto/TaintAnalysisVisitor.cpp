#include "TaintAnalysisVisitor.h"
#include "Utils.h"

void TaintAnalysisVisitor::visitCastInst(CastInst &I) {
    if (I.stripPointerCasts() != &I) return;
    auto src = I.getOperand(0);
    auto srcreg = currCtx->findOpReg(src);
    if (hasTaint(srcreg)) {
        auto dstreg = currCtx->getDestReg(&I);
        dstreg->flowTaint(srcreg, &I);
    }
}

void TaintAnalysisVisitor::visitBinaryOperator(BinaryOperator &I) {
    auto lhs = I.getOperand(0);
    auto rhs = I.getOperand(1);
    auto lreg = currCtx->findOpReg(lhs);
    auto rreg = currCtx->findOpReg(rhs);
    auto dstreg = currCtx->getDestReg(&I);
    if (hasTaint(lreg)) dstreg->flowTaint(lreg, &I);
    if (hasTaint(rreg)) dstreg->flowTaint(rreg, &I);
}

void TaintAnalysisVisitor::visitPHINode(PHINode &I) {
    RegObject *dst = nullptr;
    for (auto &use : I.incoming_values()) {
        auto reg = currCtx->findOpReg(use.get());
        if (hasTaint(reg)) {
            if (!dst) dst = currCtx->getDestReg(&I);
            dst->flowTaint(reg, &I);
        }
    }
}

void TaintAnalysisVisitor::visitSelectInst(SelectInst &I) {
    auto lhs = I.getTrueValue();
    auto rhs = I.getFalseValue();
    auto lreg = currCtx->findOpReg(lhs);
    auto rreg = currCtx->findOpReg(rhs);
    auto dstreg = currCtx->getDestReg(&I);
    if (hasTaint(lreg)) dstreg->flowTaint(lreg, &I);
    if (hasTaint(rreg)) dstreg->flowTaint(rreg, &I);
}

void TaintAnalysisVisitor::visitGetElementPtrInst(GetElementPtrInst &I) {
    if (I.stripPointerCasts() != &I) return;
    auto val = I.getPointerOperand();
    auto srcreg = currCtx->findOpReg(val);
    if (hasTaint(srcreg)) {
        auto dstreg = currCtx->getDestReg(&I);
        dstreg->flowTaint(srcreg, &I);
    }
}

void TaintAnalysisVisitor::visitLoadInst(LoadInst &I) {
    auto src = I.getPointerOperand();
    auto srcreg = currCtx->findOpReg(src);
    if (hasPointsTo(srcreg)) {
        RegObject *dstreg = nullptr;
        for (auto &pt : srcreg->pointsto) {
            auto fieldobj = pt.target->findFieldObj(pt.dstoff);
            if (hasTaint(fieldobj)) {
                if (!dstreg) dstreg = currCtx->getDestReg(&I);
                dstreg->flowTaint(fieldobj, &I);
            }
        }
    }
}

void TaintAnalysisVisitor::visitStoreInst(StoreInst &I) {
    // where to store
    auto dstptr = I.getPointerOperand();
    auto dstreg = currCtx->findOpReg(dstptr);
    if (!hasPointsTo(dstreg)) {
        assert(false);
        return;
    }
    // what to store
    auto srcval = I.getValueOperand();
    auto srcreg = currCtx->findOpReg(srcval);
    if (!hasTaint(srcreg)) return;
    // action
    for (auto &pt : dstreg->pointsto) {
        auto fieldobj = pt.target->getFieldObj(pt.dstoff);
        fieldobj->flowTaint(srcreg, &I);
        pt.target->updateTaintByField(pt.dstoff, fieldobj);
    }
}

void TaintAnalysisVisitor::visitMemTransferInst(MemTransferInst &I) {
    auto len = I.getOperand(2);
    auto src = I.getOperand(1);
    auto dst = I.getOperand(0);
    auto srcreg = currCtx->findOpReg(src);
    auto dstreg = currCtx->findOpReg(dst);
    if (!hasPointsTo(srcreg) || !hasPointsTo(dstreg)) return;
    // collect fields to transfer
    std::vector<std::pair<FieldIdTy, FieldObject *>> tmp;
    auto lenint = dyn_cast<ConstantInt>(len);
    auto length = lenint ? lenint->getZExtValue() : 1;
    for (auto &pt : srcreg->pointsto) {
        auto &fmap = pt.target->fieldmap;
        auto baseoff = pt.dstoff;
        auto end = fmap.lower_bound(baseoff + length);
        for (auto it = fmap.lower_bound(baseoff); it != end; ++it) {
            auto offset = it->first - baseoff;
            auto field = &(it->second);
            if (hasTaint(field)) tmp.push_back(std::make_pair(offset, field));
        }
    }
    // transfer collected fields
    if (tmp.size()) {
        // errs() << I << "\n";
        for (auto &pt : dstreg->pointsto) {
            for (auto &fp : tmp) {
                auto offset = pt.dstoff + fp.first;
                auto field = pt.target->getFieldObj(offset);
                field->flowTaint(fp.second, &I);
                pt.target->updateTaintByField(offset, field);
            }
        }
    }
}

void TaintAnalysisVisitor::visitReturnInst(ReturnInst &I) {
    auto retval = I.getReturnValue();
    if (retval) currCtx->retval.insert(retval);
}

void TaintAnalysisVisitor::visitLibFunctions(CallInst &I, Function *func) {
    static const char* copy1to0ret[] = {
        "strcpy", "strncpy",
        "strcat", "strncat",
    };
    static const char* copy0toret[] = {
        "realloc",
        "strchr", "strrchr",
    };

    auto srcpos = -1;

    for (auto sample: copy1to0ret) {
        if (func->getName().equals(sample)) {
            srcpos = 1;
        }
    }
    for (auto sample: copy0toret) {
        if (func->getName().equals(sample)) {
            srcpos = 0;
        }
    }

    if (srcpos == -1) return;

    // fetch src
    auto srcreg = currCtx->findOpReg(I.getOperand(srcpos));
    if (!hasPointsTo(srcreg)) return;

    std::vector<FieldObject *> tmp;
    for (auto &pt : srcreg->pointsto) {
        auto fieldobj = pt.target->getFieldObj(0);
        if (hasTaint(fieldobj))
            tmp.push_back(fieldobj);
    }

    if (tmp.size() == 0) return;

    auto dstreg = currCtx->findOpReg(&I);
    // transfer collected fields
    if (hasPointsTo(dstreg)) {
        for (auto &pt : dstreg->pointsto) {
            for (auto &fp : tmp) {
                auto field = pt.target->getFieldObj(0);
                field->flowTaint(fp, &I);
                pt.target->updateTaintByField(0, field);
            }
        }
    }

    if (srcpos == 1) {
        dstreg = currCtx->findOpReg(I.getOperand(0));
        if (hasPointsTo(dstreg)) {
            for (auto &pt : dstreg->pointsto) {
                for (auto &fp : tmp) {
                    auto field = pt.target->getFieldObj(0);
                    field->flowTaint(fp, &I);
                    pt.target->updateTaintByField(0, field);
                }
            }
        }
    }
}

bool TaintAnalysisVisitor::visitCallInst(CallInst &I, Function *targetFunction) {
    if (targetFunction->isDeclaration()) {
        if (targetFunction->getName().equals("__robust_crypto_secret")) {
            auto val = I.getArgOperand(1);
            auto reg = currCtx->findOpReg(val);
            if (reg) {
                for (auto &pt : reg->pointsto) {
                    auto field = pt.target->getFieldObj(pt.dstoff);
                    field->setTaint(&I);
                    pt.target->updateTaintByField(pt.dstoff, field);
                }
            } else {
                // dbgs() << "SECRET: Didn't find OpReg for the instruction: " << I << "\n";
            }
        }
        else if (targetFunction->getName().equals("__robust_crypto_declassify")) {
            auto val = I.getArgOperand(1);
            auto reg = currCtx->findOpReg(val);
            if (reg) {
                for (auto &pt : reg->pointsto) {
                    auto field = pt.target->getFieldObj(pt.dstoff);
                    field->setDeclassify(&I);
                    pt.target->updateTaintByField(pt.dstoff, field);
                }
            } else {
                // dbgs() << "DECLASSIFY: Didn't find OpReg for the instruction: " << I << "\n";
            }

        }
        else {
            visitLibFunctions(I, targetFunction);
        }
        return false;
    }
    return true;
}

void TaintAnalysisVisitor::setupChildContext(CallInst &I, AliasTaintContext *parentContext) {
    for (auto &arg : currCtx->func->args()) {
        auto operand = I.getArgOperand(arg.getArgNo());
        auto srcreg = parentContext->findOpReg(operand);
        if (hasTaint(srcreg)) {
            auto dstreg = currCtx->getDestReg(&arg);
            dstreg->flowTaint(srcreg, nullptr);
        }
    }
}

void TaintAnalysisVisitor::stitchChildContext(CallInst &I, AliasTaintContext *childContext) {
    RegObject *dstreg = nullptr;
    for (auto val : childContext->retval) {
        auto srcreg = childContext->findOpReg(val);
        if (hasTaint(srcreg)) {
            if (!dstreg) dstreg = currCtx->getDestReg(&I);
            dstreg->flowTaint(srcreg, &I);
        }
    }
    // for (auto &mem : childContext->localobjects.memmap) {
    //     auto memobj = mem.second.get();
    //     //TODO: FIX THIS later
    //     // if (memobj->tainted) {
    //     //     dbgs() << "Tainted: " << *(memobj->represented) << "\t" << *(memobj->tainter) << "\n";
    //     // }
    // }
    // dbgs() << "RegObjects: " << childContext->localobjects.memmap.size() << "\n";
    // dbgs() << "AliasObjects: " << childContext->localobjects.regmap.size() << "\n";
}
