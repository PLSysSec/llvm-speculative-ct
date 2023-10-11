#include "Utils.h"
#include <algorithm>
#include <llvm/ADT/SCCIterator.h>
#include <llvm/Analysis/CallGraph.h>
#include <llvm/IR/CFG.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DerivedTypes.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Linker/Linker.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include <llvm/Transforms/Utils/Cloning.h>
#include <llvm/Transforms/Utils/ValueMapper.h>
#include <queue>
#include <set>
#include <vector>

using namespace llvm;

static void splitConstExpr(Instruction *inst) {
  size_t idx = 0;
  if (auto phi = dyn_cast<PHINode>(inst)) {
    for (auto &use: phi->incoming_values()) {
      if (auto expr = dyn_cast<ConstantExpr>(use.get())) {
        auto newinst = expr->getAsInstruction();
        auto block = phi->getIncomingBlock(use);
        newinst->insertBefore(block->getTerminator());
        phi->setIncomingValue(idx, newinst);
        splitConstExpr(newinst);
      }
      idx++;
    }
  } else {
    for (auto &use: inst->operands()) {
      if (auto expr = dyn_cast<ConstantExpr>(use.get())) {
        auto newinst = expr->getAsInstruction();
        newinst->insertBefore(inst);
        inst->setOperand(idx, newinst);
        splitConstExpr(newinst);
      }
      idx++;
    }
  }
}

void splitConstExpr(Module &M) {
  // care: will this invalidate iterators?
  for (Function &F: M)
    for (BasicBlock &bbl: F)
      for (Instruction &inst: bbl)
        splitConstExpr(&inst);
}

// SCC utilities

void getSCCTraversalOrder(
        Function &F,
        std::vector<std::vector<BasicBlock*> > &bbTraversalList) {
    if (F.isDeclaration()) return;
    for (auto I = scc_begin(&F), IE = scc_end(&F); I != IE; ++I) {
        const std::vector<BasicBlock*> &constvec = *I;
        std::vector<BasicBlock*> currSCC(constvec.rbegin(), constvec.rend());
        bbTraversalList.push_back(std::move(currSCC));
    }
    std::reverse(bbTraversalList.begin(), bbTraversalList.end());
}


size_t getNumTimesToAnalyze(std::vector<BasicBlock*> &currSCC) {
    /***
     * get number of times all the loop basicblocks should be analyzed.
     *  This is same as the longest use-def chain in the provided
     *  strongly connected component.
     *
     *  Why is this needed?
     *  This is needed because we want to ensure that all the
     *  information inside the loops have been processed.
     */

    std::set<BasicBlock*> globalvisited;
    size_t numToAnalyze = 1;

    for (auto currBBMain: currSCC) {
        // if never visited: BFS on currBBMain
        if (!globalvisited.count(currBBMain)) {
            std::queue<BasicBlock*> queue;
            std::set<BasicBlock*> localvisited;
            queue.push(currBBMain);
            localvisited.insert(currBBMain);

            while (!queue.empty()) {
                auto currBB = queue.front(); queue.pop();

                for (auto &currIns: *currBB) {
                    for(auto &use: currIns.operands()) {
                        if (auto useIns = dyn_cast<Instruction>(use.get())) {
                            auto useBB = useIns->getParent();
                            auto it = std::find(
                                currSCC.begin(), currSCC.end(), useBB);
                            // if useBB in currSCC
                            if (it != currSCC.end()) {
                                // if useBB not in localvisited
                                if (localvisited.insert(useBB).second)
                                    queue.push(useBB);
                            }
                        }
                    }
                }
            }

            numToAnalyze = std::max(numToAnalyze, localvisited.size());
            globalvisited.insert(localvisited.begin(), localvisited.end());
        }
    }

    return numToAnalyze;
}


// Parser utilities


static size_t getGEPOffset(Type* &currtype, User &I, const DataLayout &dl) {
    size_t offset = 0;
    for (auto it = I.op_begin() + 2; it != I.op_end(); ++it) {
        if (currtype->isArrayTy()) {
            currtype = currtype->getArrayElementType();
        } else if (auto stype = dyn_cast<StructType>(currtype)) {
            auto idxint = extractConstantInt(it->get()).first;
            auto sl = dl.getStructLayout(stype);
            offset += sl->getElementOffset(idxint);
            currtype = stype->getElementType(idxint);
        } else {
            assert(false);
        }
    }
    return offset;
}


static size_t getGEPOffset(Type* &currtype, size_t rawoff, const DataLayout &dl) {
    size_t offset = 0;
    while (rawoff) {
        if (currtype->isArrayTy()) {
            currtype = currtype->getArrayElementType();
            auto elemsize = dl.getTypeAllocSize(currtype);
            rawoff %= elemsize;
        } else if (auto stype = dyn_cast<StructType>(currtype)) {
            auto sl = dl.getStructLayout(stype);
            auto elem = sl->getElementContainingOffset(rawoff);
            auto base = sl->getElementOffset(elem);
            currtype = stype->getElementType(elem);
            offset += base;
            rawoff -= base;
        } else {
            assert(false);
        }
    }
    return offset;
}


size_t getGEPOffset(GetElementPtrInst &I, const DataLayout &dl) {
    auto currtype = I.getSourceElementType();
    auto offset = getGEPOffset(currtype, I, dl);
    assert(currtype == I.getResultElementType());
    return offset;
}


size_t getGEPOffset(ConstantExpr *cexpr, const DataLayout &dl, LLVMContext &ctx) {
    auto target = cexpr->getOperand(0);
    auto stripped = target->stripPointerCasts();
    auto currtype = stripped->getType()->getPointerElementType();
    if (target == stripped) {
        // normal GEP
        auto dstoff = getGEPOffset(currtype, *cexpr, dl);
        assert(currtype == cexpr->getType()->getPointerElementType());
        return dstoff;
    }
    // i8 GEP: (gep (cast to i8*) 0, rawoff)
    assert(cexpr->getNumOperands() == 2
        && target->getType() == Type::getInt8PtrTy(ctx));
    auto rawoff = extractConstantInt(cexpr->getOperand(1)).first;
    auto offset = getGEPOffset(currtype, rawoff, dl);
    // DEBUG_GLOBOBJ(dbgs() << "i8 GEP: " << rawoff << " -> "
    //                      << offset << " " << stripped->getName() << "\n");
    return offset;
}


void InitializerWalker::scan(Constant* init, size_t off) {
    assert(!isa<ConstantVector>(init));
    if (auto sobj = dyn_cast<ConstantStruct>(init)) {
        auto slayout = layout.getStructLayout(sobj->getType());
        Constant *curr = sobj->getAggregateElement(0U);
        for (unsigned i = 0; curr; curr = sobj->getAggregateElement(++i)) {
            scan(curr, off + slayout->getElementOffset(i));
        }
    } else if (isa<ConstantArray>(init)) {
        Constant *curr = init->getAggregateElement(0U);
        for (unsigned i = 0; curr; curr = init->getAggregateElement(++i)) {
            scan(curr, off);
        }
    } else {
        handleNonAgg(init, off);
    }
}


void InitializerWalker::handleNonAgg(Constant* init, size_t srcoff) {
    // assert(!isa<GlobalIndirectSymbol>(init)); // TODO(MATT): what?
    if (isa<ConstantData>(init)) return;
    // simple case: globalobject
    auto stripped = init->stripPointerCasts();
    if (auto obj = dyn_cast<GlobalObject>(stripped)) {
        results.push_back(GlobalPointsTo(obj, srcoff, 0));
        return;
    }
    // then maybe gep?
    auto cexpr = dyn_cast<ConstantExpr>(stripped);
    if (cexpr->getOpcode() == Instruction::GetElementPtr) {
        auto target = cexpr->getOperand(0)->stripPointerCasts();
        if (auto obj = dyn_cast<GlobalObject>(target)) {
            auto dstoff = getGEPOffset(cexpr, layout, ctx);
            results.push_back(GlobalPointsTo(obj, srcoff, dstoff));
            return;
        }
    }
    // then ???
    // errs() << *cexpr << "\n";
    assert(false);
}


// Transform utilities


void initValueUid(Module &M, std::map<Value *, std::size_t> &valueUidMap) {
	std::size_t cnt = 0xdeadbeef00000000;
	for (auto &F : M) {
		valueUidMap[&F] = cnt;
		// dbgs() << &F << "\n";
		cnt++;
		for (auto &BB : F) {
			valueUidMap[&BB] = cnt;
			// dbgs() << "  " << &BB << "\n";
			cnt++;
			for (auto &II : BB) {
				valueUidMap[&II] = cnt;
				// dbgs() << "    " << &II << " ";
				cnt++;
			}
		}
	}
}


void insertWRPKRU(Module &M, Instruction *I, int perm_val, Value *dep) {
    // 0 : ALLOW
    // 1 : DISABLE_READ
    // 3 : DISABLE_ACCESS
    assert(perm_val == 0 || perm_val == 1 || perm_val == 3);

    // get Value
    int pkey = 1;
    LLVMContext &ctx = M.getContext();
    Type *voidty = Type::getVoidTy(ctx);
    Type *int32ty = Type::getInt32Ty(ctx);
    Value *zero = ConstantInt::get(int32ty, 0);
    Value *perm = ConstantInt::get(int32ty, perm_val << (2 * pkey));

    // build IR
    IRBuilder<> builder(I);
    if (dep && (!dep->getType()->isVoidTy() || isa<StoreInst>(dep))) {
        // explict dependence bwtween wrpkru and sandboxed inst
        auto SI = dyn_cast<StoreInst>(dep);
        if (SI) dep = SI->getPointerOperand();
        // dbgs() << *dep->getType() << "\n";
        // dbgs() << *dep << "\n";
        if (dep->getType()->isPointerTy())
            dep = builder.CreatePtrToInt(dep, int32ty);
        else
            dep = builder.CreateIntCast(dep, int32ty, true);
        // auto asmtype = TypeBuilder<void(int32_t, int32_t, int32_t, int32_t), false>::get(ctx);
        auto asmtype = FunctionType::get(voidty, {int32ty, int32ty, int32ty, int32ty}, false);
        auto asminst = InlineAsm::get(asmtype, "wrpkru", "{ax},{cx},{dx},{bx}", true);
#ifndef WRPKRU_OFF
        builder.CreateCall(asminst, SmallVector<Value*, 3>{perm, zero, zero, dep});
#endif
    } else {
        // auto asmtype = TypeBuilder<void(int32_t, int32_t, int32_t), false>::get(ctx);
        auto asmtype = FunctionType::get(voidty, {int32ty, int32ty, int32ty}, false);
        auto asminst = InlineAsm::get(asmtype, "wrpkru", "{ax},{cx},{dx}", true);
#ifndef WRPKRU_OFF
        builder.CreateCall(asminst, SmallVector<Value*, 3>{perm, zero, zero});
#endif
    }
}


CallInst* replaceAllocaWithMPKMalloc(Module &M, AllocaInst *I) {
    // get function
    auto &ctx = M.getContext();
    auto int8ptrty = Type::getInt8PtrTy(ctx);
    auto int64ty = Type::getInt64Ty(ctx);
    // auto malloctype = TypeBuilder<int8_t*(int64_t), false>::get(ctx);
    auto malloctype = FunctionType::get(int8ptrty, {int64ty}, false);
    auto mallocfunc = M.getOrInsertFunction("m_malloc", malloctype);
    // get size
    auto &dl = M.getDataLayout();
    auto allocasize = dl.getTypeAllocSize(I->getAllocatedType());
    auto argsize = ConstantInt::get(int64ty, allocasize);
    // create callinst
    Value* args[] = { argsize };
    auto callinst = CallInst::Create(mallocfunc, args, "", I);
    // create bitcast
    auto castinst = CastInst::CreatePointerCast(callinst, I->getType());
    ReplaceInstWithInst(I, castinst);
    return callinst;
}


CallInst* insertMPKFree(Module &M, Value *target, Instruction *insertbefore) {
    auto &ctx = M.getContext();
    auto int8ptrty = Type::getInt8PtrTy(ctx);
    auto voidty = Type::getVoidTy(ctx);
    // auto freetype = TypeBuilder<void(int8_t*), false>::get(M.getContext());
    auto freetype = FunctionType::get(voidty, {int8ptrty}, false);
    // auto freefunc = M.getOrInsertFunction("mpk_free", freetype);
    auto freefunc = M.getOrInsertFunction("m_free", freetype);
    Value* args[] = { target };
    return CallInst::Create(freefunc, args, "", insertbefore);
}


CallInst* insertMemset(Module &M, Value *target, Instruction *insertbefore) {
    auto I = dyn_cast<AllocaInst>(target);
    if (!I) return nullptr;
    auto &dl = M.getDataLayout();
    auto allocasize = dl.getTypeAllocSize(I->getAllocatedType());
    Type *Int8Ty = Type::getInt8Ty(M.getContext());
    auto IntZero = ConstantInt::get(Int8Ty, 0);
    IRBuilder<> builder(insertbefore);
    CallInst *Set0CI = builder.CreateMemSet(
            I, IntZero, allocasize, MaybeAlign(I->getAlign()));
    return Set0CI;
}


ExpandFuncPtr::ExpandFuncPtr(CallInst *inst) {
    originst = inst;
    funcptr = inst->getCalledOperand();
    fptype = inst->getFunctionType();
    F = inst->getFunction();
    M = inst->getModule();
    for (auto &use: inst->args()) {
        args.push_back(use.get());
    }
}


void ExpandFuncPtr::splitBlock() {
    auto origblock = originst->getParent();
    tailblock = SplitBlock(origblock, originst);
    curblock = BasicBlock::Create(M->getContext(), "funcptr", F);
    auto firstbr = dyn_cast<BranchInst>(origblock->getTerminator());
    firstbr->setSuccessor(0, curblock);
}


CallInst* ExpandFuncPtr::addTarget(Function *target) {
    // create cond block
    IRBuilder<> condbuilder(curblock);
    Value *fp2 = funcptr;
    if (fp2->getType() != target->getType())
        fp2 = condbuilder.CreateBitCast(fp2, target->getType());
    auto cond = condbuilder.CreateICmpEQ(fp2, target);
    auto nextcur = BasicBlock::Create(M->getContext(), "funcptr", F);
    auto callblock = BasicBlock::Create(M->getContext(), "funcptr.call", F);
    condbuilder.CreateCondBr(cond, callblock, nextcur);
    // create call block
    IRBuilder<> callbuilder(callblock);
    std::vector<Value*> args2(args);
    auto functype = target->getFunctionType();
    for (size_t i = 0; i < args2.size(); i++) {
        auto dsttype = functype->getParamType(i);
        if (args2[i]->getType() != dsttype)
            args2[i] = callbuilder.CreateBitCast(args2[i], dsttype);
    }
    auto callinst = callbuilder.CreateCall(functype, target, args2);
    Instruction *ret = callinst;
    if (ret->getType() != fptype->getReturnType())
        ret = dyn_cast<Instruction>(
            callbuilder.CreateBitCast(ret, fptype->getReturnType()));
    assert(ret);
    retvals.push_back(ret);
    callbuilder.CreateBr(tailblock);
    // update curblock
    curblock = nextcur;
    return callinst;
}


CallInst* ExpandFuncPtr::addFallback() {
    IRBuilder<> lastbuilder(curblock);
    auto ret = lastbuilder.CreateCall(fptype, funcptr, args);
    lastbuilder.CreateBr(tailblock);
    retvals.push_back(ret);
    return ret;
}


PHINode* ExpandFuncPtr::addPHINode() {
    auto returnty = originst->getType();
    if (returnty->isVoidTy()) return nullptr;
    auto phi = PHINode::Create(returnty, retvals.size());
    for (auto val: retvals) {
        phi->addIncoming(val, val->getParent());
    }
    ReplaceInstWithInst(originst, phi);
    return phi;
}
