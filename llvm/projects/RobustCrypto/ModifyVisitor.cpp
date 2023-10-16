#include "ModifyVisitor.h"
#include "GlobalVisitor.h"

#define LOOPFACTOR 10
#define CALLFACTOR 30

#define IGNORESTACK false

ModifiedFunctionList ModifyCallbackVisitor::newfunctions;
std::set<Function *> ModifyCallbackVisitor::analyzed_functions;

void ModifyCallbackVisitor::visitAllocaInst(AllocaInst &I) {
    if (currCtx->inside_loop) return;
    if (!I.isStaticAlloca() || !I.getAllocatedType()->isAggregateType()) return;
    auto inst =
        funcmod()->getInstMod(I, InstModType::AllocaInst, currCtx->lastloopiter, currCtx->loopidx);

    inst->ignorepriv = true;

    auto reg = currCtx->getDestReg(&I);
    if (checkPointsToTaint(reg) && (I.getParent() == &(currCtx->func->getEntryBlock()))) {
        // dbgs() << "MODIFY: tainting this instruction " << I << " \n";
        funcmod()->setTaint(inst);
    }
    // sanity check
    assert(!(checkPointsToTaint(reg) && checkPointsToSink(reg)));
}

void ModifyCallbackVisitor::visitLoadInst(LoadInst &I) {
    if (currCtx->inside_loop) return;
    auto inst =
        funcmod()->getInstMod(I, InstModType::MPKWrap, currCtx->lastloopiter, currCtx->loopidx);

    auto src = I.getPointerOperand();
    auto srcreg = currCtx->findOpReg(src);
    if (checkPointsToTaint(srcreg, IGNORESTACK)) {
        funcmod()->setTaint(inst);
        // int lineno = DbgInfo::getSrcLine(&I, currCtx->globals);
        // if (lineno >= 0) {
        //     std::string filename = DbgInfo::getSrcFileName(&I, currCtx->globals);
        //     DEBUG_MODIFY(dbgs() << formatv("KeyTaint: {0},{1},{2}\n", filename, lineno,
        //     *srcreg->represented));
        // } else {
        //     DEBUG_MODIFY(dbgs() << "KeyTaint: Cannot get lineno\n");
        // }
    }
    if (checkPointsToSink(srcreg, IGNORESTACK)) {
        // int lineno = DbgInfo::getSrcLine(&I, currCtx->globals);
        // if (lineno >= 0) {
        //     std::string filename = DbgInfo::getSrcFileName(&I, currCtx->globals);
        //     DEBUG_MODIFY(dbgs() << formatv("Declassify: {0},{1},{2}\n", filename, lineno,
        //     *srcreg->represented));
        // } else {
        //     DEBUG_MODIFY(dbgs() << "Declassify: Cannot get lineno\n");
        // }
    }
    // sanity check
    assert (!(checkPointsToTaint(srcreg, IGNORESTACK) && checkPointsToSink(srcreg, IGNORESTACK)));
}

void ModifyCallbackVisitor::visitStoreInst(StoreInst &I) {
    if (currCtx->inside_loop) return;
    auto inst =
        funcmod()->getInstMod(I, InstModType::MPKWrap, currCtx->lastloopiter, currCtx->loopidx);

    auto dst = I.getPointerOperand();
    auto dstreg = currCtx->findOpReg(dst);
    if (checkPointsToTaint(dstreg, IGNORESTACK)) {
        funcmod()->setTaint(inst);
        // int lineno = DbgInfo::getSrcLine(&I, currCtx->globals);
        // if (lineno >= 0) {
        //     std::string filename = DbgInfo::getSrcFileName(&I, currCtx->globals);
        //     DEBUG_MODIFY(dbgs() << formatv("KeyTaint: {0},{1},{2}\n", filename, lineno,
        //     *dstreg->represented));
        // } else {
        //     DEBUG_MODIFY(dbgs() << "KeyTaint: Cannot get lineno\n");
        // }
    }
    if (checkPointsToSink(dstreg, IGNORESTACK)) {
        // int lineno = DbgInfo::getSrcLine(&I, currCtx->globals);
        // if (lineno >= 0) {
        //     std::string filename = DbgInfo::getSrcFileName(&I, currCtx->globals);
        //     DEBUG_MODIFY(dbgs() << formatv("Declassify: {0},{1},{2}\n", filename, lineno,
        //     *dstreg->represented));
        // } else {
        //     DEBUG_MODIFY(dbgs() << "Declassify: Cannot get lineno\n");
        // }
    }
    // sanity check
    assert (!(checkPointsToTaint(dstreg, IGNORESTACK) && checkPointsToSink(dstreg, IGNORESTACK)));
}

void ModifyCallbackVisitor::visitMemTransferInst(MemTransferInst &I) {
    if (currCtx->inside_loop) return;
    auto inst =
        funcmod()->getInstMod(I, InstModType::MPKWrap, currCtx->lastloopiter, currCtx->loopidx);

    auto src = I.getOperand(1);
    auto dst = I.getOperand(0);
    auto srcreg = currCtx->findOpReg(src);
    auto dstreg = currCtx->findOpReg(dst);
    if (checkPointsToTaint(srcreg, IGNORESTACK) || checkPointsToTaint(dstreg, IGNORESTACK)) {
        funcmod()->setTaint(inst);
    }
    // sanity check
    assert (!(checkPointsToTaint(srcreg, IGNORESTACK) && checkPointsToSink(srcreg, IGNORESTACK)));
    assert (!(checkPointsToTaint(dstreg, IGNORESTACK) && checkPointsToSink(dstreg, IGNORESTACK)));
}

void ModifyCallbackVisitor::visitMemSetInst(MemSetInst &I) {
    if (currCtx->inside_loop) return;
    auto inst =
        funcmod()->getInstMod(I, InstModType::MPKWrap, currCtx->lastloopiter, currCtx->loopidx);

    auto dst = I.getOperand(0);
    auto dstreg = currCtx->findOpReg(dst);
    if (checkPointsToTaint(dstreg, IGNORESTACK)) {
        funcmod()->setTaint(inst);
    }
    assert(!(checkPointsToTaint(dstreg, IGNORESTACK) && checkPointsToSink(dstreg, IGNORESTACK)));
}

bool ModifyCallbackVisitor::visitCallInst(CallInst &I, Function *func) {
    if (currCtx->inside_loop) return false;

    // if (Rules::checkBlacklist(func)) {
    //     auto inst =
    //         funcmod()->getInstMod(I, InstModType::MPKWrap, currCtx->lastloopiter, currCtx->loopidx);
    //     visitLibFunction(I, func, inst);
    //     return false;
    // }
    if (currCtx->checkRecursive(I)) {
        auto inst =
            funcmod()->getInstMod(I, InstModType::MPKWrap, currCtx->lastloopiter, currCtx->loopidx);
        // dbgs() << "RECURSIVE: setting funcmod to be tainted.... not sure why :/ \n";
        funcmod()->setTaint(inst);
        return false;
    }
    if (I.getCalledFunction()) {
        if (func->isDeclaration()) {
            visitLibFunction(I, func, nullptr);
        } else
            funcmod()->getInstMod(I, InstModType::FuncDirect, currCtx->lastloopiter,
                                  currCtx->loopidx);
        // TODO: check what exactly the above statements achieve
    } else {
        auto inst =
            funcmod()->getInstMod(I, InstModType::FuncPtr, currCtx->lastloopiter, currCtx->loopidx);
        if (func->isDeclaration()) {
            visitLibFunction(I, func, inst);
        }
    }
    return !func->isDeclaration();
}

void ModifyCallbackVisitor::setupChildContext(CallInst &I, AliasTaintContext *child) {
    // Function *F = currCtx->func;
    // if (Globals::DirFuncs.size() && (Globals::DirFuncs.find(F) != Globals::DirFuncs.end()))
    //     currCtx->isExportFn = true;
}

void ModifyCallbackVisitor::stitchChildContext(CallInst &I, AliasTaintContext *child) {
    analyzed_functions.insert(child->func);
    if (!child->funcmod.anytainted) return;
    child->funcmod.calledbyExportFn = currCtx->isExportFn;
    child->funcmod.isExportFn = child->isExportFn;
    auto funcobj = newfunctions.tryinsert(child);
    auto instmod = funcmod()->getInstMod(I);
    funcmod()->addCallTarget(instmod, child->func, funcobj->ctxhash);
}

void ModifyCallbackVisitor::visitLibFunction(CallInst &I, Function *func, InstMod *instmod) {
    if (func->getName().equals("malloc") || func->getName().equals("realloc")) {
        if (!instmod)
            instmod = funcmod()->getInstMod(I, InstModType::MemFunc, currCtx->lastloopiter,
                                            currCtx->loopidx);
        auto reg = currCtx->getDestReg(&I);
        if (checkPointsToTaint(reg)) {
            funcmod()->addLibFuncCall(instmod, func, InstModType::MemFunc);
        }
        return;
    }
    if (func->getName().equals("free") || func->getName().equals("realloc")) {
        if (!instmod)
            instmod = funcmod()->getInstMod(I, InstModType::MemFunc, currCtx->lastloopiter,
                                            currCtx->loopidx);
        // currCtx->findOpReg(I.getArgOperand(0));
        // TODO: why there is no check if the re is tainted or not???
        funcmod()->addLibFuncCall(instmod, func, InstModType::MemFunc);
        return;
    }

    for (auto &use : I.operands()) {
        auto reg = currCtx->findOpReg(use.get());
        if (reg && checkPointsToTaint(reg, IGNORESTACK)) {
            if (!instmod)
                instmod = funcmod()->getInstMod(I, InstModType::MPKWrap, currCtx->lastloopiter,
                                                currCtx->loopidx);
            funcmod()->addLibFuncCall(instmod, func, InstModType::MPKWrap);
            return;
        }
    }
}

void ModifyCallbackVisitor::visitReturnInst(ReturnInst &I) {
    if (currCtx->inside_loop) return;
    funcmod()->returnlist.push_back(&I);
}

struct FunctionModifyRunner {
    ModifyCallbackVisitor *visitor;
    ModifiedFunction *funcmod;
    static std::set<Instruction *> stats_tainted_insts;

    FunctionModifyRunner(ModifyCallbackVisitor *v, ModifiedFunction *f) : visitor(v), funcmod(f) {}

    template <typename Func>
    void foreach_tainted_instmod(Func func) {
        for (auto &pair : funcmod->fn_map) {
            auto instmod = &(pair.second);
            if (instmod->tainted) func(instmod);
        }
    }

    template <typename Func>
    void foreach_privsensitive_instmod(Func func) {
        for (auto &pair : funcmod->fn_map) {
            auto instmod = &(pair.second);
            if (!instmod->ignorepriv) func(instmod);
        }
    }

    template <typename Func>
    void foreach_instmod(InstModType ty, Func func) {
        for (auto &pair : funcmod->fn_map) {
            auto instmod = &(pair.second);
            if (instmod->type == ty) func(instmod);
        }
    }

    void copyNew() {
        if (!funcmod->isentry) {
            funcmod->vmap.reset(new ValueToValueMapTy());
            funcmod->newfunc = CloneFunction(funcmod->origfunc, *(funcmod->vmap));
            auto newname = funcmod->origfunc->getName().str() + "_" + std::to_string(funcmod->ctxhash);
            funcmod->newfunc->setName(newname);
        }
    }

  void removePragmaFuncs() {
    SmallVector<CallInst*> pragmaCalls;
    foreach_tainted_instmod([&](InstMod *instmod) {
      if (CallInst* callinst = dyn_cast<CallInst>(instmod->inst)) {
        Function *calledfunc = callinst->getCalledFunction();
        if (calledfunc->getName().equals("__robust_crypto_secret") || calledfunc->getName().equals("__robust_crypto_declassify")) {
          pragmaCalls.push_back(callinst);
        }
      }
    });
    for (auto inst : pragmaCalls) {
      funcmod->fn_map.erase(inst);
      inst->eraseFromParent();
    }
  }

    void expandFuncPtr() {
        std::vector<InstMod *> funcptrs;
        foreach_tainted_instmod([&](InstMod *instmod) {
            if (instmod->type == InstModType::FuncPtr) {
                instmod->ignorepriv = true;
                funcptrs.push_back(instmod);
            }
        });
        for (auto instmod1 : funcptrs) {
            auto newinst = funcmod->resolve_inst(instmod1->inst);
            auto callinst = dyn_cast<CallInst>(newinst);
            ExpandFuncPtr expander(callinst);
            expander.splitBlock();
            for (auto &pair : instmod1->calltargets) {
                auto &target = pair.second;
                auto newcall = expander.addTarget(target.func);
                auto instmod2 =
                    funcmod->getInstMod(*newcall, target.type, instmod1->inloop, instmod1->loopidx);
                if (target.type == InstModType::FuncDirect)
                    funcmod->addCallTarget(instmod2, target.func, target.hash);
                else
                    funcmod->setTaint(instmod2);
            }
            auto newcall = expander.addFallback();
            funcmod->getInstMod(*newcall, InstModType::FuncPtr, instmod1->inloop,
                                instmod1->loopidx);
            if (!expander.addPHINode()) {
                callinst->eraseFromParent();
            }
        }
    }

    void substitueCallTarget() {
        foreach_instmod(InstModType::FuncDirect, [&](InstMod *instmod) {
            if (instmod->tainted) {
                auto newinst = funcmod->resolve_inst(instmod->inst);
                auto callinst = dyn_cast<CallInst>(newinst);
                auto &target = instmod->calltargets.begin()->second;
                auto &targetfuncmod =
                  visitor->newfunctions.map.insert_or_assign(std::make_pair(target.func, target.hash), ModifiedFunction(instmod->globals)).first->second;
                callinst->setCalledFunction(targetfuncmod.newfunc);
                instmod->tainted = targetfuncmod.callerprotect;
            } else {
                instmod->ignorepriv = true;
            }
        });
    }

    void replaceAllocs() {
        foreach_tainted_instmod([&](InstMod *instmod) {
            if (instmod->type == InstModType::MemFunc) {
                auto newinst = funcmod->resolve_inst(instmod->inst);
                auto callinst = dyn_cast<CallInst>(newinst);
                Function *calledfunc = callinst->getCalledFunction();
                if (calledfunc->getName().equals("free") || calledfunc->getName().equals("realloc"))
                    return;
                else if (calledfunc->getName().equals("malloc")) {
#ifndef MEMMANAGER_OFF
                    auto functype = calledfunc->getFunctionType();
                    auto funcname = std::string("m_") + calledfunc->getName().str();
                    auto newfunc = visitor->mod.getOrInsertFunction(funcname, functype);
                    callinst->setCalledFunction(dyn_cast<Function>(newfunc.getCallee()));
#endif
                } else {
#ifndef MEMMANAGER_OFF
                    auto functype = calledfunc->getFunctionType();
                    auto funcname = std::string("mpk_") + calledfunc->getName().str();
                    auto newfunc = visitor->mod.getOrInsertFunction(funcname, functype);
                    callinst->setCalledFunction(dyn_cast<Function>(newfunc.getCallee()));
#endif
                }
            } else if (instmod->type == InstModType::AllocaInst) {
#ifndef STACKMEMSET
#ifndef MEMMANAGER_OFF
                auto newinst = funcmod->resolve_inst(instmod->inst);
                auto allocainst = dyn_cast<AllocaInst>(newinst);
                auto newmalloc = replaceAllocaWithMPKMalloc(visitor->mod, allocainst);
                auto mallocmod = funcmod->getInstMod(*newmalloc, InstModType::MPKWrap, false);
                funcmod->setTaint(mallocmod);
                for (auto returninst : funcmod->returnlist) {
                    auto newreturn = funcmod->resolve_inst(returninst);
                    auto newfree = insertMPKFree(visitor->mod, newmalloc, newreturn);
                    auto freemod = funcmod->getInstMod(*newfree, InstModType::MPKWrap, false);
                    funcmod->setTaint(freemod);
                }
#endif
#else
#ifndef MEMMANAGER_OFF
                // DEBUG_MODIFY(dbgs() << "testtest\n");
                auto newinst = funcmod->resolve_inst(instmod->inst);
                auto allocainst = dyn_cast<AllocaInst>(newinst);
                for (auto returninst : funcmod->returnlist) {
                    auto newreturn = funcmod->resolve_inst(returninst);
                    insertMemset(visitor->mod, allocainst, newreturn);
                }
#endif
#endif
            }
        });
    }

    void countTaint() {
        size_t cnt_total = 0, cnt_tainted = 0;
        std::map<int, std::pair<int, int>> loop_map;
        foreach_privsensitive_instmod([&](InstMod *instmod) {
            auto score_pair = std::make_pair(0, 0);
            if (!funcmod->isentry && !funcmod->isExportFn &&
                (dyn_cast<LoadInst>(instmod->inst) || dyn_cast<StoreInst>(instmod->inst) ||
                 dyn_cast<MemTransferInst>(instmod->inst)))
                stats_tainted_insts.insert(instmod->inst);
            if (instmod->type == InstModType::FuncDirect) {
                auto &target = instmod->calltargets.begin()->second;
                auto &targetfuncmod =
                    visitor->newfunctions.map.insert_or_assign(std::make_pair(target.func, target.hash), ModifiedFunction(instmod->globals)).first->second;
                double child_score = (double)targetfuncmod.cnt_tainted / targetfuncmod.cnt_total;
                score_pair.first = CALLFACTOR;
                score_pair.second = CALLFACTOR * child_score;
            } else {
                score_pair.first = 1;
                if (instmod->tainted) score_pair.second = 1;
            }
            if (instmod->inloop) {
                score_pair.first *= LOOPFACTOR;
                score_pair.second *= LOOPFACTOR;
                auto ins = loop_map.emplace(instmod->loopidx, score_pair);
                // DEBUG_MODIFY(dbgs() << formatv("\t\tloop{0} taint: {1}\n",
                // instmod->loopidx, score_pair.second));
                if (!ins.second) {
                    auto &exist_pair = ins.first->second;
                    exist_pair.first += score_pair.first;
                    // if (instmod->tainted)
                    exist_pair.second += score_pair.second;
                }
            }
            cnt_total += score_pair.first;
            cnt_tainted += score_pair.second;
        });
        funcmod->cnt_total = cnt_total;
        funcmod->cnt_tainted = cnt_tainted;
        double score = (double)funcmod->cnt_tainted / funcmod->cnt_total;
        // if (funcmod->newfunc) DEBUG_MODIFY(dbgs() << formatv("\tfunction score: {0:F}\n", score * 100));
        // if (score >= Globals::Threshold) {
        if (score >= 0.5) {
          funcmod->need_callerprotect = true;
          return;
        }
        // check loop score
        for (auto &pair : loop_map) {
            auto &score_pair = pair.second;
            double score = (double)score_pair.second / score_pair.first;
            if (funcmod->newfunc)
                // DEBUG_MODIFY(dbgs() << formatv("\t\tloop{0} score: {1:F} taint: {2}\n", pair.first,
                                               // score * 100, score_pair.second));
            // if (score >= Globals::Threshold) {
            if (score >= 0.5) {
                funcmod->need_callerprotect = true;
                return;
            }
        }
        funcmod->need_callerprotect = false;

        // for (auto &name : Globals::Hotspots) {
        //     if (funcmod->func->getName() == name) {
        //         funcmod->need_callerprotect = true;
        //         DEBUG_MODIFY(dbgs() << "Hotspot : " << funcmod->newfunc->getName());
        //     }
        // }
        // if (funcmod->func->getName() == "xShiftSubst" ||
        //     funcmod->func->getName() == "xrijndaelEncrypt" ||
        //     funcmod->func->getName() == "xrijndaelDecrypt") {
        //     funcmod->need_callerprotect = false;
        // }
        }

    void insertWrpkruInst() {
        if (funcmod->newfunc) {
            // DEBUG_MODIFY(dbgs() << formatv("\tcalledbyExportFn: {0}\n", funcmod->calledbyExportFn));
            // DEBUG_MODIFY(dbgs() << formatv("\tisExportFn: {0}\n", funcmod->isExportFn));
            // DEBUG_MODIFY(
                // dbgs() << formatv("\tneed_callerprotect {0}\n", funcmod->need_callerprotect));
        }
        if (funcmod->isentry || funcmod->isExportFn || !funcmod->need_callerprotect) {
            // if (funcmod->newfunc) DEBUG_MODIFY(dbgs() << "\t*Fine-grained protected\n");
            foreach_privsensitive_instmod([&](InstMod *instmod) {
                if (instmod->tainted) {
                    auto newinst = funcmod->resolve_inst(instmod->inst);
                    insertWRPKRU(visitor->mod, newinst, 0);
                    insertWRPKRU(visitor->mod, newinst->getNextNode(), 3, newinst);
                }
            });
        } else {
            // if (funcmod->newfunc) DEBUG_MODIFY(dbgs() << "\t*Caller protected\n");
            funcmod->callerprotect = true;
            foreach_privsensitive_instmod([&](InstMod *instmod) {
                // func calls must be excluded
                if (!instmod->tainted && instmod->type == InstModType::FuncDirect) {
                    auto newinst = funcmod->resolve_inst(instmod->inst);
                    // insertWRPKRU(visitor->mod, newinst, 3);
                    insertWRPKRU(visitor->mod, newinst->getNextNode(), 0);
                }
            });
        }
    }

    void reportTaint() {
        foreach_tainted_instmod([&](InstMod *instmod) {
            if (instmod->type == InstModType::MPKWrap || instmod->type == InstModType::MemFunc) {
              // DEBUG_MODIFY(dbgs() << "Report " << *instmod->inst << "\n");
              // int lineno = DbgInfo::getSrcLine(instmod->inst, *funcmod->globals);
              // if (lineno >= 0) {
              //   std::string filename =
              //       DbgInfo::getSrcFileName(instmod->inst, *instmod->globals);
              //   (*Globals::TaintReport) << formatv("{0},{1}\n", filename, lineno);
              // } else {
              //   DEBUG_MODIFY(dbgs() << "Cannot get lineno\n");
              // }
            }
        });
    }
};

std::set<Instruction *> FunctionModifyRunner::stats_tainted_insts;

void ModifyCallbackVisitor::prestat() {
    int cnt_memop = 0;
    for (auto &F : mod) {
        for (auto &BB : F) {
            for (auto &I : BB) {
                // if (Globals::DirFuncs.size() &&
                //     (Globals::DirFuncs.find(&F) != Globals::DirFuncs.end()))
                //     continue;
                if (dyn_cast<LoadInst>(&I) || dyn_cast<StoreInst>(&I) ||
                    dyn_cast<MemTransferInst>(&I))
                    cnt_memop++;
                // dbgs() << I.getFunction()->getName() << " ";
                // dbgs() << I << "\n";
            }
        }
    }
    // dbgs() << "\n** Number of all memop insts: " << cnt_memop << "\n";
}

void ModifyCallbackVisitor::poststat() {
    std::map<Function *, int> cntmap;
    std::map<Function *, int> cntmap2;

    // dbgs() << "\n\n\n** Traversed functions\n";
    // for (auto func : analyzed_functions) {
    //     dbgs() << func->getName() << "\n";
    // }

    // dbgs() << "\n** All replicated functions\n";
    for (auto &pair : newfunctions.map) {
        auto func = pair.first.first;
        auto hash = pair.first.second;
        auto &funcmod = pair.second;
        if (!funcmod.isentry && !funcmod.isExportFn) {
            // dbgs() << "New: " << funcmod.newfunc->getName() << " hash: " << hash << "\n";
            if (cntmap.find(func) == cntmap.end())
                cntmap[func] = 1;
            else
                cntmap[func]++;

            for (auto &pair : funcmod.fn_map) {
                auto instmod = &(pair.second);
                if (instmod->tainted) {
                    if (instmod->type == InstModType::MPKWrap ||
                        instmod->type == InstModType::MemFunc) {
                        if (cntmap2.find(func) == cntmap2.end())
                            cntmap2[func] = 1;
                        else
                            cntmap2[func]++;
                        break;
                    }
                }
            }
        }
    }

    // dbgs() << "\n** Number of replica for each function\n";
    // for (auto &pair : cntmap) {
    //     auto func = pair.first;
    //     auto cnt = pair.second;
    //     dbgs() << func->getName() << " " << cnt << "\n";
    // }

    // dbgs() << "\n** Functions replicated for MPKWrap MemFunc\n";
    for (auto &pair : cntmap2) {
        auto func = pair.first;
        auto cnt = pair.second;
        // dbgs() << func->getName() << " " << cnt;
        for (auto &pair : newfunctions.map) {
            auto func_iter = pair.first.first;
            auto &funcmod = pair.second;
            if (func != func_iter) continue;
            for (auto &pair : funcmod.fn_map) {
                auto instmod = &(pair.second);
                if (!instmod->tainted) continue;
                if (instmod->type == InstModType::MPKWrap ||
                    instmod->type == InstModType::MemFunc) {
                    // dbgs() << " " << funcmod.newfunc->getName();
                    break;
                }
            }
        }
        // dbgs() << "\n";
    }

    int cnt_sens_memop = FunctionModifyRunner::stats_tainted_insts.size();
    // dbgs() << "\n** Number of all wrapped memop insts: " << cnt_sens_memop << "\n";
    // for (auto inst : FunctionModifyRunner::stats_tainted_insts) {
    //     dbgs() << inst->getFunction()->getName() << " ";
    //     dbgs() << *inst << "\n";
    // }
}

void ModifyCallbackVisitor::run_modify() {
    prestat();
    // stitch root context
    // DEBUG_MODIFY(dbgs() << "Run_modify "
    //                     << "\n");
    // DEBUG_MODIFY(dbgs() << "Threshold : " << Globals::Threshold << "\n");
    if (!currCtx->funcmod.anytainted) return;
    auto funcobj = newfunctions.tryinsert(currCtx);
    funcobj->isentry = true;
    // process every new function
    for (auto funcobj : newfunctions.list) {
        FunctionModifyRunner runner(this, funcobj);
        runner.reportTaint();
        runner.copyNew();
        runner.removePragmaFuncs();
        runner.expandFuncPtr();
        runner.substitueCallTarget();
        runner.replaceAllocs();
        // if (funcobj->newfunc) DEBUG_MODIFY(dbgs() << "A new function has been created: " << funcobj->newfunc->getName() << "\n");
        runner.countTaint();
        runner.insertWrpkruInst();
    }
    poststat();
}
