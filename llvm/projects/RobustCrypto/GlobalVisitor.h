#ifndef GLOBALVISITOR_H
#define GLOBALVISITOR_H

#include <llvm/IR/InstVisitor.h>
#include <type_traits>
#include <vector>
#include <memory>
#include <set>
#include "VisitorCallback.h"
#include "BaseContext.h"
#include "Utils.h"

struct Rules {
    static bool checkBlacklist(Function *func) {
        if (Globals::SkipFuncs.count(func->getName()) != 0)
            return true;
        else
            return false;
    }
};


template<typename CtxClass>
class GlobalVisitor: public InstVisitor<GlobalVisitor<CtxClass> > {
    static_assert(
            std::is_base_of<BaseContext<CtxClass>, CtxClass>::value,
            "Type CtxClass should be derived from BaseContext");

    public:
    typedef VisitorCallback<CtxClass> BaseCallback;
    Module &mod;
    Function &entry;
    CtxClass *currCtx;

    private:
    typedef InstVisitor<GlobalVisitor<CtxClass> > BaseVisitor;
    std::vector<std::unique_ptr<BaseCallback> > allCallbacks;
    std::vector<std::unique_ptr<CtxClass> > contexts;
    BaseVisitor *super;


    public:
    GlobalVisitor(Module &mod, Function &entry)
        : mod(mod), entry(entry), currCtx(nullptr) {
            super = static_cast<BaseVisitor*>(this);
            contexts.push_back(std::unique_ptr<CtxClass>(
                        new CtxClass(nullptr, &entry) ));
        }


    template <typename T>
        T* addCallback() {
            static_assert(
                    std::is_base_of<BaseCallback, T>::value,
                    "Type T should be derived from VisitorCallback");
            auto ret = new T(currCtx, mod);
            allCallbacks.push_back(
                    std::unique_ptr<BaseCallback>(ret));
            return ret;
        }


    void clearCallbacks() {
        allCallbacks.clear();
    }


    void analyze() {
        currCtx = contexts[0].get();
        if (Globals::IsLib) {
            currCtx->isExportFn = true;
            dbgs() << "\n\nENTRY ANALYZE: This is an export function " << entry << "\n\n";
        }
        analyze(entry);
    }


    private:
    CtxClass* pushContext(Instruction &inst, Function *func) {
        auto tmp = currCtx->getOrCreateChildCtx(&inst, func);
        if (tmp.second) contexts.push_back(
                std::unique_ptr<CtxClass>( tmp.first ));
        currCtx = tmp.first;
        return currCtx->parent;
    }


    void analyze(Function &func) {
        // DEBUG_CTXTIME(dbgs() << "Enter Function: " << func.getName() << "\n");

        int scc_cnt = 0;
        std::vector<std::vector<BasicBlock*> > traversalOrder;
        getSCCTraversalOrder(func, traversalOrder);

        for (auto &currSCC: traversalOrder) {
            if (currSCC.size() > 1) {
                scc_cnt++;
                unsigned num_to_analyze = getNumTimesToAnalyze(currSCC);
                // DEBUG_GVISITOR(dbgs() << "Enter SCC. Loop = " << num_to_analyze+1 << "\n");
                this->currCtx->inside_loop = true;

                for(unsigned i = 0; i < num_to_analyze; i++) {
                    this->visitSCC(currSCC);
                }
                this->currCtx->lastloopiter = true;
                this->currCtx->loopidx = scc_cnt;
            } else
                this->currCtx->lastloopiter = false;

            this->currCtx->inside_loop = false;
            this->visitSCC(currSCC);

            if (currSCC.size() > 1) {
                this->currCtx->lastloopiter = false;
                // DEBUG_GVISITOR(dbgs() << "Exit SCC.\n");
            }
        }
    }


    CtxClass* popContext() {
        auto child = currCtx;
        currCtx = child->parent;
        return child;
    }


    void visitSCC(std::vector<BasicBlock*> &currSCC) {
        for (auto currBB: currSCC) {
            super->visit(currBB);
        }
    }


    public:
    /// called by InstVisitor::visit(BasicBlock&)
    void visitBasicBlock(BasicBlock &BB) {
        // DEBUG_GVISITOR(dbgs() << "Visit Basic Block: " << BB.getName() << "\n");
    }


    /// called before each Instruction is handled
    void visit(Instruction &I) {
        for (auto &currCallback: allCallbacks)
            if (currCallback->enabled)
                currCallback->visit(I);
        super->visit(I);
    }


    /// called if Instruction is not handled
    void visitInstruction(Instruction &I) {
        errs() << I << "\n";
        // assert(false);
    }


#define DEFINE_VISIT_FUNC(TYPE) \
    void visit##TYPE(TYPE &I) { \
        for (auto &currCallback: allCallbacks) \
        if (currCallback->enabled) \
        currCallback->visit##TYPE(I); \
    }
#include "Instruction.def"
#undef DEFINE_VISIT_FUNC


    void visitCallInst(CallInst &I) {
        Function *currFunc = I.getCalledFunction();
        if(currCtx->inside_loop && !(currFunc && currFunc->isDeclaration())) {
            errs() << "Function inside loop, will be analyzed at last iteration\n";
            return;
        }

        if(currFunc) {
            this->processCalledFunction(I, currFunc);
        }
        else if (I.isInlineAsm()) {
            return;
            // assert(false);
        }
        else {
            Value *calledValue = I.getCalledValue();
            std::vector<Function*> targets;
            currCtx->getFuncPtrTargets(calledValue, targets);
            if (targets.size()) {
                for (auto func: targets) {
                    if (func->arg_size() == I.getNumArgOperands())
                        this->processCalledFunction(I, func);
                }
            } else {
                // DEBUG_CALLINST(dbgs() << "No targets found: " << I << "\n");
                // benign case found in libsodium: _misuse_handler
                // assert(false);
            }
        }
    }

    void processCalledFunction(CallInst &I, Function *currFunc) {
        std::vector<BaseCallback*> disabledcallbacks;
        bool divein = false;
        for (auto &currCallback: allCallbacks) {
            if (currCallback->enabled) {
                if (currCallback->visitCallInst(I, currFunc)) {
                    divein = true;
                } else {
                    disabledcallbacks.push_back(currCallback.get());
                }
            }
        }

        if (Rules::checkBlacklist(currFunc)) {
            // DEBUG_CALLINST(dbgs() << "Function in Black list: " << currFunc->getName() << "\n");
            return;
        }
        if (currCtx->checkRecursive(I)) {
            // DEBUG_CALLINST(dbgs() << "Recursive found: " << I << "\n");
            return;
        }

        if (divein) {
            assert(!currFunc->isDeclaration());
            for (auto cb: disabledcallbacks) {
                cb->enabled = false;
            }
            auto parentCtx = pushContext(I, currFunc);
            for (auto &currCallback: allCallbacks) {
                if (currCallback->enabled) {
                    currCallback->setupChildContext(I, parentCtx);
                }
            }
            analyze(*currFunc);
            auto childCtx = popContext();
            for (auto &currCallback: allCallbacks) {
                if (currCallback->enabled) {
                    currCallback->stitchChildContext(I, childCtx);
                }
            }
            for (auto cb: disabledcallbacks) {
                cb->enabled = true;
            }
        }
    }
};

#endif  // GLOBALVISITOR_H
