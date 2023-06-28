#ifndef CONTEXTBASE_H
#define CONTEXTBASE_H

#include <llvm/IR/Module.h>
#include <llvm/IR/Instructions.h>
#include <utility>
#include <vector>

using namespace llvm;

template<typename CtxClass>
struct BaseContext {
    std::vector<CtxClass*> children;
    CtxClass *parent, *self;

    Instruction *inst;
    Function *func;
    bool inside_loop, lastloopiter;
    int loopidx;

    // context navigation

    std::pair<CtxClass*, bool> getOrCreateChildCtx(Instruction *inst, Function *func) {
        for (auto ctxptr: children) {
            if (ctxptr->inst == inst && ctxptr->func == func) {
                return std::make_pair(ctxptr, false);
            }
        }
        auto ret = new CtxClass(inst, func);
        ret->parent = self;
        children.push_back(ret);
        return std::make_pair(ret, true);
    }

    bool checkRecursive(Instruction &I) {
        for (auto ctx = self; ctx; ctx = ctx->parent) {
            if (&I == ctx->inst) {
                return true;
            }
        }
        return false;
    }

    // interfaces

    BaseContext(Instruction *inst, Function *func)
            : parent(nullptr), inst(inst), func(func), loopidx(0) {
        self = static_cast<CtxClass*>(this);
    }

    void getFuncPtrTargets(Value *fp, std::vector<Function*> &ret) {
        assert(false);
    }
};


#endif  // CONTEXTBASE_H
