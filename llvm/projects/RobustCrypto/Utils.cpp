#include "Utils.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Passes/PassBuilder.h"

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

