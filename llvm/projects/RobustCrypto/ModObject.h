#ifndef MODOBJECT_H
#define MODOBJECT_H

#include "Utils.h"
#include "llvm/IR/Module.h"

enum struct InstModType { MPKWrap, AllocaInst, MemFunc, FuncPtr, FuncDirect };

struct InstMod {

  struct CallTarget {
    Function *func;
    InstModType type;
    size_t hash;

    CallTarget() {}

    CallTarget(Function *f, InstModType t, size_t h)
        : func(f), type(t), hash(h) {}
  };

  bool inloop;
  int loopidx;
  Instruction *inst;
  InstModType type;
  bool tainted, ignorepriv;
  std::map<Function *, CallTarget> calltargets;
  Globals *globals;

  InstMod(Globals *globals)
      : inst(nullptr), tainted(false), ignorepriv(false),
        globals(globals) {}

  InstMod(const InstMod &other) {
    inloop = other.inloop;
    loopidx = other.loopidx;
    inst = other.inst;
    type = other.type;
    tainted = other.tainted;
    ignorepriv = other.ignorepriv;
    calltargets = other.calltargets;
    globals = other.globals;
  }

  size_t calcHash() {
    size_t hash = 0;
    hash_combine(hash, (globals->ValueUidMap)[inst]);
    hash_combine(hash, type);

    std::map<size_t, CallTarget> tmpMap;
    for (auto &pair : calltargets) {
      tmpMap[(globals->ValueUidMap)[pair.first]] = pair.second;
    }

    for (auto &pair : tmpMap) {
      auto &target = pair.second;
      hash_combine(hash, (globals->ValueUidMap)[target.func]);
      hash_combine(hash, target.type);
      hash_combine(hash, target.hash);
    }
    return hash;
  }
};

struct FuncMod {
  std::map<Instruction *, InstMod> fn_map;

  std::vector<ReturnInst *> returnlist;
  bool anytainted, isExportFn = false, calledbyExportFn = false;
  int cnt_total, cnt_tainted;
  Globals *globals;

  FuncMod(Globals *globals)
      : anytainted(false), cnt_total(0), cnt_tainted(0),
        globals(globals) {}

  size_t calcHash() {
    size_t hash = 0;
    std::map<size_t, InstMod> tmpMap;
    for (auto &pair : fn_map) {
      tmpMap.insert_or_assign((globals->ValueUidMap)[pair.first], pair.second);
    }
    for (auto &pair : tmpMap) {
      auto &instmod = pair.second;
      if (instmod.tainted)
        hash_combine(hash, instmod.calcHash());
    }
    return hash;
  }

  InstMod *getInstMod(Instruction &I, InstModType type, bool inloop = false,
                      int loopidx = -1) {
    auto inst = &I;
    auto it = fn_map.find(inst);
    if (it == fn_map.end()) {
      auto &temp = fn_map.insert_or_assign(inst, InstMod(globals)).first->second;
      temp.inst = inst;
      temp.type = type;
      temp.inloop = inloop;
      temp.loopidx = loopidx;
      return &temp;
    }
    return &(it->second);
  }

  InstMod *getInstMod(Instruction &I) {
    auto inst = &I;
    auto it = fn_map.find(inst);
    if (it == fn_map.end())
      return nullptr;
    return &(it->second);
  }

  void setTaint(InstMod *instmod) {
    instmod->tainted = true;
    anytainted = true;
  }

  void addCallTarget(InstMod *instmod, Function *func, size_t ctx) {
    instmod->calltargets[func] =
        InstMod::CallTarget(func, InstModType::FuncDirect, ctx);
    setTaint(instmod);
  }

  void addLibFuncCall(InstMod *instmod, Function *func, InstModType type) {
    if (instmod->type != InstModType::FuncPtr) {
      setTaint(instmod);
    } else {
      instmod->calltargets[func] = InstMod::CallTarget(func, type, 0);
      setTaint(instmod);
    }
  }
};

#endif // MODOBJECT_H
