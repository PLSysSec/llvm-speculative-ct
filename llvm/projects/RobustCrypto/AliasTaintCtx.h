#ifndef ALIASTAINTCTX_H
#define ALIASTAINTCTX_H

#include <vector>
#include <memory>
#include <map>
#include <set>
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/Constants.h"
#include "BaseContext.h"
#include "ModObject.h"

using namespace llvm;

struct AliasObject;
typedef int FieldIdTy;


struct PointsTo {
    FieldIdTy dstoff;
    AliasObject *target;
    Instruction *propagator;

    PointsTo(AliasObject *obj, FieldIdTy off, Instruction *inst)
        : dstoff(off), target(obj), propagator(inst) { }

    bool operator<(const PointsTo &rhs) const {
        if (target == rhs.target)
            return dstoff < rhs.dstoff;
        return target < rhs.target;
    }
};


struct FieldObject {
    std::set<PointsTo> pointsto;
    int taintflag, declassify;
    Instruction *tainter, *declassifier;

    FieldObject(): taintflag(0), declassify(0), tainter(nullptr), declassifier(nullptr) {
        // dbgs() << "BASH: A FieldObject is created -----------------------------\n";
    }

    void addPointsTo(AliasObject *obj, FieldIdTy off, Instruction *inst) {
        pointsto.insert(PointsTo(obj, off, inst));
    }

    void mergePointsTo(FieldObject *src, Instruction *inst) {
        for (auto &item: src->pointsto) {
            auto tmp = item;
            tmp.propagator = inst;
            pointsto.insert(tmp);
        }
    }

    // TODO: optimize these rules
    void flowTaint(FieldObject *src, Instruction *inst) {
        assert(src->declassify != src->taintflag);

        if (declassify && src->taintflag) {
            dbgs() << "FLOWTAINT: Not flowing taint to declassified value " << *inst << "\n";
            return;
        }

        if (src->declassify) {
            declassify = src->declassify;
            declassifier = inst;

            // unset taint
            taintflag = 0;
            tainter = nullptr;
            return;
        }
        if (!src->declassify && src->taintflag) {
#ifndef ONLY_MASTERKEY
            taintflag = src->taintflag;
            tainter = inst;

            // unset declassify
            declassify = 0;
            declassifier = nullptr;
#endif
            return;
        }

    }

    // Make sure that a fieldobject is not secret and declassify
    void setTaint(Instruction *inst) {
        dbgs() << "SECRET: marking tainted " << *inst << "\n";
        taintflag = 1;
        tainter = inst;

        // declassify
        declassify = 0;
        declassifier = nullptr;
    }


    // Make sure that a fieldobject is not secret and declassify
    void setDeclassify(Instruction *inst) {
        dbgs() << "DECLASSIFY: marking public " << *inst << "\n";
        declassify = 1;
        declassifier = inst;

        // secret unsetTaint
        taintflag = 0;
        tainter = nullptr;
    }
};


struct RegObject: public FieldObject {
    Value *represented;

    RegObject(Value* obj): represented(obj) {
        // dbgs() << "BASH: A RegObject is created -----------------------------\n";
     }
};


inline bool hasPointsTo(FieldObject *reg) {
    return reg && reg->pointsto.size();
}


inline bool hasTaint(FieldObject *reg) {
    return reg && reg->taintflag;
}

// separate function to check declassify
inline bool hasDeclassify(FieldObject *reg) {
    return reg && reg->declassify;
}


struct AliasObject {
    std::map<FieldIdTy, FieldObject> fieldmap;
    Value *represented;
    bool fake;

    AliasObject(Value* obj)
        : represented(obj), fake(false) {
            // dbgs() << "BASH: An AliasObject is created -----------------------------\n";
        }

    FieldObject* findFieldObj(FieldIdTy fid) {
        auto it = fieldmap.find(fid);
        if (it != fieldmap.end())
            return &(it->second);
        return nullptr;
    }

    // TODO Looks like there is a serious bug
    // out of bound access was performed here
    FieldObject* getFieldObj(FieldIdTy fid) {
        // if (!findFieldObj(fid))
            // dbgs() << "GETFIELDOBJ: looks like this will insert an item into fieldmap\n";
        return &(fieldmap[fid]);
    }

    void updateTaintByField(FieldIdTy fid, FieldObject* fobj) {
        // dbgs() << "\nUPDATE_TAINT_BY_FIELD: The size of the fieldmap is " << fieldmap.size() << " and the fieldid is " << fid << "\n";
        // for (auto item: fieldmap) {
        //     dbgs() << "the id is " << item.first << "\n";
        // }

        auto item = findFieldObj(fid);
        assert(item != nullptr);
        assert(fobj->taintflag != fobj->declassify);

        // This is field-senstive code
        item->taintflag = fobj->taintflag;
        item->tainter = fobj->tainter;
        item->declassify = fobj->declassify;
        item->declassifier = fobj->declassifier;
    }

    bool isstackobj() {
        if (represented && dyn_cast<AllocaInst>(represented))
            return true;
        else
            return false;
    }
};


inline bool checkPointsToTaint(FieldObject *reg, bool ignorestack=false) {
    assert(reg != nullptr);
    // BASH new logic - field sensitive ???
    for (auto &pt: reg->pointsto) {
        if ((!ignorestack || !pt.target->isstackobj()) && pt.target->fieldmap[pt.dstoff].taintflag) {
            assert(pt.target->fieldmap[pt.dstoff].taintflag != pt.target->fieldmap[pt.dstoff].declassify);
            return true;
        }
    }
    return false;
}

inline bool checkPointsToSink(FieldObject *reg, bool ignorestack=false) {
    assert(reg != nullptr);
    // BASH new logic - field sensitive ???
    for (auto &pt: reg->pointsto) {
        if ((!ignorestack || !pt.target->isstackobj()) && pt.target->fieldmap[pt.dstoff].declassify) {
            assert(pt.target->fieldmap[pt.dstoff].taintflag != pt.target->fieldmap[pt.dstoff].declassify);
            return true;
        }
    }
    return false;
}

struct ObjectMap {
    std::map<Value*, std::unique_ptr<RegObject> > regmap;
    std::map<Value*, std::unique_ptr<AliasObject> > memmap;

    std::pair<RegObject*, AliasObject*> createRegMemPair(Value *val) {
        auto regs = getOrCreateObject<RegObject>(regmap, val);
        auto mems = getOrCreateObject<AliasObject>(memmap, val);
        // if it is added for the first time
        if (regs.second || mems.second) {
            auto inst = static_cast<Instruction*>(val);
            regs.first->addPointsTo(mems.first, 0, inst);
        }
        return std::make_pair(regs.first, mems.first);
    }

    RegObject* getRegObj(Value *val) {
        return getOrCreateObject<RegObject>(regmap, val).first;
    }

    RegObject* findRegObj(Value *val) {
        return getNoCreateObject<RegObject>(regmap, val);
    }

    AliasObject* findMemObj(Value *val) {
        return getNoCreateObject<AliasObject>(memmap, val);
    }

private:
    template<typename T, typename Map>
    T* getNoCreateObject(Map &map, Value *val) {
        auto it = map.find(val);
        if (it != map.end())
            return it->second.get();
        return nullptr;
    }

    template<typename T, typename Map>
    std::pair<T*, bool> getOrCreateObject(Map &map, Value *val) {
        // emplace returns a bool if the item was actually inserted
        auto ins = map.emplace(val, std::unique_ptr<T>(nullptr));
        auto &uptr = ins.first->second;
        if (ins.second) uptr.reset(new T(val));
        return std::make_pair(uptr.get(), ins.second);
    }
};


struct AliasTaintContext: public BaseContext<AliasTaintContext> {
    static ObjectMap globalobjects;
    ObjectMap localobjects;
    std::set<Value*> retval;
    FuncMod funcmod;
    bool isExportFn;

    // MemObj management

    std::pair<RegObject*, AliasObject*>
    createRegMemPair(Value *val, bool fake = false) {
        auto ret = localobjects.createRegMemPair(val);
        // later create may overwrite previous fake flag
        ret.second->fake = fake;
        return ret;
    }

    // RegObj management

    RegObject* getDestReg(Value *val) {
        auto newval = val->stripPointerCasts();
        if (newval != val) return getDestReg(newval);
        // no new globalobjects will be created
        if (isa<GlobalObject>(val))
            return globalobjects.findRegObj(val);
        return localobjects.getRegObj(val);
    }

    RegObject* findOpReg(Value *val) {
        auto newval = val->stripPointerCasts();
        if (newval != val) return findOpReg(newval);
        if (isa<GlobalObject>(val))
            return globalobjects.findRegObj(val);
        auto ret = localobjects.findRegObj(val);
        // create missing pointees on last round of loop
        if (!ret && !inside_loop && val->getType()->isPointerTy()
                 && !isa<ConstantPointerNull>(val)) {
            // DEBUG_LOADSTOR(dbgs() << "findOpReg failed: " << *val << "\n");
            ret = createRegMemPair(val, true).first;
        }
        return ret;
    }

    // interfaces

    static void setupGlobals(Module &m);

    AliasTaintContext(Instruction *inst, Function *func)
        : BaseContext(inst, func), isExportFn(false) { }

    void getFuncPtrTargets(Value *fp, std::vector<Function*> &ret);
};


#endif  // ALIASTAINTCTX_H
