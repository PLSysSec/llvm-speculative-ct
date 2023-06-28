#include "AliasTaintCtx.h"
#include "Utils.h"


ObjectMap AliasTaintContext::globalobjects;


void AliasTaintContext::setupGlobals(Module &m) {
    for (Function &func: m) {
        globalobjects.createRegMemPair(&func);
    }
    for (GlobalVariable &var: m.getGlobalList()) {
        globalobjects.createRegMemPair(&var);
    }

    InitializerWalker walker(m.getDataLayout(), m.getContext());
    for (GlobalVariable &var: m.getGlobalList()) {
        if (var.hasInitializer()) {
            auto init = var.getInitializer();
            walker.scan(init);
            if (!walker.results.size()) continue;

            // DEBUG_GLOBOBJ(dbgs() << var.getName() << "\n");
            auto srcobj = globalobjects.findMemObj(&var);
            for (auto &item: walker.results) {
                auto dstobj = globalobjects.findMemObj(item.target);
                auto field = srcobj->getFieldObj(item.srcoff);
                field->addPointsTo(dstobj, item.dstoff, nullptr);
                // DEBUG_GLOBOBJ(dbgs()
                //     << "\t" << item.srcoff << "\t" << item.dstoff
                //     << "\t" << item.target->getName() << "\n");
            }
        }
    }
}


void AliasTaintContext::getFuncPtrTargets(Value *fp, std::vector<Function*> &ret) {
    auto fpReg = findOpReg(fp);
    if (!hasPointsTo(fpReg)) return;
    for (auto &pt: fpReg->pointsto) {
        auto dst = pt.target;
        if (auto func = dyn_cast<Function>(dst->represented))
            ret.push_back(func);
    }
    if (ret.size()) {
        // DEBUG_CALLINST(dbgs() << "Targets found for: " << *fp << "\n");
        for (auto func: ret) {
            // DEBUG_CALLINST(dbgs() << "\t" << func->getName() << "\n");
        }
    }
}
