#ifndef DATAGUARD_HPP
#define DATAGUARD_HPP

#include "llvm/IR/Value.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "program-dependence-graph/include/PTAWrapper.hh"
#include "Utils.hpp"
#include <map>
#include <set>

namespace UnifiedMemSafe {
    class DataGuard {
    public:
        static bool doesPointToStack(
            const llvm::Value *V,
            const llvm::TargetLibraryInfo *TLI,
            pdg::PTAWrapper &PTA,
            const std::map<const llvm::Value *, VariableInfo> &heapPointerSet
        );

        static void identifyDifferentKindsOfUnsafeStackPointers(
            const std::map<const llvm::Value *, VariableInfo> &heapPointerSet,
            const AnalysisState &TheState,
            llvm::Module *CurrentModule,
            const llvm::TargetLibraryInfo *TLI,
            pdg::PTAWrapper &PTA
        );
    };
}

#endif // DATAGUARD_HPP
