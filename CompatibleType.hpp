#ifndef COMPATIBLETYPE_HPP
#define COMPATIBLETYPE_HPP

#include "llvm/IR/Value.h"
#include "llvm/IR/Instructions.h"
#include "Utils.hpp"
#include <map>

namespace UnifiedMemSafe {

    class CompatibleType {
    public:
        void safeTypeCastAnalysis(
            std::map<const VariableMapKeyType *, VariableInfo> &heapDynPointerSet,
            const AnalysisState &TheState);
    };

} // namespace UnifiedMemSafe

#endif // COMPATIBLETYPE_HPP
