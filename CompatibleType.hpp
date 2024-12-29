/*
 * Copyright © 2024 Kaiming Huang
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
 
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
