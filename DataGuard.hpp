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
