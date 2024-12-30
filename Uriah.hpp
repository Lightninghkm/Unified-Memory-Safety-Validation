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
 
#ifndef URIAH_HPP
#define URIAH_HPP

#include "llvm/IR/Value.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "program-dependence-graph/include/PTAWrapper.hh"
#include "program-dependence-graph/include/Graph.hh"
#include "program-dependence-graph/include/PDGEnums.hh"
#include "ProgramDependencyGraph.hh" 
#include "Utils.hpp"
#include <map>
#include <set>
#include <chrono>

namespace UnifiedMemSafe {

    class Uriah {
    public:
        static bool isPtrToHeap(llvm::Value* ssaVariable, const llvm::TargetLibraryInfo *TLI, pdg::PTAWrapper &ptaw);


        static llvm::Value* getRootValue(llvm::Value* v);

        static bool queryAliasing(llvm::Value* v1, llvm::Value* v2);

        static void collectHeapPointers(
            std::map<const VariableMapKeyType *, VariableInfo> &heapPointerSet,
            AnalysisState &TheState,
            const llvm::TargetLibraryInfo *TLI,
            pdg::PTAWrapper &ptaw,
            pdg::ProgramGraph *pdgraph,
            const std::set<pdg::EdgeType> &edgeTypes,
            std::set<pdg::Node *> &unsafeNode /* out-param */
        );

        static void identifyHeapObjectClassification(
            std::map<const VariableMapKeyType *, VariableInfo> &heapPointerSet,
            std::map<const VariableMapKeyType *, VariableInfo> &heapSeqPointerSet,
            std::map<const VariableMapKeyType *, VariableInfo> &heapDynPointerSet,
            std::map<const VariableMapKeyType *, VariableInfo> &heapDynPtrSet,
            std::map<const VariableMapKeyType *, VariableInfo> &unsafeUniqueHeapPointerSet,
            std::map<const VariableMapKeyType *, VariableInfo> &unsafeHeapPointerSet
        );

        static void identifyAndClassifyUnsafeHeapObjects(
            std::map<const VariableMapKeyType *, VariableInfo> &heapPointerSet,
            std::map<const VariableMapKeyType *, VariableInfo> &unsafeUniqueHeapPointerSet,
            std::map<const VariableMapKeyType *, VariableInfo> &unsafeAliasHeapPointerSet,
            std::map<const VariableMapKeyType *, VariableInfo> &unsafeHeapPointerSet,
            std::map<const VariableMapKeyType *, VariableInfo> &heapSeqPointerSet,
            std::map<const VariableMapKeyType *, VariableInfo> &heapDynPointerSet,
            std::map<const VariableMapKeyType *, VariableInfo> &heapDynPtrSet,
            AnalysisState &TheState,
            pdg::PTAWrapper &ptaw
        );

        static void findNonAliasedAndRepresentativeHeapPointers(
            const std::map<const VariableMapKeyType *, VariableInfo> &heapPointerSet,
            std::set<const llvm::Value *> &NonAliasedHeapPointers,
            pdg::PTAWrapper &ptaw
        );

        static void findAliasedAllocations(
            const std::set<const llvm::Value *> &NonAliasedHeapPointers,
            const std::map<const VariableMapKeyType *, VariableInfo> &somePtrSet, 
            std::set<const llvm::Value *> &AliasedResult,
            pdg::PTAWrapper &ptaw
        );

        static void identifyDifferentKindsOfUnsafeHeapPointers(
            std::map<const VariableMapKeyType *, VariableInfo> &heapPointerSet,
            AnalysisState &TheState,
            llvm::Module *CurrentModule,
            const llvm::TargetLibraryInfo *TLI,
            pdg::PTAWrapper &ptaw,
            pdg::ProgramGraph *pdgraph,
            const std::set<pdg::EdgeType> &edgeTypes,
            std::set<const llvm::Value *> &AliasedWithHeapSeqPointers,
            std::set<const llvm::Value *> &AliasedWithHeapDynPointers
        );
    };

} // namespace UnifiedMemSafe

#endif // URIAH_HPP
