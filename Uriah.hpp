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
            std::map<const VariableMapKeyType *, VariableInfo> &unsafeUniqueHeapPointerSet,
            std::map<const VariableMapKeyType *, VariableInfo> &unsafeHeapPointerSet
        );

        static void identifyAndClassifyUnsafeHeapObjects(
            std::map<const VariableMapKeyType *, VariableInfo> &heapPointerSet,
            std::map<const VariableMapKeyType *, VariableInfo> &unsafeUniqueHeapPointerSet,
            std::map<const VariableMapKeyType *, VariableInfo> &unsafeAliasHeapPointerSet,
            std::map<const VariableMapKeyType *, VariableInfo> &unsafeHeapPointerSet,
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
