#include "Uriah.hpp"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"
#include "Utils.hpp"
#include "ValueRange.hpp"
#include "CompatibleType.hpp"
#include "llvm/Analysis/MemoryBuiltins.h"

using namespace llvm;
using namespace UnifiedMemSafe;

bool UnifiedMemSafe::Uriah::isPtrToHeap(llvm::Value* ssaVariable, const llvm::TargetLibraryInfo *TLI, pdg::PTAWrapper &ptaw) {
    int noOperands = -1;
    llvm::Instruction* local = dyn_cast_or_null<Instruction>(ssaVariable);
    if (!local) {
        return false;
    }

    noOperands = local->getNumOperands();

    if (!(ptaw._ander_pta->getPAG()->hasValueNode(ssaVariable))) {
        return false;
    }

    if (local && TLI) {
        // If it is a call instruction to heap allocation functions
        if (isa<GlobalVariable>(ssaVariable)) {
            return false;
        }

        if (isAllocationFn(local, TLI)) {
            return true;
        }

        if (CallInst *allocationFn = dyn_cast_or_null<CallInst>(local)) {
            if (allocationFn != nullptr && allocationFn->getCalledFunction() != nullptr &&
                (allocationFn->getCalledFunction()->getName().contains("alloc") ||
                 allocationFn->getCalledFunction()->getName().contains("operator new") ||
                 allocationFn->getCalledFunction()->getName().contains("operator new[]"))) {
                return true;
            }
        }

        // Traverse all its operands to see whether it relates to the heap
        for (int j = 0; j < noOperands; j++) {
            // Test if it relates to a Global variable
            if (isa<GlobalVariable>(local->getOperand(j))) {
                return false;
            }

            if (local->getOperand(j) && isAllocationFn(local->getOperand(j), TLI)) {
                return true;
            }

            if (CallInst *operandAlloc = dyn_cast_or_null<CallInst>(local->getOperand(j))) {
                if (operandAlloc->getCalledFunction() != nullptr &&
                    (operandAlloc->getCalledFunction()->getName().contains("alloc") ||
                     operandAlloc->getCalledFunction()->getName().contains("operator new") ||
                     operandAlloc->getCalledFunction()->getName().contains("operator new[]"))) {
                    return true;
                }
            }
        }
    } else {
        SVF::NodeID nodeId = ptaw._ander_pta->getPAG()->getValueNode(ssaVariable);
        SVF::PointsTo pointsToInfo = ptaw._ander_pta->getPts(nodeId);
        for (auto memObjID = pointsToInfo.begin(); memObjID != pointsToInfo.end(); memObjID++) {
            if (ptaw._ander_pta->getPAG()->getObject(*memObjID)->isHeap()) {
                return true;
            }
        }
        return false;
    }

    return false;
}


Value *UnifiedMemSafe::Uriah::getRootValue(Value *v) {
    Value *root = v;
    
    if (GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(v)) {
        Value *op = gep->getPointerOperand();
        return getRootValue(op);
    }
    else if (LoadInst *load = dyn_cast<LoadInst>(v)) {
        Value *op = load->getPointerOperand();
        return getRootValue(op);
    }
    else if (AllocaInst *alloca = dyn_cast<AllocaInst>(v)) { // root
        root = alloca;
        return root;
    }
    else if (CallInst *call = dyn_cast_or_null<CallInst>(v)){
        if ((call->getCalledFunction()!=NULL) && call->getCalledFunction()->getName().contains("alloc")) {
            Value *arg_0 = call->getArgOperand(0);
            return getRootValue(arg_0);
        }	
    }
    else if (CastInst *cast = dyn_cast<CastInst>(v)) {
        Value *op = cast->getOperand(0);
        return getRootValue(op);
    }

    return root;
}

bool UnifiedMemSafe::Uriah::queryAliasing(Value *v1, Value *v2) {
    
    Value *root1 = getRootValue(v1);
    Value *root2 = getRootValue(v2);

    if (root1 == root2) {
        return true;
    }

    return false;
}

/// -----------------------------------------------------------------------
/// Collect all potential heap pointers & do alias checking (PDG + SVF)
/// -----------------------------------------------------------------------

void UnifiedMemSafe::Uriah::collectHeapPointers(
    std::map<const VariableMapKeyType *, VariableInfo> &heapPointerSet,
    AnalysisState &TheState,
    const llvm::TargetLibraryInfo *TLI,
    pdg::PTAWrapper &ptaw,
    pdg::ProgramGraph *pdgraph,
    const std::set<pdg::EdgeType> &edgeTypes,
    std::set<pdg::Node *> &unsafeNode /* out-param */)
{
    for (auto it = TheState.Variables.begin(); it != TheState.Variables.end(); ++it) {
        const Instruction *instruction = dyn_cast_or_null<Instruction>(it->first);
        llvm::Value *ssaVariable = const_cast<UnifiedMemSafe::VariableMapKeyType *>(it->first);

        if (!instruction)
            continue;

        // This SSA variable has nothing to do with heap, discarding
        if (!isPtrToHeap(ssaVariable, TLI, ptaw)) {
            continue;
        }

        // Found pointer to the heap
        heapPointerSet[it->first] = it->second;

        llvm::Function *heapAnalyzeFunction = const_cast<llvm::Instruction *>(instruction)->getFunction();
        llvm::Value *heapPointer = const_cast<llvm::Value *>(it->first);

        // Using PDG for aliasing
        std::set<pdg::EdgeType> edgeTypesCopy = edgeTypes;
        auto *node = pdgraph->getNode(*heapPointer);
        if (!node) 
            continue; // Just in case getNode returns null

        auto reachable_nodes = pdgraph->findNodesReachedByEdges(*node, edgeTypesCopy);
        for (auto n : reachable_nodes) {
            pdg::GraphNodeType node_type = n->getNodeType();
            if (node_type == pdg::GraphNodeType::INST) {
                unsafeNode.insert(n);
            }
        }

        // Using SVF for aliasing
        for (inst_iterator heapinst = inst_begin(*heapAnalyzeFunction), 
                           e = inst_end(*heapAnalyzeFunction);
             heapinst != e; 
             ++heapinst)
        {
            if (heapPointer == &*heapinst)
                continue;

            Instruction *InstMayAliasHeap = &*heapinst;
            /*
            if (!(ptaw._ander_pta->getPAG()->hasValueNode(heapPointer))) {
                errs() << GREEN << "Heap Alias Missing SVF Node " << *InstMayAliasHeap << NORMAL << "\n";
            }
            if (!(ptaw._ander_pta->getPAG()->hasValueNode(InstMayAliasHeap))) {
                errs() << GREEN << "Heap Alias Missing SVF Node " << *InstMayAliasHeap << NORMAL << "\n";
            }
            */

            if (!(ptaw._ander_pta->getPAG()->hasValueNode(heapPointer)) ||
                !(ptaw._ander_pta->getPAG()->hasValueNode(InstMayAliasHeap)))
            {
                continue;
            }
            // Get aliasing information
            // errs() << GREEN << "Querying Heap Alias: " << *InstMayAliasHeap
            //        << " With: " << *heapPointer << NORMAL << "\n";
            auto aliasResultHeap = ptaw.queryAlias(*heapPointer, *InstMayAliasHeap);
            auto aliasResultHeapOverApproximated = queryAliasing(heapPointer, InstMayAliasHeap);
            if ((aliasResultHeap != NoAlias) || (aliasResultHeapOverApproximated)) {
                // errs() << GREEN << "Find Heap Alias: " << *InstMayAliasHeap
                //        << " With: " << *heapPointer << NORMAL << "\n";
                if (UnifiedMemSafe::VariableMapKeyType *mayAliasPointerHeap =
                        dyn_cast_or_null<UnifiedMemSafe::VariableMapKeyType>(InstMayAliasHeap))
                {
                    // errs() << GREEN << "Heap Alias: " << *mayAliasPointerHeap << NORMAL << "\n";
                    if (TheState.GetPointerVariableInfo(mayAliasPointerHeap) != nullptr) {
                        UnifiedMemSafe::VariableInfo *aliasVariableInfoHeap = 
                            TheState.GetPointerVariableInfo(mayAliasPointerHeap);
                        heapPointerSet[mayAliasPointerHeap] = *aliasVariableInfoHeap;
                    }
                }
            }
        }
    }
}


/// -----------------------------------------------------------------------
///  Identify classification of heap objects (seq / dyn) -> unsafe sets
/// -----------------------------------------------------------------------
void UnifiedMemSafe::Uriah::identifyHeapObjectClassification(
    std::map<const VariableMapKeyType *, VariableInfo> &heapPointerSet,
    std::map<const VariableMapKeyType *, VariableInfo> &heapSeqPointerSet,
    std::map<const VariableMapKeyType *, VariableInfo> &heapDynPointerSet,
    std::map<const VariableMapKeyType *, VariableInfo> &unsafeUniqueHeapPointerSet,
    std::map<const VariableMapKeyType *, VariableInfo> &unsafeHeapPointerSet)
{
    for (auto it = heapPointerSet.begin(); it != heapPointerSet.end(); ++it) {
        if (it->second.classification == UnifiedMemSafe::VariableStates::Dyn ||
            it->second.classification == UnifiedMemSafe::VariableStates::Seq)
        {
            // Mark as unsafe
            unsafeUniqueHeapPointerSet[it->first] = it->second;
            unsafeHeapPointerSet[it->first] = it->second;

            if (it->second.classification == UnifiedMemSafe::VariableStates::Seq) {
                heapSeqPointerSet[it->first] = it->second;
            }
            if (it->second.classification == UnifiedMemSafe::VariableStates::Dyn) {
                heapDynPointerSet[it->first] = it->second;
            }
        }
    }
}


/// -----------------------------------------------------------------------
///  Identify + classify unsafe heap objects by alias
/// -----------------------------------------------------------------------
void UnifiedMemSafe::Uriah::identifyAndClassifyUnsafeHeapObjects(
    std::map<const VariableMapKeyType *, VariableInfo> &heapPointerSet,
    std::map<const VariableMapKeyType *, VariableInfo> &unsafeUniqueHeapPointerSet,
    std::map<const VariableMapKeyType *, VariableInfo> &unsafeAliasHeapPointerSet,
    std::map<const VariableMapKeyType *, VariableInfo> &unsafeHeapPointerSet,
    AnalysisState &TheState,
    pdg::PTAWrapper &ptaw)
{
    for (auto it = unsafeUniqueHeapPointerSet.begin();
              it != unsafeUniqueHeapPointerSet.end(); 
              ++it)
    {
        const Instruction *instruction = dyn_cast_or_null<Instruction>(it->first);
        if (!instruction) 
            continue;

        llvm::Function *analyzeFunction = const_cast<llvm::Instruction *>(instruction)->getFunction();
        llvm::Value *unsafePointer = const_cast<llvm::Value *>(it->first);

        for (inst_iterator inst = inst_begin(*analyzeFunction), 
                           e = inst_end(*analyzeFunction);
             inst != e;
             ++inst)
        {
            if (unsafePointer == &*inst)
                continue;

            Instruction *InstMayAlias = &*inst;
            if (!(ptaw._ander_pta->getPAG()->hasValueNode(unsafePointer)) ||
                !(ptaw._ander_pta->getPAG()->hasValueNode(InstMayAlias)))
            {
                continue;
            }
            // errs() << GREEN << "Querying Heap Alias: " << *InstMayAlias
            //        << " With: " << *unsafePointer << NORMAL << "\n";
            auto aliasResult = ptaw.queryAlias(*unsafePointer, *InstMayAlias);
            auto aliasResultOverApproximated = queryAliasing(unsafePointer, InstMayAlias);

            if (aliasResult != NoAlias || aliasResultOverApproximated) {
                // errs() << GREEN << "Find Heap Alias: " << *InstMayAlias
                //        << " With: " << *unsafePointer << NORMAL << "\n";
                if (auto *mayAliasPointer = 
                        dyn_cast_or_null<UnifiedMemSafe::VariableMapKeyType>(InstMayAlias))
                {
                    if (TheState.GetPointerVariableInfo(mayAliasPointer) != nullptr) {
                        UnifiedMemSafe::VariableInfo *aliasVariableInfo = 
                            TheState.GetPointerVariableInfo(mayAliasPointer);
                        unsafeAliasHeapPointerSet[mayAliasPointer] = *aliasVariableInfo;
                        unsafeHeapPointerSet[mayAliasPointer] = *aliasVariableInfo;
                        heapPointerSet[mayAliasPointer] = *aliasVariableInfo;
                    }
                }
            }
        }
    }
}


/// -----------------------------------------------------------------------
///  Find non-aliased heap pointers and representatives among aliased sets
/// -----------------------------------------------------------------------
void UnifiedMemSafe::Uriah::findNonAliasedAndRepresentativeHeapPointers(
    const std::map<const VariableMapKeyType *, VariableInfo> &heapPointerSet,
    std::set<const llvm::Value *> &NonAliasedHeapPointers,
    pdg::PTAWrapper &ptaw)
{
    // ------------------------------
    //  Identify truly non-aliased calls
    // ------------------------------
    for (auto it1 = heapPointerSet.begin(); it1 != heapPointerSet.end(); ++it1) {
        bool hasAlias = false;
        bool isCallResult = llvm::isa<llvm::CallInst>(it1->first) &&
                            !llvm::isa<llvm::InvokeInst>(it1->first);

        if (!isCallResult)
            continue;

        for (auto it2 = heapPointerSet.begin(); it2 != heapPointerSet.end(); ++it2) {
            if (it1 == it2) continue;
            if (!(ptaw._ander_pta->getPAG()->hasValueNode(it1->first)) ||
                !(ptaw._ander_pta->getPAG()->hasValueNode(it2->first)))
            {
                continue;
            }
            auto aliasResult = ptaw.queryAlias(
                *(const_cast<llvm::Value *>(it1->first)),
                *(const_cast<llvm::Value *>(it2->first))
            );
            auto aliasResultOverApp = queryAliasing(
                const_cast<llvm::Value *>(it1->first), 
                const_cast<llvm::Value *>(it2->first)
            );
            if ((aliasResult != NoAlias || aliasResultOverApp) && isCallResult) {
                hasAlias = true;
                break;
            }
        }

        if (!hasAlias && isCallResult) {
            NonAliasedHeapPointers.insert(it1->first);
        }
    }

    // ------------------------------
    //  Representatives among aliased sets
    // ------------------------------
    std::set<const llvm::Value *> processedAliases;
    for (auto it1 = heapPointerSet.begin(); it1 != heapPointerSet.end(); ++it1) {
        // If it1->first is already identified as a truly non-aliased pointer, skip
        if (NonAliasedHeapPointers.find(it1->first) != NonAliasedHeapPointers.end())
            continue;

        bool isRepresentative = true;
        bool isCall = llvm::isa<llvm::CallInst>(it1->first) &&
                      !llvm::isa<llvm::InvokeInst>(it1->first);

        if (!isCall)
            continue;

        for (auto it2 = heapPointerSet.begin(); it2 != heapPointerSet.end(); ++it2) {
            if (it1 == it2) 
                continue;

            if (!(ptaw._ander_pta->getPAG()->hasValueNode(it1->first)) ||
                !(ptaw._ander_pta->getPAG()->hasValueNode(it2->first)))
            {
                continue;
            }
            auto aliasResult = ptaw.queryAlias(
                *(const_cast<llvm::Value *>(it1->first)),
                *(const_cast<llvm::Value *>(it2->first))
            );
            auto aliasResultOverApprox = queryAliasing(
                const_cast<llvm::Value *>(it1->first), 
                const_cast<llvm::Value *>(it2->first)
            );
            if ((aliasResult != NoAlias || aliasResultOverApprox) && isCall) {
                if (processedAliases.find(it2->first) != processedAliases.end()) {
                    isRepresentative = false;
                    break;
                }
            }
        }

        if (isRepresentative && isCall) {
            NonAliasedHeapPointers.insert(it1->first);
            processedAliases.insert(it1->first);
        }
    }
}


/// -----------------------------------------------------------------------
///  Find which allocations in `NonAliasedHeapPointers` are aliased
///    with a given pointer set (seq or dyn).
/// -----------------------------------------------------------------------
void UnifiedMemSafe::Uriah::findAliasedAllocations(
    const std::set<const llvm::Value *> &NonAliasedHeapPointers,
    const std::map<const VariableMapKeyType *, VariableInfo> &somePtrSet, 
    std::set<const llvm::Value *> &AliasedResult,
    pdg::PTAWrapper &ptaw)
{
    for (const llvm::Value *ptr : NonAliasedHeapPointers) {
        for (auto it = somePtrSet.begin(); it != somePtrSet.end(); ++it) {
            if (!(ptaw._ander_pta->getPAG()->hasValueNode(ptr)) ||
                !(ptaw._ander_pta->getPAG()->hasValueNode(it->first)))
            {
                continue;
            }
            auto aliasResult = ptaw.queryAlias(
                *(const_cast<llvm::Value *>(ptr)),
                *(const_cast<llvm::Value *>(it->first))
            );
            auto aliasResultOA = queryAliasing(
                const_cast<llvm::Value *>(ptr), 
                const_cast<llvm::Value *>(it->first)
            );
            // if (aliasResult != NoAlias) {
            if (aliasResult != NoAlias || aliasResultOA) {
                AliasedResult.insert(ptr);
                break;
            }
        }
    }
}

void Uriah::identifyDifferentKindsOfUnsafeHeapPointers(
    std::map<const VariableMapKeyType *, VariableInfo> &heapPointerSet,
    AnalysisState &TheState,
    llvm::Module *CurrentModule,
    const llvm::TargetLibraryInfo *TLI,
    pdg::PTAWrapper &ptaw,
    pdg::ProgramGraph *pdgraph,
    const std::set<pdg::EdgeType> &edgeTypes,
    std::set<const llvm::Value *> &AliasedWithHeapSeqPointers,
    std::set<const llvm::Value *> &AliasedWithHeapDynPointers)
{
    // ------------------------------------------------------------------
    // Local data structures (as before).
    // ------------------------------------------------------------------
    const Instruction *instruction;
    int heapPointerCount = 0;      // Not used in the original code, but we keep it
    int globalPointerCount = 0;    // Also not used in the original code

    std::set<const llvm::Value *> NonAliasedHeapPointers;
    std::map<const UnifiedMemSafe::VariableMapKeyType *, UnifiedMemSafe::VariableInfo> heapSeqPointerSet;
    std::map<const UnifiedMemSafe::VariableMapKeyType *, UnifiedMemSafe::VariableInfo> heapDynPointerSet;
    std::map<const UnifiedMemSafe::VariableMapKeyType *, UnifiedMemSafe::VariableInfo> unsafeUniqueHeapPointerSet;
    std::map<const UnifiedMemSafe::VariableMapKeyType *, UnifiedMemSafe::VariableInfo> unsafeAliasHeapPointerSet;
    std::map<const UnifiedMemSafe::VariableMapKeyType *, UnifiedMemSafe::VariableInfo> unsafeHeapPointerSet;
    std::set<pdg::Node *> unsafeNode;

    // Make sure PTA info is available
    if (!ptaw.hasPTASetup()) {
        errs() << "Points to info not computed\n";
        return;
    }

    // ------------------------------------------------------------------
    // 1) Collect all potential heap pointers & do alias checking
    // ------------------------------------------------------------------
    collectHeapPointers(
        heapPointerSet, TheState, TLI, ptaw, pdgraph, edgeTypes, unsafeNode
    );

    // ------------------------------------------------------------------
    // 2) Identify classification of heap objects (Dyn / Seq)
    // ------------------------------------------------------------------
    identifyHeapObjectClassification(
        heapPointerSet,
        heapSeqPointerSet,
        heapDynPointerSet,
        unsafeUniqueHeapPointerSet,
        unsafeHeapPointerSet
    );

    // ------------------------------------------------------------------
    // 3) Identify + classify unsafe heap objects by alias
    // ------------------------------------------------------------------
    identifyAndClassifyUnsafeHeapObjects(
        heapPointerSet,
        unsafeUniqueHeapPointerSet,
        unsafeAliasHeapPointerSet,
        unsafeHeapPointerSet,
        TheState,
        ptaw
    );

    // ------------------------------------------------------------------
    // Remove overlap between “originally unsafe” and “alias-unsafe”
    // (the same logic as in the original code).
    // ------------------------------------------------------------------
    for (auto it = unsafeAliasHeapPointerSet.begin();
              it != unsafeAliasHeapPointerSet.end(); )
    {
        if (unsafeUniqueHeapPointerSet.find(it->first) != unsafeUniqueHeapPointerSet.end())
            unsafeAliasHeapPointerSet.erase(it++);
        else
            ++it;
    }

    // ------------------------------------------------------------------
    // Print stats about total heap pointers.
    // ------------------------------------------------------------------
    errs() << NORMAL << "-------------HEAP MEMORY SAFETY ANALYSIS RESULTS---------------\n\n";
    errs() << GREEN << "Total Heap Pointer Number:\t\t\t\t" 
           << DETAIL << heapPointerSet.size() 
           << NORMAL << "\n";

    // ------------------------------------------------------------------
    // 4) Identify non-aliased heap pointers and alias representatives
    // ------------------------------------------------------------------
    findNonAliasedAndRepresentativeHeapPointers(
        heapPointerSet,
        NonAliasedHeapPointers,
        ptaw
    );

    // Print stats about the number of allocations
    errs() << GREEN << "Number of Heap Allocations:\t\t\t\t" 
           << DETAIL << NonAliasedHeapPointers.size() 
           << "\n";

    // ------------------------------------------------------------------
    // Print + final stats about unsafe pointers
    // ------------------------------------------------------------------
    errs() << GREEN << "CCured Unsafe Heap Pointer:\t\t\t\t" 
           << DETAIL << unsafeUniqueHeapPointerSet.size() 
           << NORMAL << "\n";

    errs() << GREEN << "Unsafe Heap Pointer By Alias:\t\t\t\t" 
           << DETAIL << unsafeAliasHeapPointerSet.size() 
           << NORMAL << "\n\n";

    errs() << GREEN << "Heap Seq Pointer:\t\t\t\t\t" 
           << DETAIL << heapSeqPointerSet.size() 
           << NORMAL << "\n";

    errs() << GREEN << "Heap Wild Pointer:\t\t\t\t\t" 
           << DETAIL << heapDynPointerSet.size() 
           << NORMAL << "\n";

    // ------------------------------------------------------------------
    // 5) Determine which allocations are aliased with Seq or Dyn pointers
    // ------------------------------------------------------------------
    findAliasedAllocations(
        NonAliasedHeapPointers, 
        heapSeqPointerSet, 
        AliasedWithHeapSeqPointers, 
        ptaw
    );

    findAliasedAllocations(
        NonAliasedHeapPointers, 
        heapDynPointerSet, 
        AliasedWithHeapDynPointers, 
        ptaw
    );
    errs() << NORMAL << "\n";

    // ------------------------------------------------------------------
    // 6) Run value-range analysis and compatible-type analysis
    // ------------------------------------------------------------------
    valueRangeAnalysis(CurrentModule, heapPointerSet, TheState);

    UnifiedMemSafe::CompatibleType compTypePass;
    compTypePass.safeTypeCastAnalysis(heapDynPointerSet, TheState);
}



