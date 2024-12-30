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
 
#include "DataGuard.hpp"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"
#include "Utils.hpp"
#include "ValueRange.hpp"
#include "CompatibleType.hpp"
#include "llvm/Analysis/MemoryBuiltins.h"

using namespace llvm;
using namespace UnifiedMemSafe;


// Use already computed heapPointerSet and GlobalVars to determine whether pointer points to stacks
bool DataGuard::doesPointToStack(
    const llvm::Value *V,
    const llvm::TargetLibraryInfo *TLI,
    pdg::PTAWrapper &PTA,
    const std::map<const llvm::Value *, VariableInfo> &heapPointerSet
) {
    auto *Inst = dyn_cast_or_null<Instruction>(V);
    if (!Inst)
        return false;

    for (int j = 0; j < static_cast<int>(Inst->getNumOperands()); ++j) {
        llvm::Value *op = Inst->getOperand(j);
        if (isAllocationFn(op, TLI) || llvm::isa<GlobalVariable>(op)) {
            return false;
        }
    }

    if (isAllocationFn(V, TLI))
        return false;

    if (!PTA._ander_pta->getPAG()->hasValueNode(Inst))
        return false;

    SVF::NodeID nodeId = PTA._ander_pta->getPAG()->getValueNode(Inst);
    SVF::PointsTo pointsToInfo = PTA._ander_pta->getPts(nodeId);

    for (const auto &kv : heapPointerSet) {
        const llvm::Value *heapPtr = kv.first;
        if (!PTA._ander_pta->getPAG()->hasValueNode(heapPtr))
            continue;
        SVF::NodeID heapId = PTA._ander_pta->getPAG()->getValueNode(heapPtr);
        if (heapId == nodeId) {
            return false;
        }
    }

    return true;
}

void DataGuard::identifyDifferentKindsOfUnsafeStackPointers(
    const std::map<const llvm::Value *, VariableInfo> &heapPointerSet,
    const AnalysisState &TheState,
    llvm::Module *CurrentModule,
    const llvm::TargetLibraryInfo *TLI,
    pdg::PTAWrapper &PTA
) {
    std::set<Value *> totalStackPointerSet;
    std::set<Value *> unsafeStackPointerSet;
    std::map<const VariableMapKeyType *, VariableInfo> stackSeqPointerSet;
    std::map<const VariableMapKeyType *, VariableInfo> stackDynPointerSet;
    std::map<const VariableMapKeyType *, VariableInfo> stackDynPtrSet; // Need further validation

    if (!PTA.hasPTASetup()) {
        errs() << RED << "Points to info not computed\n" << NORMAL;
        return;
    }

    // -------------------------------------------------------------------
    //  COUNT *ALL* STACK POINTERS (SAFE + SEQ + DYN + OTHERS)
    // -------------------------------------------------------------------

    // Count all stack pointers
    // Now we ignore classification, just check if it's on stack
    for (auto it = TheState.Variables.begin(); it != TheState.Variables.end(); ++it) {
        auto *Inst = dyn_cast_or_null<Instruction>(it->first);
        if (!Inst)
            continue; // Not an instruction => not on stack

        if (doesPointToStack(it->first, TLI, PTA, heapPointerSet)) {
            totalStackPointerSet.insert(const_cast<Value *>(it->first));
        }
    }

    int totalStackPointerCount = static_cast<int>(totalStackPointerSet.size());
    errs() << NORMAL << "-------------STACK MEMORY SAFETY ANALYSIS RESULTS-------------\n";
    errs() << NORMAL << "\n";
    errs() << GREEN << "Total Stack Pointer Number:\t\t\t\t" << DETAIL
           << totalStackPointerCount << NORMAL << "\n\n";


    // -------------------------------------------------------------------
    //  LOOP FOR "UNSAFE" STACK POINTERS (Dyn/Seq)
    // -------------------------------------------------------------------
    for (auto it = TheState.Variables.begin(); it != TheState.Variables.end(); ++it) {
        bool isUnsafeStackPointer = false;

        if (it->second.classification == VariableStates::Dyn ||
            it->second.classification == VariableStates::Seq) {

            isUnsafeStackPointer = true;

            auto *instruction = dyn_cast_or_null<Instruction>(it->first);
            if (instruction) {
                if (!doesPointToStack(it->first, TLI, PTA, heapPointerSet)) {
                    isUnsafeStackPointer = false;
                }
            } else {
                isUnsafeStackPointer = false;
            }

            if (isUnsafeStackPointer) {
                Value *unsafePtr = const_cast<Value *>(it->first);
                unsafeStackPointerSet.insert(unsafePtr);

                if (it->second.classification == VariableStates::Seq) {
                    stackSeqPointerSet[it->first] = it->second;
                } else if (it->second.classification == VariableStates::Dyn) {
                    stackDynPointerSet[it->first] = it->second;
                    if (CastInst *cast = dyn_cast_or_null<CastInst>(const_cast<Value*>(it->first))) {
                        stackDynPtrSet[it->first] = it->second;
                    }
                }
            }
        }
    }

    // -------------------------------------------------------------------
    //  PRINT RESULTS FOR "UNSAFE" POINTERS
    // -------------------------------------------------------------------
    errs() << GREEN << "Unsafe Stack Pointer Count:\t\t\t\t" << DETAIL
           << unsafeStackPointerSet.size() << NORMAL << "\n\n";
    errs() << GREEN << "Stack Seq Pointer Count:\t\t\t\t" << DETAIL
           << stackSeqPointerSet.size() << NORMAL << "\n";
    errs() << GREEN << "Stack Dyn Pointer Count:\t\t\t\t" << DETAIL
           << stackDynPointerSet.size() << NORMAL << "\n\n";
    valueRangeAnalysis(CurrentModule, stackSeqPointerSet, TheState);
    UnifiedMemSafe::CompatibleType compTypePass;
    compTypePass.safeTypeCastAnalysis(stackDynPtrSet, TheState);
}