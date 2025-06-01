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

#include "CompatibleType.hpp"
#include "Utils.hpp"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
using namespace UnifiedMemSafe;

int CountIndirections(Type *T){
    if (!T->isPointerTy())
        return 0;
    PointerType *innerT = dyn_cast_or_null<PointerType>(T);
    return CountIndirections(innerT->getElementType()) + 1;
}

// unwraps a pointer until the innermost type
Type *UnwrapPointer(Type *T){
    if (!T->isPointerTy())
        return T;
    PointerType *innerT = dyn_cast_or_null<PointerType>(T);
    return UnwrapPointer(innerT->getElementType());
}

/// Utility function: determines if the cast is potentially unsafe.
bool isPotentiallyUnsafeCast(Type *innerSrcT,
                             Type *realSrcType,
                             Type *realDstType,
                             Type *innerDstT)
{
    // Search subtypes of realSrcType to see if realDstType is present
    for (Type::subtype_iterator STI = realSrcType->subtype_begin(),
                                 STE = realSrcType->subtype_end();
         STI != STE; ++STI)
    {
        if ((llvm::Type *)STI == realDstType) {
            // Found a match => potentially "downcast"
            return true;
        }
    }

    // Another special integer check
    if ((innerSrcT->isIntegerTy() && realSrcType->isIntegerTy()) &&
        ((!realDstType->isIntegerTy()) || (!innerDstT->isIntegerTy())))
    {
        return true;
    }

    /* -----------------------------------------------------------------
     *  NEW RULE:
     *  If both realSrcType and realDstType are non-integer first-class
     *  types (struct / array / vector / opaque) and they differ, regard
     *  the cast as potentially unsafe.  This flags casts such as
     *      i8* → %struct.foo*
     *      %struct.A* → %struct.B*
     *  that were previously treated as safe.
     * ----------------------------------------------------------------- */
    if (!realSrcType->isIntegerTy() && !realDstType->isIntegerTy()) {
        if (realSrcType != realDstType)
            return true;
    }

    // Otherwise considered safe
    return false;
}

/// Helper function: handle the case where CastInst operand is a LoadInst.
bool handleLoadCast(CastInst *II,
                    LoadInst *loadInst,
                    std::map<const VariableMapKeyType *, VariableInfo> &heapDynPointerSet,
                    std::map<const UnifiedMemSafe::VariableMapKeyType *,
                             UnifiedMemSafe::VariableInfo>::iterator &it,
                    Type *innerSrcT,
                    Type *innerDstT,
                    const AnalysisState &TheState)
{
    // Analyzing the "LoadInst" sub-case:
    Type *realSrcType = UnwrapPointer(loadInst->getType());
    Type *realDstType = nullptr;

    // Find realDstType from the uses
    for (Use &use : II->uses()) {
        User *user = use.getUser();
        Instruction *userInst = dyn_cast<Instruction>(user);
        if (StoreInst *SI = dyn_cast_or_null<StoreInst>(userInst)) {
            realDstType = UnwrapPointer(SI->getPointerOperandType());
            break;
        } else if (LoadInst *LI = dyn_cast_or_null<LoadInst>(userInst)) {
            realDstType = UnwrapPointer(LI->getType());
            for (Use &LIuse : LI->uses()) {
                User *LIuser = LIuse.getUser();
                Instruction *LIuserInst = dyn_cast<Instruction>(LIuser);
                if (CastInst *CII = dyn_cast_or_null<CastInst>(LIuserInst)) {
                    realDstType = UnwrapPointer(CII->getDestTy());
                    break;
                }
            }
            break;
        } else if (CastInst *CI = dyn_cast_or_null<CastInst>(userInst)) {
            realDstType = UnwrapPointer(CI->getDestTy());
            break;
        }
    }
    if (realDstType == nullptr)
        realDstType = innerDstT;

    // Check if it is an unsafe cast
    bool isLoadUnsafeCast = isPotentiallyUnsafeCast(innerSrcT, realSrcType, realDstType, innerDstT);
    if (!isLoadUnsafeCast) {
        // Erase from the set if safe
        heapDynPointerSet.erase(it++);
        if (UnifiedMemSafe::VariableMapKeyType *loadVar =
                dyn_cast_or_null<UnifiedMemSafe::VariableMapKeyType>(II->getOperand(0)))
        {
            if (heapDynPointerSet.find(loadVar) != heapDynPointerSet.end())
                heapDynPointerSet.erase(loadVar);
        }
        return false;
    }
    return true; // Keep going
}

/// Helper function: handle the case where CastInst operand is a GEP.
bool handleGetElementPtrCast(
    CastInst *II,
    GetElementPtrInst *gepInst,
    std::map<const VariableMapKeyType *, VariableInfo> &heapDynPointerSet,
    std::map<const UnifiedMemSafe::VariableMapKeyType *,
             UnifiedMemSafe::VariableInfo>::iterator &it,
    Type *innerSrcT,
    Type *innerDstT)
{
    Type *realSrcType = UnwrapPointer(gepInst->getResultElementType());
    Type *realDstType = nullptr;

    // Find realDstType from the uses
    for (Use &use : II->uses()) {
        User *user = use.getUser();
        Instruction *userInst = dyn_cast<Instruction>(user);
        if (StoreInst *SI = dyn_cast_or_null<StoreInst>(userInst)) {
            realDstType = UnwrapPointer(SI->getPointerOperandType());
            break;
        } else if (LoadInst *LI = dyn_cast_or_null<LoadInst>(userInst)) {
            realDstType = UnwrapPointer(LI->getType());
            for (Use &LIuse : LI->uses()) {
                User *LIuser = LIuse.getUser();
                Instruction *LIuserInst = dyn_cast<Instruction>(LIuser);
                if (CastInst *CII = dyn_cast_or_null<CastInst>(LIuserInst)) {
                    realDstType = UnwrapPointer(CII->getDestTy());
                    break;
                }
            }
            break;
        } else if (CastInst *CI = dyn_cast_or_null<CastInst>(userInst)) {
            realDstType = UnwrapPointer(CI->getDestTy());
            break;
        }
    }
    if (realDstType == nullptr)
        realDstType = innerDstT;

    // Check if it is an unsafe cast
    bool isGEPUnsafeCast = isPotentiallyUnsafeCast(innerSrcT, realSrcType, realDstType, innerDstT);
    if (!isGEPUnsafeCast) {
        // Erase from the set if safe
        heapDynPointerSet.erase(it++);
        if (UnifiedMemSafe::VariableMapKeyType *GEPVar =
                dyn_cast_or_null<UnifiedMemSafe::VariableMapKeyType>(II->getOperand(0)))
        {
            if (heapDynPointerSet.find(GEPVar) != heapDynPointerSet.end())
                heapDynPointerSet.erase(GEPVar);
        }
        return false;
    }
    return true;
}

/// Helper function: handle the case where CastInst operand is another CastInst.
bool handleCastInstCast(
    CastInst *II,
    CastInst *nestedCast,
    std::map<const VariableMapKeyType *, VariableInfo> &heapDynPointerSet,
    std::map<const UnifiedMemSafe::VariableMapKeyType *,
             UnifiedMemSafe::VariableInfo>::iterator &it,
    Type *innerSrcT,
    Type *innerDstT)
{
    Type *realSrcType = UnwrapPointer(nestedCast->getSrcTy());
    Type *realDstType = nullptr;

    // Find realDstType from the uses
    for (Use &use : II->uses()) {
        User *user = use.getUser();
        Instruction *userInst = dyn_cast<Instruction>(user);
        if (StoreInst *SI = dyn_cast_or_null<StoreInst>(userInst)) {
            realDstType = UnwrapPointer(SI->getPointerOperandType());
            break;
        } else if (LoadInst *LI = dyn_cast_or_null<LoadInst>(userInst)) {
            realDstType = UnwrapPointer(LI->getType());
            for (Use &LIuse : LI->uses()) {
                User *LIuser = LIuse.getUser();
                Instruction *LIuserInst = dyn_cast<Instruction>(LIuser);
                if (CastInst *CII = dyn_cast_or_null<CastInst>(LIuserInst)) {
                    realDstType = UnwrapPointer(CII->getDestTy());
                    break;
                }
            }
            break;
        } else if (CastInst *CI = dyn_cast_or_null<CastInst>(userInst)) {
            realDstType = UnwrapPointer(CI->getDestTy());
            break;
        }
    }
    if (realDstType == nullptr)
        realDstType = innerDstT;

    // Check if it is an unsafe cast
    bool isCastUnsafeCast = isPotentiallyUnsafeCast(innerSrcT, realSrcType, realDstType, innerDstT);
    if (!isCastUnsafeCast) {
        // Erase from the set if safe
        heapDynPointerSet.erase(it++);
        if (UnifiedMemSafe::VariableMapKeyType *CastVar =
                dyn_cast_or_null<UnifiedMemSafe::VariableMapKeyType>(II->getOperand(0)))
        {
            if (heapDynPointerSet.find(CastVar) != heapDynPointerSet.end())
                heapDynPointerSet.erase(CastVar);
        }
        return false;
    }
    return true;
}

/// Helper function: handle the case where CastInst operand is a CallInst.
bool handleCallInstCast(
    CastInst *II,
    Value *op,
    std::map<const VariableMapKeyType *, VariableInfo> &heapDynPointerSet,
    std::map<const UnifiedMemSafe::VariableMapKeyType *,
             UnifiedMemSafe::VariableInfo>::iterator &it)
{
    bool isUnsafe = false;

    if (CallInst *CI = dyn_cast<CallInst>(op)) {
        Function *Callee = CI->getCalledFunction();
        if (Callee) {
            StringRef FName = Callee->getName();

            /* ------------------------------------------------------------
             *  Detect undersized malloc / calloc followed by
             *  cast to a larger struct type.
             * ------------------------------------------------------------ */
            if (FName == "malloc" || FName == "calloc") {
                uint64_t allocSize = 0;

                if (FName == "malloc") {
                    if (auto *SzC = dyn_cast<ConstantInt>(CI->getArgOperand(0)))
                        allocSize = SzC->getZExtValue();
                } else { // calloc
                    if (auto *CntC = dyn_cast<ConstantInt>(CI->getArgOperand(0)))
                        if (auto *SzC = dyn_cast<ConstantInt>(CI->getArgOperand(1)))
                            allocSize = CntC->getZExtValue() * SzC->getZExtValue();
                }

                if (allocSize > 0 && II->getDestTy()->isPointerTy()) {
                    const DataLayout &DL = II->getModule()->getDataLayout();
                    uint64_t dstSize =
                        DL.getTypeAllocSize(UnwrapPointer(II->getDestTy()));

                    /*  Flag as unsafe if the destination struct (or array, etc.)
                     *  is larger than the allocation. */
                    if (dstSize > allocSize)
                        isUnsafe = true;
                }
            }
        }
    }

    if (!isUnsafe) {
        /*  Previous behaviour: treat as safe and remove the entry. */
        heapDynPointerSet.erase(it++);
        if (UnifiedMemSafe::VariableMapKeyType *CallVar =
                dyn_cast_or_null<UnifiedMemSafe::VariableMapKeyType>(op))
        {
            if (heapDynPointerSet.find(CallVar) != heapDynPointerSet.end())
                heapDynPointerSet.erase(CallVar);
        }
        return false; // iterator erased
    }

    /* Keep the map entry so the pointer is reported as unsafe. */
    return true;
}

bool handleCastOperation(
    CastInst *II,
    std::map<const VariableMapKeyType *, VariableInfo> &heapDynPointerSet,
    std::map<const VariableMapKeyType *, VariableInfo>::iterator &it,
    Type *innerSrcT,
    Type *innerDstT,
    const AnalysisState &TheState)
{
    Value *op = II->getOperand(0);

    if (LoadInst *loadInst = dyn_cast_or_null<LoadInst>(op)) {
        return handleLoadCast(II, loadInst, heapDynPointerSet, it, innerSrcT,
                              innerDstT, TheState);
    } else if (GetElementPtrInst *gepInst =
                   dyn_cast_or_null<GetElementPtrInst>(op)) {
        return handleGetElementPtrCast(II, gepInst, heapDynPointerSet, it,
                                       innerSrcT, innerDstT);
    } else if (CastInst *nestedCast = dyn_cast_or_null<CastInst>(op)) {
        return handleCastInstCast(II, nestedCast, heapDynPointerSet, it,
                                  innerSrcT, innerDstT);
    } else if (isa<CallInst>(op)) {
        return handleCallInstCast(II, op, heapDynPointerSet, it);
    }
    return true; // If no cases match, just continue.
}

void CompatibleType::safeTypeCastAnalysis(
    std::map<const VariableMapKeyType *, VariableInfo> &heapDynPointerSet,
    const AnalysisState &TheState)
{
    for (auto it = heapDynPointerSet.begin(); it != heapDynPointerSet.end();) {
        const Instruction *instruction = dyn_cast_or_null<Instruction>(it->first);
        Instruction *dynInst =
            const_cast<llvm::Instruction *>(instruction);

        if (CastInst *II = dyn_cast_or_null<CastInst>(dynInst)) {
            Type *srcT = II->getSrcTy();
            Type *dstT = II->getDestTy();

            if (srcT->isPointerTy()) {
                Type *innerSrcT = UnwrapPointer(srcT);
                Type *innerDstT = UnwrapPointer(dstT);

                if (CountIndirections(srcT) != CountIndirections(dstT) ||
                    !innerSrcT->isIntegerTy() || !innerDstT->isIntegerTy())
                {
                    if (!handleCastOperation(II, heapDynPointerSet, it,
                                             innerSrcT, innerDstT, TheState))
                        continue;
                } else if (innerSrcT->isIntegerTy() &&
                           innerDstT->isIntegerTy() && !isa<SExtInst>(II) &&
                           !isa<TruncInst>(II))
                {
                    if (!handleCastOperation(II, heapDynPointerSet, it,
                                             innerSrcT, innerDstT, TheState))
                        continue;
                }
            } else if (!isa<SExtInst>(II) && !isa<TruncInst>(II)) {
                Type *innerSrcT = UnwrapPointer(srcT);
                Type *innerDstT = UnwrapPointer(dstT);
                if (!handleCastOperation(II, heapDynPointerSet, it, innerSrcT,
                                         innerDstT, TheState))
                    continue;
            }
        }

        if (!heapDynPointerSet.empty())
            ++it;
        else
            break;
    }

    errs() << GREEN
           << "Unsafe Dyn Pointer After Compatible-Type Cast Analysis:\t"
           << DETAIL << heapDynPointerSet.size() << NORMAL << "\n\n\n";
}
