#include "CompatibleType.hpp"
#include "Utils.hpp"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
using namespace UnifiedMemSafe;

int CountIndirections(Type *T){
    if (!(T->isPointerTy()))
    return 0;
    PointerType *innerT = dyn_cast_or_null<PointerType>(T);
    return CountIndirections(innerT->getElementType()) + 1;
}
// unwraps a pointer until the innermost type
Type *UnwrapPointer(Type *T){
    if (!(T->isPointerTy()))
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

    // If none triggered, its not unsafe by the old definition
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
    // Original code for analyzing the "LoadInst" sub-case:
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
    if (realDstType == nullptr) {
        realDstType = innerDstT;
    }

    // Check if its an unsafe cast
    bool isLoadUnsafeCast = isPotentiallyUnsafeCast(innerSrcT, realSrcType, realDstType, innerDstT);
    if (!isLoadUnsafeCast) {
        // Erase from the set if safe
        heapDynPointerSet.erase(it++);
        if (UnifiedMemSafe::VariableMapKeyType *loadVar =
                dyn_cast_or_null<UnifiedMemSafe::VariableMapKeyType>(II->getOperand(0)))
        {
            if (heapDynPointerSet.find(loadVar) != heapDynPointerSet.end()) {
                heapDynPointerSet.erase(loadVar);
            }
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
    if (realDstType == nullptr) {
        realDstType = innerDstT;
    }

    // Check if its an unsafe cast
    bool isGEPUnsafeCast = isPotentiallyUnsafeCast(innerSrcT, realSrcType, realDstType, innerDstT);
    if (!isGEPUnsafeCast) {
        // Erase from the set if safe
        heapDynPointerSet.erase(it++);
        if (UnifiedMemSafe::VariableMapKeyType *GEPVar =
                dyn_cast_or_null<UnifiedMemSafe::VariableMapKeyType>(II->getOperand(0)))
        {
            if (heapDynPointerSet.find(GEPVar) != heapDynPointerSet.end()) {
                heapDynPointerSet.erase(GEPVar);
            }
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
    if (realDstType == nullptr) {
        realDstType = innerDstT;
    }

    // Check if its an unsafe cast
    bool isCastUnsafeCast = isPotentiallyUnsafeCast(innerSrcT, realSrcType, realDstType, innerDstT);
    if (!isCastUnsafeCast) {
        // Erase from the set if safe
        heapDynPointerSet.erase(it++);
        if (UnifiedMemSafe::VariableMapKeyType *CastVar =
                dyn_cast_or_null<UnifiedMemSafe::VariableMapKeyType>(II->getOperand(0)))
        {
            if (heapDynPointerSet.find(CastVar) != heapDynPointerSet.end()) {
                heapDynPointerSet.erase(CastVar);
            }
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
    // If operand is a CallInst, original code just erases from the set
    heapDynPointerSet.erase(it++);
    if (UnifiedMemSafe::VariableMapKeyType *CallVar =
            dyn_cast_or_null<UnifiedMemSafe::VariableMapKeyType>(op))
    {
        if (heapDynPointerSet.find(CallVar) != heapDynPointerSet.end()) {
            heapDynPointerSet.erase(CallVar);
        }
    }
    return false; // We erased the iterator
}


void CompatibleType::safeTypeCastAnalysis(
    std::map<const VariableMapKeyType *, VariableInfo> &heapDynPointerSet,
    const AnalysisState &TheState) 
{
    for (std::map<const UnifiedMemSafe::VariableMapKeyType *,
                  UnifiedMemSafe::VariableInfo>::iterator it = heapDynPointerSet.begin();
         it != heapDynPointerSet.end();)
    {
        const Instruction *instruction = dyn_cast_or_null<Instruction>(it->first);
        Instruction *dynInst = const_cast<llvm::Instruction *>(instruction);

        // If it's a CastInst, analyze pointer/unsafe casts:
        if (CastInst *II = dyn_cast_or_null<CastInst>(dynInst)) {
            Type *srcT = II->getSrcTy();
            Type *dstT = II->getDestTy();

            // If srcT is pointer, let's do deeper checks:
            if (srcT->isPointerTy()) {
                Type *innerSrcT = UnwrapPointer(srcT);
                Type *innerDstT = UnwrapPointer(dstT);

                // If the cast is suspicious (different pointer-level or non-integer),
                // we check all sub-cases:
                if (CountIndirections(srcT) != CountIndirections(dstT) ||
                    (!innerSrcT->isIntegerTy()) ||
                    (!innerDstT->isIntegerTy()))
                {
                    Value *op = II->getOperand(0);

                    // 1) LoadInst cast
                    if (LoadInst *loadInst = dyn_cast_or_null<LoadInst>(op)) {
                        if (!handleLoadCast(II, loadInst, heapDynPointerSet, it, innerSrcT, innerDstT, TheState)) {
                            // If the helper function erased the iterator, skip increment
                            continue;
                        }
                    }
                    // 2) GetElementPtrInst cast
                    else if (GetElementPtrInst *gepInst = dyn_cast_or_null<GetElementPtrInst>(op)) {
                        if (!handleGetElementPtrCast(II, gepInst, heapDynPointerSet, it, innerSrcT, innerDstT)) {
                            continue;
                        }
                    }
                    // 3) Another CastInst as operand
                    else if (CastInst *nestedCast = dyn_cast_or_null<CastInst>(op)) {
                        if (!handleCastInstCast(II, nestedCast, heapDynPointerSet, it, innerSrcT, innerDstT)) {
                            continue;
                        }
                    }
                    // 4) CallInst as operand
                    else if (isa<CallInst>(op)) {
                        if (!handleCallInstCast(II, op, heapDynPointerSet, it)) {
                            continue;
                        }
                    }
                }
            }
        }

        // Only increment if we did NOT erase `it`:
        if (heapDynPointerSet.size() != 0) {
            ++it;
        } else {
            break;
        }
    }

    errs() << GREEN << "Compatible-Type Cast Analysis:\t\t\t\t"
           << DETAIL << heapDynPointerSet.size() << NORMAL << "\n\n\n";
}


