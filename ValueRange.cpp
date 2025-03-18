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

#include "llvm/ADT/APSInt.h"
#include "llvm/Analysis/ConstantFolding.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"

#include <bitset>
#include <memory>
#include <string>

#include "DataflowAnalysis.h"
#include "ValueRange.hpp"

#include "Utils.hpp"
#include "program-dependence-graph/include/PTAWrapper.hh"
#include "program-dependence-graph/include/Graph.hh"
#include "program-dependence-graph/include/PDGEnums.hh"
#include "ProgramDependencyGraph.hh" 


using namespace llvm;
using std::string;
using std::unique_ptr;


enum class PossibleRangeValues {
    unknown,
    constant,
    infinity
};

struct RangeValue {
    PossibleRangeValues kind;
    llvm::ConstantInt *lvalue, *rvalue;

    RangeValue() : kind(PossibleRangeValues::unknown),
                   lvalue(nullptr),
                   rvalue(nullptr) {}


    bool isUnknown() const {
        return kind == PossibleRangeValues::unknown;
    }

    bool isInfinity() const {
        return kind == PossibleRangeValues::infinity;
    }

    bool isConstant() const {
        return kind == PossibleRangeValues::constant;
    }

    /**
     * Merge (meet) operator. Reorder checks to 
     *   short-circuit the common scenarios:
     *   1. Identical ranges => early return
     *   2. Either side is infinity => infinity
     *   3. Unknown merges with X => X (unless both are unknown)
     *   4. Otherwise both are constant => unify
     */
    RangeValue operator|(const RangeValue &other) const {
        // if already exactly the same (including both ∞, both unknown, or same constants)
        // Uncomment if needed:
        // llvm::errs() << "[RangeValue::operator|] Checking if identical.\n";
        if (*this == other) {
            // llvm::errs() << "[RangeValue::operator|] Short-circuit: identical ranges.\n";
            return *this;
        }

        // // llvm::errs() << "[RangeValue::operator|] Merging range kinds: " << (int)kind << " | " << (int)other.kind << "\n";

        // 1. If either side is infinity => result is infinity
        if (isInfinity() || other.isInfinity()) {
            RangeValue r;
            r.kind = PossibleRangeValues::infinity;
            return r;
        }

        // 2. If both unknown => still unknown
        if (isUnknown() && other.isUnknown()) {
            return RangeValue(); // Both unknown
        }

        // 3. If one is unknown => take the other
        if (isUnknown()) {
            return other;
        }
        if (other.isUnknown()) {
            return *this;
        }

        // 4. Otherwise, both are constant => unify the numeric range
        RangeValue r;
        r.kind = PossibleRangeValues::constant;

        // unify bit widths to 64 bits before comparisons
        APInt selfL = lvalue->getValue().sextOrTrunc(64);
        APInt selfR = rvalue->getValue().sextOrTrunc(64);
        APInt otherL = other.lvalue->getValue().sextOrTrunc(64);
        APInt otherR = other.rvalue->getValue().sextOrTrunc(64);

        // Take the smallest "left" bound
        if (selfL.slt(otherL)) {
            r.lvalue = lvalue;
        } else {
            r.lvalue = other.lvalue;
        }
        // Take the largest "right" bound
        if (selfR.sgt(otherR)) {
            r.rvalue = rvalue;
        } else {
            r.rvalue = other.rvalue;
        }

        return r;
    }

    /**
     * Equality check. 
     * - constant == constant if they have the same [lvalue, rvalue].
     * - infinity == infinity
     * - unknown == unknown
     */
    bool operator==(const RangeValue &other) const {
        // Uncomment if needed:
        // llvm::errs() << "[RangeValue::operator==] Checking equality.\n";

        if (kind != other.kind) {
            return false;
        }
        if (kind == PossibleRangeValues::constant) {
            // Compare underlying constants with unified bit widths
            APInt selfL = lvalue->getValue().sextOrTrunc(64);
            APInt selfR = rvalue->getValue().sextOrTrunc(64);
            APInt otherL = other.lvalue->getValue().sextOrTrunc(64);
            APInt otherR = other.rvalue->getValue().sextOrTrunc(64);
            return (selfL == otherL && selfR == otherR);
        }
        // If both unknown or both infinity => they match
        return true;
    }
};

RangeValue makeRange(LLVMContext &context, APInt &left, APInt &right) {
    //errs() << "makeRange" << "\n";
    RangeValue r;
    r.kind = PossibleRangeValues::constant;
    r.lvalue = ConstantInt::get(context, left);
    r.rvalue = ConstantInt::get(context, right);
    return r;
}

RangeValue infRange() {
     //errs() << "infRange" << "\n";
    RangeValue r;
    r.kind = PossibleRangeValues::infinity;
    return r;
}

using RangeState  = analysis::AbstractState<RangeValue>;
using RangeResult = analysis::DataflowResult<RangeValue>;

class RangeMeet : public analysis::Meet<RangeValue, RangeMeet> {
public:
    RangeValue
    meetPair(RangeValue &s1, RangeValue &s2) const {
        return s1 | s2;
    }
};

class RangeTransfer {
public:
    RangeValue getRangeFor(llvm::Value *v, RangeState &state) const {
         //errs() << "getRangeFor" << "\n";
        if (auto *constant = llvm::dyn_cast<llvm::ConstantInt>(v)) {
            RangeValue r;
            r.kind = PossibleRangeValues::constant;
            r.lvalue = r.rvalue = constant;
            return r;
        }
        return state[v];
    }

    RangeValue evaluateBinOP(llvm::BinaryOperator &binOp,
                             RangeState &state) const {
        // llvm::errs() << "[RangeTransfer::evaluateBinOP] " << binOp << "\n";
        auto *op1 = binOp.getOperand(0);
        auto *op2 = binOp.getOperand(1);

        auto range1 = getRangeFor(op1, state);
        auto range2 = getRangeFor(op2, state);

        // If either side is infinity => result is infinity
        if (range1.isInfinity() || range2.isInfinity()) {
            // llvm::errs() << "  => Infinity.\n";
            return infRange();
        }

        // If both unknown => result is unknown (by default)
        if (range1.isUnknown() && range2.isUnknown()) {
            // llvm::errs() << "  => Both unknown => unknown.\n";
            return RangeValue();
        }

        // If either side unknown, or if not both constant => unknown
        if (!(range1.isConstant() && range2.isConstant())) {
            // llvm::errs() << "  => One side unknown or not constant => unknown.\n";
            return RangeValue();
        }

        // Both are constant => unify bit widths
        APInt l1 = range1.lvalue->getValue().sextOrTrunc(64);
        APInt r1 = range1.rvalue->getValue().sextOrTrunc(64);
        APInt l2 = range2.lvalue->getValue().sextOrTrunc(64);
        APInt r2 = range2.rvalue->getValue().sextOrTrunc(64);

        auto &context = range1.lvalue->getContext();
        auto opcode = binOp.getOpcode();

        switch (opcode) {
        case Instruction::Add: {
            bool ofL, ofR;
            auto ll = l1.sadd_ov(l2, ofL);
            auto rr = r1.sadd_ov(r2, ofR);
            if (ofL || ofR) {
                // llvm::errs() << "  => Overflow in Add => infRange.\n";
                return infRange();
            }
            return makeRange(context, ll, rr);
        }
        case Instruction::Sub: {
            bool ofL, ofR;
            auto ll = l1.ssub_ov(r2, ofL);
            auto rr = r1.ssub_ov(l2, ofR);
            if (ofL || ofR) {
                // llvm::errs() << "  => Overflow in Sub => infRange.\n";
                return infRange();
            }
            return makeRange(context, ll, rr);
        }
        case Instruction::Mul: {
            SmallVector<APInt, 4> candidates;
            bool of[4];
            candidates.push_back(l1.smul_ov(l2, of[0]));
            candidates.push_back(l1.smul_ov(r2, of[1]));
            candidates.push_back(r1.smul_ov(l2, of[2]));
            candidates.push_back(r1.smul_ov(r2, of[3]));
            for (auto o : of) {
                if (o) {
                    // llvm::errs() << "  => Overflow in Mul => infRange.\n";
                    return infRange();
                }
            }
            auto mn = candidates[0];
            auto mx = candidates[0];
            for (auto &val : candidates) {
                if (val.slt(mn)) mn = val;
                if (val.sgt(mx)) mx = val;
            }
            return makeRange(context, mn, mx);
        }
        case Instruction::SDiv: {
            SmallVector<APInt, 4> candidates;
            bool of[4];
            candidates.push_back(l1.sdiv_ov(l2, of[0]));
            candidates.push_back(l1.sdiv_ov(r2, of[1]));
            candidates.push_back(r1.sdiv_ov(l2, of[2]));
            candidates.push_back(r1.sdiv_ov(r2, of[3]));
            for (auto o : of) {
                if (o) {
                    // llvm::errs() << "  => Overflow in SDiv => infRange.\n";
                    return infRange();
                }
            }
            auto mn = candidates[0];
            auto mx = candidates[0];
            for (auto &val : candidates) {
                if (val.slt(mn)) mn = val;
                if (val.sgt(mx)) mx = val;
            }
            return makeRange(context, mn, mx);
        }
        case Instruction::UDiv: {
            auto ll = r1.udiv(l2);
            auto rr = l1.udiv(r2);
            APInt minVal = (ll.ult(rr) ? ll : rr);
            APInt maxVal = (ll.ugt(rr) ? ll : rr);
            return makeRange(context, minVal, maxVal);
        }
        default:
            // llvm::errs() << "  => Unhandled op => infRange.\n";
            return infRange();
        }
    }

    RangeValue evaluateCast(llvm::CastInst &castOp, RangeState &state) const {
        auto *op = castOp.getOperand(0);
        auto value = getRangeFor(op, state);

        if (value.isConstant()) {
            auto &layout = castOp.getModule()->getDataLayout();
            auto x = ConstantFoldCastOperand(castOp.getOpcode(), value.lvalue,
                                            castOp.getDestTy(), layout);
            auto y = ConstantFoldCastOperand(castOp.getOpcode(), value.rvalue,
                                            castOp.getDestTy(), layout);

            if (llvm::isa<llvm::ConstantExpr>(x) || llvm::isa<llvm::ConstantExpr>(y)) {
                return infRange(); // Cast produced a non-constant expression
            } else {
                auto *cix = dyn_cast<ConstantInt>(x);
                auto *ciy = dyn_cast<ConstantInt>(y);

                if (cix && ciy) {
                    // Valid constants
                    RangeValue r;
                    r.kind = PossibleRangeValues::constant;
                    r.lvalue = cix;
                    r.rvalue = ciy;
                    return r;
                } else {
                    // Cast failed to produce valid ConstantInt
                    return infRange();
                }
            }
        } else {
            RangeValue r;
            r.kind = value.kind;
            return r;
        }
    }

    void
    operator()(llvm::Value &i, RangeState &state) {

        if (auto *constant = llvm::dyn_cast<llvm::ConstantInt>(&i)) {
            RangeValue r;
            r.kind = PossibleRangeValues::constant;
            r.lvalue = r.rvalue = constant;
            state[&i] = r;
        }
        else if (auto *binOp = llvm::dyn_cast<llvm::BinaryOperator>(&i)) {
            state[binOp] = evaluateBinOP(*binOp, state);
        }
        else if (auto *castOp = llvm::dyn_cast<llvm::CastInst>(&i)) {
            state[castOp] = evaluateCast(*castOp, state);
        }
        else {
            state[&i].kind = PossibleRangeValues::infinity;
        }
    }
};

void valueRangeAnalysis(Module *M, std::map<const UnifiedMemSafe::VariableMapKeyType *, UnifiedMemSafe::VariableInfo>heapSeqPointerSet, UnifiedMemSafe::AnalysisState TheState){
    // I removed the print messages for cleanness in this pass
    // If you want to print, e.g., declaration and use sites, please refer to DataGuard Repository for the statements
    auto *mainFunction = M->getFunction("main");
    if (!mainFunction) {
       errs() << RED << "Unable to find main function for Value-Range Analysis! Skipping!\n" << NORMAL;
       return;
    }
    
    using Value    = RangeValue;
    using Transfer = RangeTransfer;
    using Meet     = RangeMeet;
    using Analysis = analysis::ForwardDataflowAnalysis<Value, Transfer, Meet>;
    Analysis analysis{*M, mainFunction};
    auto results = analysis.computeForwardDataflow();

    std::map<const UnifiedMemSafe::VariableMapKeyType *, UnifiedMemSafe::VariableInfo> heapUnsafeSeqPointerSet;
    
    for (auto & [ctxt, contextResults] : results) {
        for (auto & [function, rangeStates] : contextResults) {
            for (auto &valueStatePair : rangeStates) {
                auto *inst = llvm::dyn_cast<llvm::GetElementPtrInst>(valueStatePair.first);
                if (!inst) {
                    continue;
                }
                if (heapSeqPointerSet.find(inst) != heapSeqPointerSet.end()){
                    auto &state = analysis::getIncomingState(rangeStates, *inst);
                    Type *type = cast<PointerType>(
                            cast<GetElementPtrInst>(inst)->getPointerOperandType())->getElementType();
                    auto pointerTy = dyn_cast_or_null<PointerType>(type);
                    auto arrayTy = dyn_cast_or_null<ArrayType>(type);
                    auto structTy = dyn_cast_or_null<StructType>(type);
                    
                    if(!arrayTy && !structTy){
                        if(UnifiedMemSafe::VariableMapKeyType *vmkt = dyn_cast_or_null<UnifiedMemSafe::VariableMapKeyType>(inst)){
                            // Check if vmktinfo is non-null
                            if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                if(!vmktinfo){
                                    // vmktinfo is NULL
                                    continue;
                                }
                                if (auto *gepInst = dyn_cast<llvm::GetElementPtrInst>(inst)) {
                                    // Check the number of operands in the GEP instruction
                                    auto index = (gepInst->getNumOperands() > 2) 
                                                ? gepInst->getOperand(2)  // Use the third operand if more than 2 operands
                                                : gepInst->getOperand(1); // Use the second operand otherwise

                                    auto constant = dyn_cast<ConstantInt>(index);
                                    if (constant) {
                                        // If the offset is constant
                                        auto *sizeCI = dyn_cast<ConstantInt>(vmktinfo->size);
                                        if(!sizeCI) {
                                            // vmktinfo->size is not a ConstantInt
                                            continue;
                                        }
                                        int underlyingSize = sizeCI->getSExtValue();
                                        if (!constant->isNegative() && underlyingSize > 0) {
                                            // Offset is within bounds, discard this case
                                            continue;
                                        } else {
                                            // Offset is out of bounds, add to the set
                                            heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                        }
                                    } else {
                                        // If the index is not constant, add to the set
                                        heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                    }
                                }
                            }
                        }
                        continue;
                    }
                    else if(arrayTy){
                        auto size = arrayTy->getNumElements();
                        auto elmtTy = arrayTy->getElementType();
                        auto &layout = M->getDataLayout();
                        auto numBytes = layout.getTypeAllocSize(arrayTy);
                        auto elmtBytes = layout.getTypeAllocSize(elmtTy);
                        llvm::Value* index;
                        if(inst->getNumOperands() > 2)
                            index = inst->getOperand(2);
                        else {
                            index = inst->getOperand(1);
                        }
                        auto constant = dyn_cast<ConstantInt>(index);
                        if (constant) {
                            if (!constant->isNegative() && !constant->uge(size)) {
                                if (numBytes >= ((int64_t) constant->getValue().getLimitedValue() * elmtBytes)){}
                                else {
                                    if(UnifiedMemSafe::VariableMapKeyType *vmkt = dyn_cast_or_null<UnifiedMemSafe::VariableMapKeyType>(inst)){
                                        if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                            UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                            heapUnsafeSeqPointerSet[vmkt]=*vmktinfo;
                                        }
                                    }
                                }
                            }
                        }
                        else {
                            auto &rangeValue = state[index];
                            if (rangeValue.isUnknown() ||
                                rangeValue.isInfinity() ||
                                !rangeValue.lvalue || !rangeValue.rvalue || 
                                rangeValue.lvalue->isNegative() ||
                                rangeValue.rvalue->uge(size)) {
                                if(UnifiedMemSafe::VariableMapKeyType *vmkt = dyn_cast_or_null<UnifiedMemSafe::VariableMapKeyType>(inst)){
                                    if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                        UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                        heapUnsafeSeqPointerSet[vmkt]=*vmktinfo;
                                    }
                                }
                            }
                        }
                    }
                    
                    else if(structTy){
                        auto size = structTy->getNumElements();
                        auto &layout = M->getDataLayout();
                        auto numBytes = layout.getTypeAllocSize(structTy);
                        llvm::Value* index;
                        if(inst->getNumOperands() > 2)
                            index = inst->getOperand(2);
                        else {
                            index = inst->getOperand(1);
                        }
                        
                        const llvm::StructLayout* structureLayout = layout.getStructLayout(structTy);
                        auto constant = dyn_cast<ConstantInt>(index);
                        if (constant) {
                            auto intIndex = (uint64_t)constant->getValue().getLimitedValue();
                            if(intIndex < size){
                                auto offset = structureLayout->getElementOffset(intIndex);
                                if (!constant->isNegative() && !constant->uge(size)) {
                                    if (numBytes >= offset){}
                                    else{
                                        if(UnifiedMemSafe::VariableMapKeyType *vmkt = dyn_cast_or_null<UnifiedMemSafe::VariableMapKeyType>(inst)){
                                            if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                                UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                                heapUnsafeSeqPointerSet[vmkt]=*vmktinfo;
                                            }
                                        }
                                    } 
                                }  
                            }
                            else{
                                if(UnifiedMemSafe::VariableMapKeyType *vmkt = dyn_cast_or_null<UnifiedMemSafe::VariableMapKeyType>(inst)){
                                    if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                        UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                        heapUnsafeSeqPointerSet[vmkt]=*vmktinfo;
                                    }
                                }
                            }
                        }
                        else {
                            auto &rangeValue = state[index];
                            if (rangeValue.isUnknown() ||
                                rangeValue.isInfinity() ||
                                !rangeValue.lvalue || !rangeValue.rvalue ||
                                rangeValue.lvalue->isNegative() ||
                                rangeValue.rvalue->uge(size)) {
                                if (rangeValue.isInfinity() || rangeValue.isUnknown()) {
                                    if(UnifiedMemSafe::VariableMapKeyType *vmkt = dyn_cast_or_null<UnifiedMemSafe::VariableMapKeyType>(inst)){
                                        if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                            UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                            heapUnsafeSeqPointerSet[vmkt]=*vmktinfo;
                                        }
                                    }
                                }
                            }
                        }
                    }
                    else{
                        // Additional processing can be added here.
                    }
                }           
            }
        }
    }
    errs() << GREEN << "Unsafe Seq Pointer After Value Range Analysis:\t\t" << DETAIL << heapUnsafeSeqPointerSet.size()<< NORMAL << "\n"; 

    /*for (const auto &pair : heapUnsafeSeqPointerSet) {
        const llvm::Value *key = pair.first;

        // Use llvm::dyn_cast to cast the key to an Instruction
        if (const llvm::Instruction *instruction = llvm::dyn_cast<llvm::Instruction>(key)) {
            // Print the instruction using LLVM's print method
            instruction->print(llvm::outs());
            llvm::outs() << "\n";
        } else {
            std::cerr << "Key cannot be cast to LLVM Instruction." << std::endl;
        }
    }
    */
}
