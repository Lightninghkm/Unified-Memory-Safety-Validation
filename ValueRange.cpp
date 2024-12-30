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

    RangeValue
    operator|(const RangeValue &other) const {
        RangeValue r;
        if (isUnknown() || other.isUnknown()) {
            if (isUnknown()) {
                return other;
            }
            else {
                return *this;
            }
        }
        else if (isInfinity() || other.isInfinity()) {
            r.kind = PossibleRangeValues::infinity;
            return r;
        }
        else {
            auto &selfL = lvalue->getValue();
            auto &selfR = rvalue->getValue();
            auto &otherL = (other.lvalue)->getValue();
            auto &otherR = (other.rvalue)->getValue();

            r.kind = PossibleRangeValues::constant;
            if (selfL.slt(otherL)) {
                r.lvalue = lvalue;
            }
            else {
                r.lvalue = other.lvalue;
            }

            if (selfR.sgt(otherR)) {
                r.rvalue = rvalue;
            }
            else {
                r.rvalue = other.rvalue;
            }
            return r;
        }
    }

    bool
    operator==(const RangeValue &other) const {
        if (kind == PossibleRangeValues::constant &&
            other.kind == PossibleRangeValues::constant) {
            auto &selfL = lvalue->getValue();
            auto &selfR = rvalue->getValue();
            auto &otherL = (other.lvalue)->getValue();
            auto &otherR = (other.rvalue)->getValue();
            return selfL == otherL && selfR == otherR;
        }
        else {
            return kind == other.kind;
        }
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

        // errs() << "evaluateBinop" << "\n";
        auto *op1 = binOp.getOperand(0);
        auto *op2 = binOp.getOperand(1);
        auto range1 = getRangeFor(op1, state);
        auto range2 = getRangeFor(op2, state);

        if (range1.isConstant() && range2.isConstant()) {
            auto l1 = range1.lvalue->getValue();
            auto r1 = range1.rvalue->getValue();
            auto l2 = range2.lvalue->getValue();
            auto r2 = range2.rvalue->getValue();

            auto &context = (range1.lvalue)->getContext();
            auto opcode = binOp.getOpcode();

            if (opcode == Instruction::Add) {
                bool ofl, ofr;
                auto l = l1.sadd_ov(l2, ofl);
                auto r = r1.sadd_ov(r2, ofr);
                if (ofl || ofr) {
                    return infRange();
                }
                else {
                    return makeRange(context, l, r);
                }
            }
            else if (opcode == Instruction::Sub) {
                bool ofl, ofr;
                auto l = l1.ssub_ov(r2, ofl);
                auto r = r1.ssub_ov(l2, ofr);
                if (ofl || ofr) {
                    return infRange();
                }
                else {
                    return makeRange(context, l, r);
                }
            }
            else if (opcode == Instruction::Mul) {
                SmallVector<APInt, 4> candidates;
                bool ofFlags[4];
                candidates.push_back(l1.smul_ov(l2, ofFlags[0]));
                candidates.push_back(l1.smul_ov(r2, ofFlags[1]));
                candidates.push_back(r1.smul_ov(l2, ofFlags[2]));
                candidates.push_back(r1.smul_ov(r2, ofFlags[3]));
                for (auto of:ofFlags) {
                    if (of) {
                        return infRange();
                    }
                }
                auto max = candidates[0];
                for (auto &x : candidates) {
                    if (x.sgt(max)) {
                        max = x;
                    }
                }
                auto min = candidates[0];
                for (auto &x : candidates) {
                    if (x.slt(min)) {
                        min = x;
                    }
                }
                return makeRange(context, min, max);
            }
            else if (opcode == Instruction::SDiv) {
                if (l2.isNegative() && r2.isStrictlyPositive()) {
                    auto abs1 = l1.abs();
                    auto abs2 = r1.abs();
                    auto abs = abs1.sgt(abs2) ? abs1 : abs2;
                    APInt l(abs);
                    l.flipAllBits();
                    ++l;
                    return makeRange(context, l, abs);
                }
                else {
                    SmallVector<APInt, 4> candidates;
                    bool ofFlags[4];
                    candidates.push_back(l1.sdiv_ov(l2, ofFlags[0]));
                    candidates.push_back(l1.sdiv_ov(r2, ofFlags[1]));
                    candidates.push_back(r1.sdiv_ov(l2, ofFlags[2]));
                    candidates.push_back(r1.sdiv_ov(r2, ofFlags[3]));
                    for (auto of:ofFlags) {
                        if (of) {
                            return infRange();
                        }
                    }
                    auto max = candidates[0];
                    for (auto &x : candidates) {
                        if (x.sgt(max)) {
                            max = x;
                        }
                    }
                    auto min = candidates[0];
                    for (auto &x : candidates) {
                        if (x.slt(min)) {
                            min = x;
                        }
                    }
                    return makeRange(context, min, max);
                }
            }
            else if (opcode == Instruction::UDiv) {
                auto l = r1.udiv(l2);
                auto r = l1.udiv(r2);
                return makeRange(context, l, r);
            }
            else {
                // todo: fill in
                return infRange();
            }
        }
        else if (range1.isInfinity() || range2.isInfinity()) {
            RangeValue r;
            r.kind = PossibleRangeValues::infinity;
            return r;
        }
        else {
            RangeValue r;
            return r;
        }
    }

    RangeValue evaluateCast(llvm::CastInst &castOp, RangeState &state) const {
         //errs() << "evaluateCast" << "\n";
        auto *op = castOp.getOperand(0);
        auto value = getRangeFor(op, state);

        if (value.isConstant()) {
            auto &layout = castOp.getModule()->getDataLayout();
            auto x = ConstantFoldCastOperand(castOp.getOpcode(), value.lvalue,
                                             castOp.getDestTy(), layout);
            auto y = ConstantFoldCastOperand(castOp.getOpcode(), value.rvalue,
                                             castOp.getDestTy(), layout);
            if (llvm::isa<llvm::ConstantExpr>(x) || llvm::isa<llvm::ConstantExpr>(y)) {
                return infRange();
            }
            else {
                RangeValue r;
                auto *cix = dyn_cast<ConstantInt>(x);
                auto *ciy = dyn_cast<ConstantInt>(y);
                r.kind = PossibleRangeValues::constant;
                r.lvalue = cix;
                r.rvalue = ciy;
                return r;
            }
        }
        else {
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
                            if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                if (auto *gepInst = dyn_cast<llvm::GetElementPtrInst>(inst)) {
                                    // Check the number of operands in the GEP instruction
                                    auto index = (gepInst->getNumOperands() > 2) 
                                                ? gepInst->getOperand(2)  // Use the third operand if more than 2 operands
                                                : gepInst->getOperand(1); // Use the second operand otherwise

                                    auto constant = dyn_cast<ConstantInt>(index);
                                    if (constant) {
                                        // If the offset is constant
                                        int underlyingSize = dyn_cast<ConstantInt>(vmktinfo->size)->getSExtValue();
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
				        
				        else{
							index = inst->getOperand(1);
				        }
						auto constant = dyn_cast<ConstantInt>(index);
						if (constant) {
						    if (!constant->isNegative() && !constant->uge(size)) {
				                if (numBytes >= ((int64_t) constant->getValue().getLimitedValue() * elmtBytes)){}
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
						else {
						    auto &rangeValue = state[index];
						    if (rangeValue.isUnknown() ||
						        rangeValue.isInfinity() ||
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
				        
				        else{
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
		            }
				}           
            }
        }
    }
    errs() << GREEN << "Unsafe Seq Pointer After Value Range:\t\t\t" << DETAIL << heapUnsafeSeqPointerSet.size()<< NORMAL << "\n"; 

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
