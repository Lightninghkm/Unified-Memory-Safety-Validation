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
#include <unordered_map> // for storeHappened

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


// A small bounding threshold to avoid unbounded expansions
static const uint64_t MAX_RANGE_SIZE = 1024;

// Check if pointer is local alloca
static bool isLocalAllocaPointer(Value *ptr) {
    ptr = ptr->stripPointerCasts();
    if (auto *AI = dyn_cast<AllocaInst>(ptr)) {
        return true;
    }
    return false;
}

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

    bool isUnknown()  const { return kind == PossibleRangeValues::unknown; }
    bool isInfinity() const { return kind == PossibleRangeValues::infinity; }
    bool isConstant() const { return kind == PossibleRangeValues::constant; }

    // The original operator|
    RangeValue operator|(const RangeValue &other) const {
        RangeValue r;
        if (isUnknown() || other.isUnknown()) {
            if (isUnknown()) {
                return other;
            } else {
                return *this;
            }
        } else if (isInfinity() || other.isInfinity()) {
            r.kind = PossibleRangeValues::infinity;
            return r;
        } else {
            auto &selfL = lvalue->getValue();
            auto &selfR = rvalue->getValue();
            auto &otherL = other.lvalue->getValue();
            auto &otherR = other.rvalue->getValue();

            r.kind = PossibleRangeValues::constant;
            if (selfL.slt(otherL)) {
                r.lvalue = lvalue;
            } else {
                r.lvalue = other.lvalue;
            }
            if (selfR.sgt(otherR)) {
                r.rvalue = rvalue;
            } else {
                r.rvalue = other.rvalue;
            }
        }
        // bounding
        if (r.kind == PossibleRangeValues::constant && r.lvalue && r.rvalue) {
            APInt L = r.lvalue->getValue();
            APInt R = r.rvalue->getValue();
            APInt diff = (R.sgt(L) ? R - L : L - R);
            if (diff.ugt(MAX_RANGE_SIZE)) {
                r.kind   = PossibleRangeValues::infinity;
                r.lvalue = nullptr;
                r.rvalue = nullptr;
            }
        }
        return r;
    }

    bool operator==(const RangeValue &other) const {
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
    RangeValue r;
    r.kind   = PossibleRangeValues::constant;
    r.lvalue = ConstantInt::get(context, left);
    r.rvalue = ConstantInt::get(context, right);
    return r;
}

RangeValue infRange() {
    RangeValue r;
    r.kind = PossibleRangeValues::infinity;
    return r;
}

using RangeState  = analysis::AbstractState<RangeValue>;
using RangeResult = analysis::DataflowResult<RangeValue>;

// The meet: reuses operator|( ) from RangeValue
class RangeMeet : public analysis::Meet<RangeValue, RangeMeet> {
public:
    RangeValue
    meetPair(RangeValue &s1, RangeValue &s2) const {
        return s1 | s2;
    }
};

class RangeTransfer {
public:
    // ADDED: We track pointers that have been stored to once, so we skip merging on subsequent stores
    // "only consider the most recent one"
    // Key = pointer Value*, Value = boolean
    // Once we store once, we set storeHappened[ptr]=true
    // Next time we store => we just overwrite
    mutable std::unordered_map<llvm::Value*, bool> storeHappened;

    void operator()(llvm::Value &I, RangeState &state) {
        // If store => handle
        if (auto *st = dyn_cast<StoreInst>(&I)) {
            handleStore(*st, state);
            return;
        }
        // If load => handle
        if (auto *ld = dyn_cast<LoadInst>(&I)) {
            handleLoad(*ld, state);
            return;
        }

        // Original logic
        if (auto *constant = llvm::dyn_cast<llvm::ConstantInt>(&I)) {
            RangeValue r;
            r.kind = PossibleRangeValues::constant;
            r.lvalue = r.rvalue = constant;
            state[&I] = r;
        }
        else if (auto *binOp = llvm::dyn_cast<llvm::BinaryOperator>(&I)) {
            state[binOp] = evaluateBinOP(*binOp, state);
        }
        else if (auto *castOp = llvm::dyn_cast<llvm::CastInst>(&I)) {
            state[castOp] = evaluateCast(*castOp, state);
        }
        else {
            state[&I].kind = PossibleRangeValues::infinity;
        }
    }

    RangeValue getRangeFor(llvm::Value *v, RangeState &state) const {
        if (auto *cint = dyn_cast<ConstantInt>(v)) {
            RangeValue r;
            r.kind = PossibleRangeValues::constant;
            r.lvalue = r.rvalue = cint;
            return r;
        }
        return state[v];
    }

    RangeValue evaluateBinOP(llvm::BinaryOperator &binOp,
                             RangeState &state) const {
        auto *op1 = binOp.getOperand(0);
        auto *op2 = binOp.getOperand(1);
        auto range1 = getRangeFor(op1, state);
        auto range2 = getRangeFor(op2, state);

        if (range1.isConstant() && range2.isConstant()) {
            auto l1 = range1.lvalue->getValue();
            auto r1 = range1.rvalue->getValue();
            auto l2 = range2.lvalue->getValue();
            auto r2 = range2.rvalue->getValue();

            auto &ctx = (range1.lvalue)->getContext();
            auto opcode = binOp.getOpcode();

            if (opcode == Instruction::Add) {
                bool of1, of2;
                APInt sum1 = l1.sadd_ov(l2, of1);
                APInt sum2 = r1.sadd_ov(r2, of2);
                if (of1 || of2) {
                    return infRange();
                }
                return makeRange(ctx, sum1, sum2);
            }
            // For simplicity, other ops => your original logic
            else if (opcode == Instruction::Sub) {
                bool of1, of2;
                APInt a = l1.ssub_ov(r2, of1);
                APInt b = r1.ssub_ov(l2, of2);
                if (of1 || of2) {
                    return infRange();
                }
                return makeRange(ctx, a, b);
            }
            else if (opcode == Instruction::Mul) {
                SmallVector<APInt, 4> candidates;
                bool ofFlags[4];
                candidates.push_back(l1.smul_ov(l2, ofFlags[0]));
                candidates.push_back(l1.smul_ov(r2, ofFlags[1]));
                candidates.push_back(r1.smul_ov(l2, ofFlags[2]));
                candidates.push_back(r1.smul_ov(r2, ofFlags[3]));
                for (auto flag: ofFlags) {
                    if (flag) return infRange();
                }
                APInt maxv = candidates[0];
                APInt minv = candidates[0];
                for (auto &c : candidates) {
                    if (c.sgt(maxv)) maxv = c;
                    if (c.slt(minv)) minv = c;
                }
                return makeRange(ctx, minv, maxv);
            }
            else if (opcode == Instruction::SDiv) {
                // your original sdiv logic
                if (l2.isNegative() && r2.isStrictlyPositive()) {
                    auto abs1 = l1.abs();
                    auto abs2 = r1.abs();
                    auto abs = abs1.sgt(abs2) ? abs1 : abs2;
                    APInt ll(abs);
                    ll.flipAllBits();
                    ++ll;
                    return makeRange(ctx, ll, abs);
                }
                else {
                    SmallVector<APInt, 4> cands;
                    bool fl[4];
                    cands.push_back(l1.sdiv_ov(l2, fl[0]));
                    cands.push_back(l1.sdiv_ov(r2, fl[1]));
                    cands.push_back(r1.sdiv_ov(l2, fl[2]));
                    cands.push_back(r1.sdiv_ov(r2, fl[3]));
                    for (auto f: fl) {
                        if (f) return infRange();
                    }
                    APInt mx = cands[0], mn = cands[0];
                    for (auto &cc: cands) {
                        if (cc.sgt(mx)) mx = cc;
                        if (cc.slt(mn)) mn = cc;
                    }
                    return makeRange(ctx, mn, mx);
                }
            }
            else if (opcode == Instruction::UDiv) {
                APInt a = r1.udiv(l2);
                APInt b = l1.udiv(r2);
                return makeRange(ctx, a, b);
            }
            else {
                return infRange();
            }
        }
        else if (range1.isInfinity() || range2.isInfinity()) {
            RangeValue rr;
            rr.kind = PossibleRangeValues::infinity;
            return rr;
        }
        else {
            // fallback => unknown
            RangeValue rr;
            return rr;
        }
    }

    RangeValue evaluateCast(llvm::CastInst &Cst, RangeState &state) const {
        auto valRange = getRangeFor(Cst.getOperand(0), state);
        if (!valRange.isConstant()) {
            RangeValue r;
            r.kind = valRange.kind;
            return r;
        }
        auto &layout = Cst.getModule()->getDataLayout();
        Constant *cl = ConstantFoldCastOperand(Cst.getOpcode(), valRange.lvalue,
                                               Cst.getDestTy(), layout);
        Constant *cr = ConstantFoldCastOperand(Cst.getOpcode(), valRange.rvalue,
                                               Cst.getDestTy(), layout);
        if (!cl || !cr || isa<ConstantExpr>(cl) || isa<ConstantExpr>(cr)) {
            return infRange();
        }
        auto *cli = dyn_cast<ConstantInt>(cl);
        auto *cri = dyn_cast<ConstantInt>(cr);
        if (!cli || !cri) {
            return infRange();
        }
        RangeValue rv;
        rv.kind   = PossibleRangeValues::constant;
        rv.lvalue = cli;
        rv.rvalue = cri;
        return rv;
    }

private:
    void handleStore(StoreInst &SI, RangeState &state) const {
        llvm::Value *val = SI.getValueOperand();
        llvm::Value *ptr = SI.getPointerOperand();

        if (isLocalAllocaPointer(ptr)) {
            // If we've stored to 'ptr' before, do not merge; just overwrite
            // "only consider the most recent one"
            auto it = storeHappened.find(ptr);
            // read the range of 'val'
            auto valRange = getRangeFor(val, state);

            if (it == storeHappened.end()) {
                // first time storing
                storeHappened[ptr] = true;
                state[ptr] = valRange;
            } else {
                // subsequent store => just overwrite
                // no merges with old state
                state[ptr] = valRange;
            }
        }
    }

    void handleLoad(LoadInst &LI, RangeState &state) const {
        llvm::Value *ptr = LI.getPointerOperand();
        if (isLocalAllocaPointer(ptr)) {
            auto it = state.find(ptr);
            if (it != state.end()) {
                state[&LI] = it->second;
                return;
            }
        }
        // fallback => unknown or infinity
        state[&LI].kind = PossibleRangeValues::infinity;
    }
};

void valueRangeAnalysis(Module *M,
    std::map<const UnifiedMemSafe::VariableMapKeyType *, UnifiedMemSafe::VariableInfo>heapSeqPointerSet,
    UnifiedMemSafe::AnalysisState TheState){

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
                                    auto index = (gepInst->getNumOperands() > 2) 
                                                ? gepInst->getOperand(2)
                                                : gepInst->getOperand(1);

                                    auto constant = dyn_cast<ConstantInt>(index);
                                    if (constant) {
                                        int underlyingSize = dyn_cast<ConstantInt>(vmktinfo->size)->getSExtValue();
                                        if (!constant->isNegative() && underlyingSize > 0) {
                                            continue;
                                        } else {
                                            heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                        }
                                    } else {
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
    errs() << GREEN << "Unsafe Seq Pointer After Value Range Analysis:\t\t" << DETAIL << heapUnsafeSeqPointerSet.size()<< NORMAL << "\n"; 
}
