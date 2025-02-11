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
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DebugLoc.h"
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

#include "llvm/Support/CommandLine.h"

static llvm::cl::opt<bool> EnableDebug("enable-debug", llvm::cl::desc("Enable debug output"), llvm::cl::init(false));
#define DEBUG_PRINT(x) if (EnableDebug) { llvm::errs() << x << "\n"; };

using namespace llvm;
using std::string;
using std::unique_ptr;

// A small bounding threshold to avoid unbounded expansions
static const uint64_t MAX_RANGE_SIZE = 1024;

// ----------------------------------------------------------------------
// ORIGINAL: Check if pointer is local alloca
// ----------------------------------------------------------------------
static bool isLocalAllocaPointer(Value *ptr) {
    ptr = ptr->stripPointerCasts();
    if (auto *AI = dyn_cast<AllocaInst>(ptr)) {
        return true;
    }
    return false;
}

// ----------------------------------------------------------------------
// UPDATED: Check if pointer is a call to malloc(...). For calls with
//          a non-constant size, we still recognize it as a malloc call
//          but return `nbytes = 0` to indicate unknown size.
// ----------------------------------------------------------------------
static bool isKnownMallocCall(llvm::Value *v, uint64_t &nbytes) {
    if (!v) return false;
    v = v->stripPointerCasts();

    auto *call = dyn_cast<CallBase>(v);
    if (!call) return false;
    Function *callee = call->getCalledFunction();
    if (!callee) return false;
    if (callee->getName() != "malloc") return false;
    // Update the logic here to handle customized allocation wrappers

    if (call->arg_size() < 1) return false;
    if (auto *cint = dyn_cast<ConstantInt>(call->getArgOperand(0))) {
        // Update here as well to reflect the size
        nbytes = cint->getZExtValue();
        DEBUG_PRINT("Detected malloc call with size: " << nbytes);
    } else {
        // Non-constant allocation size => still recognized as malloc
        nbytes = 0; // Use 0 as a sentinel for "unknown" or variable size
        DEBUG_PRINT("Detected malloc call with non-constant size; setting nbytes=0 to indicate unknown size.");
    }
    return true;
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

    // ----------------------------------------------------------------------
    // We unify all APInt bit widths here to 64 bits before comparing or merging
    // ----------------------------------------------------------------------

    bool operator==(const RangeValue &other) const {
        if (kind == PossibleRangeValues::constant &&
            other.kind == PossibleRangeValues::constant) {
            // Ensure both sides have the same bit width (64) before comparison
            APInt selfL = lvalue->getValue().sextOrTrunc(64);
            APInt selfR = rvalue->getValue().sextOrTrunc(64);
            APInt otherL = other.lvalue->getValue().sextOrTrunc(64);
            APInt otherR = other.rvalue->getValue().sextOrTrunc(64);
            return selfL == otherL && selfR == otherR;
        }
        else {
            return kind == other.kind;
        }
    }

    // The original operator|, but we unify bit widths before any APInt operation:
    RangeValue operator|(const RangeValue &other) const {
        RangeValue r;
        if (isUnknown() || other.isUnknown()) {
            if (isUnknown()) {
                DEBUG_PRINT("Merging with unknown range. Result is other range.");
                return other;
            } else {
                DEBUG_PRINT("Merging with unknown range. Result is this range.");
                return *this;
            }
        } else if (isInfinity() || other.isInfinity()) {
            DEBUG_PRINT("Merging with infinity range. Result is infinity.");
            r.kind = PossibleRangeValues::infinity;
            return r;
        } else {
            // Unify to 64 bits
            APInt selfL = lvalue->getValue().sextOrTrunc(64);
            APInt selfR = rvalue->getValue().sextOrTrunc(64);
            APInt otherL = other.lvalue->getValue().sextOrTrunc(64);
            APInt otherR = other.rvalue->getValue().sextOrTrunc(64);

            r.kind = PossibleRangeValues::constant;
            if (selfL.slt(otherL)) {
                r.lvalue = lvalue;
                DEBUG_PRINT("Lower bound updated to " << selfL);
            } else {
                r.lvalue = other.lvalue;
                DEBUG_PRINT("Lower bound updated to " << otherL);
            }
            if (selfR.sgt(otherR)) {
                r.rvalue = rvalue;
                DEBUG_PRINT("Upper bound updated to " << selfR);
            } else {
                r.rvalue = other.rvalue;
                DEBUG_PRINT("Upper bound updated to " << otherR);
            }
        }
        // bounding
        if (r.kind == PossibleRangeValues::constant && r.lvalue && r.rvalue) {
            APInt L = r.lvalue->getValue().sextOrTrunc(64);
            APInt R = r.rvalue->getValue().sextOrTrunc(64);
            APInt diff = (R.sgt(L) ? R - L : L - R);
            DEBUG_PRINT("Range difference: " << diff);
            if (diff.ugt(MAX_RANGE_SIZE)) {
                DEBUG_PRINT("Range exceeds MAX_RANGE_SIZE. Setting to infinity.");
                r.kind   = PossibleRangeValues::infinity;
                r.lvalue = nullptr;
                r.rvalue = nullptr;
            }
        }
        return r;
    }
};

RangeValue makeRange(LLVMContext &context, APInt left, APInt right) {
    RangeValue r;
    r.kind   = PossibleRangeValues::constant;
    r.lvalue = ConstantInt::get(context, left);
    r.rvalue = ConstantInt::get(context, right);
    DEBUG_PRINT("Created range: [" << left << ", " << right << "]");
    return r;
}

RangeValue infRange() {
    RangeValue r;
    r.kind = PossibleRangeValues::infinity;
    DEBUG_PRINT("Created infinity range.");
    return r;
}

using RangeState  = analysis::AbstractState<RangeValue>;
using RangeResult = analysis::DataflowResult<RangeValue>;

// The meet: reuses operator|( ) from RangeValue
class RangeMeet : public analysis::Meet<RangeValue, RangeMeet> {
public:
    RangeValue
    meetPair(RangeValue &s1, RangeValue &s2) const {
        DEBUG_PRINT("\nMeeting two RangeValues.");
        return s1 | s2;
    }
};

class RangeTransfer {
public:
    // ADDED: Track pointers that have been stored to once, skip merging on subsequent stores - optimization
    // Key = pointer Value*, Value = boolean
    mutable std::unordered_map<llvm::Value*, bool> storeHappened;

    void operator()(llvm::Value &I, RangeState &state) const {
        DEBUG_PRINT("\nProcessing instruction: " << I);

        // If store => handle
        if (auto *st = dyn_cast<StoreInst>(&I)) {
            DEBUG_PRINT("Instruction is a StoreInst.");
            handleStore(*st, state);
            return;
        }
        // If load => handle
        if (auto *ld = dyn_cast<LoadInst>(&I)) {
            DEBUG_PRINT("Instruction is a LoadInst.");
            handleLoad(*ld, state);
            return;
        }

        // if recognized as malloc => record size
        {
            uint64_t sz = 0;
            if (isKnownMallocCall(&I, sz)) {
                // We do not directly store it into the state here;
                // usually it's stored to a variable. handleStore sees it.
                DEBUG_PRINT("Malloc call recognized. Size: " << sz);
            }
        }

        // Handle bitcast of malloc result to track derived pointers
        if (auto *castInst = dyn_cast<BitCastInst>(&I)) {
            llvm::Value *originalPtr = castInst->getOperand(0)->stripPointerCasts();
            DEBUG_PRINT("Instruction is a BitCastInst. Original pointer: " << *originalPtr);
            auto it = state.find(originalPtr);
            if (it != state.end() && it->second.isConstant()) {
                // unify bit widths to 64
                uint64_t allocSize = it->second.rvalue->getValue().sextOrTrunc(64).getZExtValue() + 1;
                state[&I] = makeRange(castInst->getContext(),
                                      APInt(64, 0),
                                      APInt(64, allocSize - 1));
                DEBUG_PRINT("Associated derived pointer with size: " << allocSize);
            }
        }

        // Handle GetElementPtrInst (GEP)
        if (auto *gep = dyn_cast<GetElementPtrInst>(&I)) {
            DEBUG_PRINT("Instruction is a GetElementPtrInst.");
            handleGEP(*gep, state);
            return;
        }

        // Handle ConstantInt
        if (auto *constant = dyn_cast<ConstantInt>(&I)) {
            RangeValue r;
            r.kind = PossibleRangeValues::constant;
            r.lvalue = r.rvalue = constant;
            state[&I] = r;
            DEBUG_PRINT("ConstantInt found. Setting range to constant.");
        }
        // Handle BinaryOperator
        else if (auto *binOp = dyn_cast<BinaryOperator>(&I)) {
            DEBUG_PRINT("BinaryOperator found. Evaluating operation.");
            state[binOp] = evaluateBinOP(*binOp, state);
        }
        // Handle CastInst
        else if (auto *castOp = dyn_cast<CastInst>(&I)) {
            DEBUG_PRINT("CastInst found. Evaluating cast.");
            state[castOp] = evaluateCast(*castOp, state);
        }
        // Default: Instruction Needs Further Processing
        else {
            state[&I].kind = PossibleRangeValues::infinity;
            DEBUG_PRINT("Instruction needs further process or uninterested. Setting range to infinity at this moment to retain soundness.");
        }
    }

    RangeValue getRangeFor(llvm::Value *v, RangeState &state) const {
        if (auto *cint = dyn_cast<ConstantInt>(v)) {
            RangeValue r;
            r.kind   = PossibleRangeValues::constant;
            r.lvalue = r.rvalue = cint;
            DEBUG_PRINT("getRangeFor: ConstantInt encountered. Range is constant.");
            return r;
        }
        DEBUG_PRINT("getRangeFor: Retrieving range for " << *v);
        auto it = state.find(v);
        if (it != state.end()) {
            return it->second;
        }
        else {
            // If not found, default to unknown
            RangeValue r;
            r.kind = PossibleRangeValues::unknown;
            DEBUG_PRINT("getRangeFor: Value not found in state. Setting range to unknown.");
            return r;
        }
    }

    RangeValue evaluateBinOP(llvm::BinaryOperator &binOp, RangeState &state) const {
        auto *op1 = binOp.getOperand(0);
        auto *op2 = binOp.getOperand(1);
        DEBUG_PRINT("Evaluating BinaryOperator: " << binOp.getOpcodeName());
        auto range1 = getRangeFor(op1, state);
        auto range2 = getRangeFor(op2, state);

        // For all arithmetic ops, unify bitwidths to 64 before performing them
        if (range1.isConstant() && range2.isConstant()) {
            APInt l1 = range1.lvalue->getValue().sextOrTrunc(64);
            APInt r1 = range1.rvalue->getValue().sextOrTrunc(64);
            APInt l2 = range2.lvalue->getValue().sextOrTrunc(64);
            APInt r2 = range2.rvalue->getValue().sextOrTrunc(64);

            auto &ctx = range1.lvalue->getContext();
            auto opcode = binOp.getOpcode();

            if (opcode == Instruction::Add) {
                DEBUG_PRINT("Handling Add operation.");
                bool of1, of2;
                APInt sum1 = l1.sadd_ov(l2, of1);
                APInt sum2 = r1.sadd_ov(r2, of2);
                if (of1 || of2) {
                    DEBUG_PRINT("Overflow detected in Add. Setting range to infinity.");
                    return infRange();
                }
                return makeRange(ctx, sum1, sum2);
            }
            else if (opcode == Instruction::Sub) {
                DEBUG_PRINT("Handling Sub operation.");
                bool of1, of2;
                APInt a = l1.ssub_ov(r2, of1);
                APInt b = r1.ssub_ov(l2, of2);
                if (of1 || of2) {
                    DEBUG_PRINT("Overflow detected in Sub. Setting range to infinity.");
                    return infRange();
                }
                return makeRange(ctx, a, b);
            }
            else if (opcode == Instruction::Mul) {
                DEBUG_PRINT("Handling Mul operation.");
                SmallVector<APInt, 4> candidates;
                bool ofFlags[4] = {false, false, false, false};
                candidates.push_back(l1.smul_ov(l2, ofFlags[0]));
                candidates.push_back(l1.smul_ov(r2, ofFlags[1]));
                candidates.push_back(r1.smul_ov(l2, ofFlags[2]));
                candidates.push_back(r1.smul_ov(r2, ofFlags[3]));
                for (auto flag : ofFlags) {
                    if (flag) {
                        DEBUG_PRINT("Overflow detected in Mul. Setting range to infinity.");
                        return infRange();
                    }
                }
                APInt maxv = candidates[0];
                APInt minv = candidates[0];
                for (auto &c : candidates) {
                    if (c.sgt(maxv)) {
                        maxv = c;
                        DEBUG_PRINT("Updated maxv to " << c);
                    }
                    if (c.slt(minv)) {
                        minv = c;
                        DEBUG_PRINT("Updated minv to " << c);
                    }
                }
                return makeRange(ctx, minv, maxv);
            }
            else if (opcode == Instruction::SDiv) {
                DEBUG_PRINT("Handling SDiv operation.");
                // Very simplified code below, but we unify widths first anyway
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
                    bool fl[4] = {false, false, false, false};
                    cands.push_back(l1.sdiv_ov(l2, fl[0]));
                    cands.push_back(l1.sdiv_ov(r2, fl[1]));
                    cands.push_back(r1.sdiv_ov(l2, fl[2]));
                    cands.push_back(r1.sdiv_ov(r2, fl[3]));
                    for (auto f : fl) {
                        if (f) {
                            DEBUG_PRINT("Overflow detected in SDiv. Setting range to infinity.");
                            return infRange();
                        }
                    }
                    APInt mx = cands[0], mn = cands[0];
                    for (auto &cc : cands) {
                        if (cc.sgt(mx)) {
                            mx = cc;
                            DEBUG_PRINT("Updated mx to " << cc);
                        }
                        if (cc.slt(mn)) {
                            mn = cc;
                            DEBUG_PRINT("Updated mn to " << cc);
                        }
                    }
                    return makeRange(ctx, mn, mx);
                }
            }
            else if (opcode == Instruction::UDiv) {
                DEBUG_PRINT("Handling UDiv operation.");
                APInt a = r1.udiv(l2);
                APInt b = l1.udiv(r2);
                return makeRange(ctx, a, b);
            }
            else {
                DEBUG_PRINT("Unhandled BinaryOperator opcode: " << binOp.getOpcodeName() << ". Setting range to infinity.");
                return infRange();
            }
        }
        else if (range1.isInfinity() || range2.isInfinity()) {
            DEBUG_PRINT("One of the ranges is infinity. Setting result to infinity.");
            RangeValue rr;
            rr.kind = PossibleRangeValues::infinity;
            return rr;
        }
        else {
            DEBUG_PRINT("Non-constant ranges encountered. Setting range to unknown.");
            RangeValue rr;
            return rr;
        }
    }

    RangeValue evaluateCast(llvm::CastInst &Cst, RangeState &state) const {
        DEBUG_PRINT("Evaluating CastInst: " << Cst);
        auto valRange = getRangeFor(Cst.getOperand(0), state);
        if (!valRange.isConstant()) {
            RangeValue r;
            r.kind = valRange.kind;
            DEBUG_PRINT("Cast operand range is not constant. Setting cast result to same kind.");
            return r;
        }
        auto *context = &Cst.getContext();
        Constant *cl = ConstantFoldCastOperand(Cst.getOpcode(), valRange.lvalue,
                                               Cst.getDestTy(), Cst.getModule()->getDataLayout());
        Constant *cr = ConstantFoldCastOperand(Cst.getOpcode(), valRange.rvalue,
                                               Cst.getDestTy(), Cst.getModule()->getDataLayout());
        if (!cl || !cr || isa<ConstantExpr>(cl) || isa<ConstantExpr>(cr)) {
            DEBUG_PRINT("Cast operation resulted in non-constant. Setting range to infinity.");
            return infRange();
        }
        auto *cli = dyn_cast<ConstantInt>(cl);
        auto *cri = dyn_cast<ConstantInt>(cr);
        if (!cli || !cri) {
            DEBUG_PRINT("Cast operands are not ConstantInt after casting. Setting range to infinity.");
            return infRange();
        }
        RangeValue rv;
        rv.kind   = PossibleRangeValues::constant;
        rv.lvalue = cli;
        rv.rvalue = cri;
        DEBUG_PRINT("Cast operation successful. New range: [" << cli->getValue() << ", " << cri->getValue() << "]");
        return rv;
    }

private:
    void handleStore(StoreInst &SI, RangeState &state) const {
        llvm::Value *val = SI.getValueOperand();
        llvm::Value *ptr = SI.getPointerOperand();

        DEBUG_PRINT("Handling StoreInst. Value: " << *val << ", Pointer: " << *ptr);

        if (isLocalAllocaPointer(ptr)) {
            auto it = storeHappened.find(ptr);
            auto valRange = getRangeFor(val, state);

            if (it == storeHappened.end()) {
                storeHappened[ptr] = true;
                state[ptr] = valRange;
                DEBUG_PRINT("First store to pointer " << *ptr << ". Setting range.");
            } else {
                state[ptr] = valRange;
                DEBUG_PRINT("Subsequent store to pointer " << *ptr << ". Updating range.");
            }

            // Propagate allocation size if val is a malloc or derived pointer
            uint64_t sz = 0;
            if (isKnownMallocCall(val, sz)) {
                // If sz == 0 => non-constant => treat as unknown => infinity
                if (sz == 0) {
                    state[ptr] = infRange();
                    DEBUG_PRINT("Propagated unknown malloc size to stored pointer " << *ptr);
                } else {
                    state[ptr] = makeRange(ptr->getContext(), APInt(64, 0), APInt(64, sz - 1));
                    DEBUG_PRINT("Propagated malloc size " << sz << " to stored pointer " << *ptr);
                }
            }
            else if (state.find(val) != state.end() && state[val].isConstant()) {
                uint64_t allocSize = state[val].rvalue->getValue().sextOrTrunc(64).getZExtValue() + 1;
                state[ptr] = makeRange(ptr->getContext(), APInt(64, 0), APInt(64, allocSize - 1));
                DEBUG_PRINT("Propagated malloc size " << allocSize << " to stored pointer " << *ptr);
            }
        }
    }

    void handleLoad(LoadInst &LI, RangeState &state) const {
        llvm::Value *ptr = LI.getPointerOperand();
        DEBUG_PRINT("Handling LoadInst. Pointer: " << *ptr);
        if (isLocalAllocaPointer(ptr)) {
            auto it = state.find(ptr);
            if (it != state.end()) {
                state[&LI] = it->second;
                DEBUG_PRINT("Loaded value from pointer " << *ptr << " with range kind: " 
                            << static_cast<int>(it->second.kind));
                return;
            }
        }

        // Fallback: unknown or infinity
        state[&LI].kind = PossibleRangeValues::infinity;
        DEBUG_PRINT("Pointer not found or not a local alloca. Setting load range to infinity.");
    }

    void handleGEP(GetElementPtrInst &gep, RangeState &state) const {
        llvm::Value *basePtr = gep.getPointerOperand();
        DEBUG_PRINT("Handling GEP. Base pointer: " << *basePtr);

        // Retrieve base pointer's range
        RangeValue baseRange = getRangeFor(basePtr, state);
        if (baseRange.isInfinity() || baseRange.isUnknown()) {
            DEBUG_PRINT("Base pointer range is infinity or unknown. Setting GEP range to infinity.");
            state[&gep].kind = PossibleRangeValues::infinity;
            return;
        }

        // Handle multi-dimensional GEPs by iterating over all indices
        unsigned numIndices = gep.getNumIndices();
        APInt totalOffset(64, 0); // always 64-bit offset

        for (unsigned i = 0; i < numIndices; ++i) {
            llvm::Value *indexVal = gep.getOperand(i + 1); // Operand 0 is the base pointer
            RangeValue indexRange = getRangeFor(indexVal, state);

            if (indexRange.isInfinity() || indexRange.isUnknown()) {
                DEBUG_PRINT("GEP index range is infinity or unknown. Setting GEP range to infinity.");
                state[&gep].kind = PossibleRangeValues::infinity;
                return;
            }

            // Handle constant indices
            if (indexRange.isConstant()) {
                // unify bit widths
                APInt idx = indexRange.lvalue->getValue().sextOrTrunc(64);
                int64_t index = idx.getSExtValue();
                const DataLayout &DL = gep.getModule()->getDataLayout();
                Type *elemType = gep.getResultElementType();
                uint64_t elemSize = DL.getTypeAllocSize(elemType);

                if (index < 0) {
                    DEBUG_PRINT("GEP index " << index << " is negative. Setting range to infinity.");
                    state[&gep].kind = PossibleRangeValues::infinity;
                    return;
                }

                // Calculate the total offset in bytes
                APInt indexOffset = APInt(64, (uint64_t)index) * APInt(64, elemSize);
                totalOffset += indexOffset;

                DEBUG_PRINT("GEP index " << index << " contributes " << elemSize 
                            << " bytes. Total offset now: " << totalOffset);
            }
            else {
                DEBUG_PRINT("GEP index is not constant. Setting GEP range to infinity.");
                state[&gep].kind = PossibleRangeValues::infinity;
                return;
            }
        }

        // Check if the total offset is within the base pointer's allocated size
        if (baseRange.isConstant()) {
            // unify bitwidth
            uint64_t allocSize = baseRange.rvalue->getValue().sextOrTrunc(64).getZExtValue() + 1;
            uint64_t computedOffset = totalOffset.getZExtValue();

            DEBUG_PRINT("Computed total offset: " << computedOffset 
                        << " bytes. Allocated size: " << allocSize << " bytes.");

            if (computedOffset < allocSize) {
                // corrected Range: [0, allocSize - computedOffset - 1]
                if (allocSize <= computedOffset) {
                    DEBUG_PRINT("Computed offset exceeds or equals allocated size. Setting range to infinity.");
                    state[&gep].kind = PossibleRangeValues::infinity;
                    return;
                }
                uint64_t newMaxValue = allocSize - computedOffset - 1;
                APInt lower = APInt(64, 0);
                APInt upper = APInt(64, newMaxValue);
                RangeValue gepRange = makeRange(gep.getContext(), lower, upper);
                state[&gep] = gepRange;
                DEBUG_PRINT("GEP offset is within bounds. Setting range to [0, " << newMaxValue << "]");
            }
            else {
                DEBUG_PRINT("GEP offset exceeds allocated size. Setting range to infinity.");
                state[&gep].kind = PossibleRangeValues::infinity;
            }
        }
        else {
            DEBUG_PRINT("Base pointer does not have an associated allocation size. Setting GEP range to infinity.");
            state[&gep].kind = PossibleRangeValues::infinity;
        }
    }
};

void valueRangeAnalysis(Module *M,
    std::map<const UnifiedMemSafe::VariableMapKeyType *, UnifiedMemSafe::VariableInfo> heapSeqPointerSet,
    UnifiedMemSafe::AnalysisState TheState)
{
    DEBUG_PRINT("Starting Value Range Analysis.");
    auto *mainFunction = M->getFunction("main");
    if (!mainFunction) {
       DEBUG_PRINT("ERROR: Unable to find main function for Value-Range Analysis! Skipping!");
       return;
    }

    using Value    = RangeValue;
    using Transfer = RangeTransfer;
    using Meet     = RangeMeet;
    using Analysis = analysis::ForwardDataflowAnalysis<Value, Transfer, Meet>;
    Analysis analysis{*M, mainFunction};
    DEBUG_PRINT("Computing forward dataflow analysis.");
    auto results = analysis.computeForwardDataflow();

    std::map<const UnifiedMemSafe::VariableMapKeyType *, UnifiedMemSafe::VariableInfo> heapUnsafeSeqPointerSet;

    DEBUG_PRINT("\nProcessing analysis results.");
    for (auto & [ctxt, contextResults] : results) {
        for (auto & [function, rangeStates] : contextResults) {
            for (auto &valueStatePair : rangeStates) {
                auto *inst = llvm::dyn_cast<llvm::GetElementPtrInst>(valueStatePair.first);
                if (!inst) {
                    continue;
                }

                // We only check GEP instructions that we previously recognized in "heapSeqPointerSet":
                if (heapSeqPointerSet.find(inst) != heapSeqPointerSet.end()) {
                    DEBUG_PRINT("\nAnalyzing GEP instruction: " << *inst);
                    auto &state = analysis::getIncomingState(rangeStates, *inst);
                    Type *type = cast<PointerType>(
                            cast<GetElementPtrInst>(inst)->getPointerOperandType())->getElementType();
                    auto pointerTy = dyn_cast_or_null<PointerType>(type);
                    auto arrayTy   = dyn_cast_or_null<ArrayType>(type);
                    auto structTy  = dyn_cast_or_null<StructType>(type);

                    llvm::Value *basePtr = inst->getPointerOperand();
                    DEBUG_PRINT("Base pointer for GEP: " << *basePtr);

                    // See if basePtr is recognized malloc or derived malloc => do bounding
                    bool hasMallocSize = false;
                    uint64_t mallocSize = 0;

                    // Check if basePtr has a constant range in state
                    if (auto it = state.find(basePtr); it != state.end() && it->second.isConstant()) {
                        mallocSize = it->second.rvalue->getValue().sextOrTrunc(64).getZExtValue() + 1;
                        hasMallocSize = true;
                        DEBUG_PRINT("Base pointer has a known allocation size: " << mallocSize);
                    } else {
                        // If the pointer is in Infinity/Unknown range, we mark the GEP unsafe:
                        auto it2 = state.find(basePtr);
                        if (it2 != state.end() &&
                            (it2->second.isInfinity() || it2->second.isUnknown())) {
                            auto vmkt = dyn_cast<UnifiedMemSafe::VariableMapKeyType>(inst);
                            if (vmkt && TheState.GetPointerVariableInfo(vmkt) != NULL) {
                                UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                DEBUG_PRINT("Base pointer has infinite/unknown range => Marking GEP as unsafe.");
                                heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                            }
                        }
                        DEBUG_PRINT("Base pointer is not a known malloc or derived malloc pointer.");
                    }

                    if(!arrayTy && !structTy){
                        // Check if 'inst' can be cast to VariableMapKeyType
                        auto vmkt = dyn_cast<UnifiedMemSafe::VariableMapKeyType>(inst);
                        if(vmkt){
                            if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                if(!vmktinfo) {
                                    DEBUG_PRINT("vmktinfo is NULL; skipping analysis.");
                                    continue;
                                }

                                if (auto *gepInst = dyn_cast<llvm::GetElementPtrInst>(inst)) {
                                    auto index = (gepInst->getNumOperands() > 2)
                                                ? gepInst->getOperand(2)
                                                : gepInst->getOperand(1);
                                    DEBUG_PRINT("GEP index operand: " << *index);

                                    auto constant = dyn_cast<ConstantInt>(index);

                                    // If this base pointer has a known malloc size, do bounding:
                                    if (hasMallocSize) {
                                        const DataLayout &DL = M->getDataLayout();
                                        Type *elemTy = gepInst->getResultElementType();
                                        uint64_t elemSize = DL.getTypeAllocSize(elemTy);
                                        if (elemSize == 0) {
                                            elemSize = 1;
                                            DEBUG_PRINT("Element size is 0. Setting to 1.");
                                        }
                                        int64_t maxElemCount = static_cast<int64_t>(mallocSize / elemSize);
                                        DEBUG_PRINT("Element size: " << elemSize << ", Max element count: " << maxElemCount);
                                        if (constant) {
                                            int64_t c = constant->getSExtValue();
                                            DEBUG_PRINT("Constant index value: " << c);
                                            if (c < 0 || c >= maxElemCount) {
                                                DEBUG_PRINT("Index " << c << " is out of bounds. Marking as unsafe.");
                                                heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                            }
                                        }
                                        else {
                                            RangeValue &rv2 = state[index];
                                            DEBUG_PRINT("Range value for index: kind = " << static_cast<int>(rv2.kind));
                                            if (rv2.isUnknown() || rv2.isInfinity()) {
                                                DEBUG_PRINT("Index range is unknown or infinity. Marking as unsafe.");
                                                heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                            }
                                            else if (rv2.isConstant()) {
                                                int64_t lo = rv2.lvalue->getValue().sextOrTrunc(64).getSExtValue();
                                                int64_t hi = rv2.rvalue->getValue().sextOrTrunc(64).getSExtValue();
                                                DEBUG_PRINT("Index range: [" << lo << ", " << hi << "]");
                                                if (lo < 0 || hi >= maxElemCount) {
                                                    DEBUG_PRINT("Index range exceeds bounds. Marking as unsafe.");
                                                    heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                                }
                                            }
                                            else {
                                                DEBUG_PRINT("Index range is not constant. Marking as unsafe.");
                                                heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                            }
                                        }
                                        continue;
                                    }

                                    // Otherwise, if no known malloc size, fall back on vmkt->size if available:
                                    if (constant) {
                                        auto *sizeCI = dyn_cast<ConstantInt>(vmktinfo->size);
                                        if(!sizeCI) {
                                            DEBUG_PRINT("vmktinfo->size is not a ConstantInt. Skipping analysis.");
                                            continue;
                                        }
                                        int underlyingSize = sizeCI->getSExtValue();

                                        DEBUG_PRINT("Index is a constant: " << constant->getSExtValue()
                                                   << ", Underlying size: " << underlyingSize);
                                        if (!constant->isNegative() && underlyingSize > 0) {
                                            DEBUG_PRINT("Index is within valid range. Continuing.");
                                            continue;
                                        } else {
                                            DEBUG_PRINT("Index is out of valid range. Marking as unsafe.");
                                            heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                        }
                                    } else {
                                        DEBUG_PRINT("Index is not a constant. Marking as unsafe.");
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
                        DEBUG_PRINT("Array GEP index operand: " << *index);
                        auto constant = dyn_cast<ConstantInt>(index);
                        if (constant) {
                            DEBUG_PRINT("Array index is a constant: " << constant->getSExtValue());
                            if (!constant->isNegative() && !constant->uge(size)) {
                                if (numBytes >= ((int64_t) constant->getValue().getLimitedValue() * elmtBytes)){
                                    DEBUG_PRINT("Array size in terms of number of elements: "<< numBytes/elmtBytes);
                                    DEBUG_PRINT("Array total size: "<< numBytes);
                                    DEBUG_PRINT("Array index within bounds. Safe access.");
                                }
                                else{
                                    DEBUG_PRINT("Array index multiplied by element size exceeds allocated bytes. Marking as unsafe.");
                                    auto vmkt = dyn_cast<UnifiedMemSafe::VariableMapKeyType>(inst);
                                    if (vmkt) {
                                        if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                            UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                            heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                            DEBUG_PRINT("Pointer marked as unsafe.");
                                        }
                                    }
                                }
                            }
                            else{
                                DEBUG_PRINT("Array index exceeds allocated size. Marking as unsafe.");
                                auto vmkt = dyn_cast<UnifiedMemSafe::VariableMapKeyType>(inst);
                                if (vmkt) {
                                    if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                        UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                        heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                        DEBUG_PRINT("Pointer marked as unsafe.");
                                    }
                                }
                            }
                        }
                        else {
                            // `index` is not a literal ConstantInt in the IR, so we look up its range:
                            auto it = state.find(index);
                            if (it != state.end()) {
                                auto &rangeValue = it->second;
                                DEBUG_PRINT("Array index is not a compile-time constant. Range kind: "
                                            << static_cast<int>(rangeValue.kind));

                                // 1) Handle unknown, infinite, or negative-lower-bound ranges
                                if (rangeValue.isUnknown() ||
                                    rangeValue.isInfinity() ||
                                    (rangeValue.lvalue && rangeValue.lvalue->isNegative())) {
                                    DEBUG_PRINT("Array index range is indeed not a constant. Marking as unsafe.");
                                    auto vmkt = dyn_cast<UnifiedMemSafe::VariableMapKeyType>(inst);
                                    if (vmkt) {
                                        if (TheState.GetPointerVariableInfo(vmkt) != NULL) {
                                            UnifiedMemSafe::VariableInfo *vmktinfo =
                                                TheState.GetPointerVariableInfo(vmkt);
                                            heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                            DEBUG_PRINT("Pointer marked as unsafe.");
                                        }
                                    }
                                }
                                // 2) If the dataflow says it's a constant range, explicitly check bounds
                                else if (rangeValue.isConstant()) {
                                    DEBUG_PRINT("DataFlow analysis suggests that the variable index can be retrieved as constant.");
                                    // Unify bitwidth to 64 before extracting
                                    int64_t loVal = rangeValue.lvalue
                                        ? rangeValue.lvalue->getValue().sextOrTrunc(64).getSExtValue()
                                        : 0;
                                    int64_t hiVal = rangeValue.rvalue
                                        ? rangeValue.rvalue->getValue().sextOrTrunc(64).getSExtValue()
                                        : 0;

                                    if (loVal < 0) {
                                        // Negative index => unsafe
                                        DEBUG_PRINT("Array index range has negative lower bound. Marking as unsafe.");
                                        auto vmkt = dyn_cast<UnifiedMemSafe::VariableMapKeyType>(inst);
                                        if (vmkt) {
                                            if (TheState.GetPointerVariableInfo(vmkt) != NULL) {
                                                UnifiedMemSafe::VariableInfo *vmktinfo =
                                                    TheState.GetPointerVariableInfo(vmkt);
                                                heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                                DEBUG_PRINT("Pointer marked as unsafe.");
                                            }
                                        }
                                    }
                                    else if (hiVal >= static_cast<int64_t>(size)) {
                                        // Upper bound beyond the array dimension => unsafe
                                        DEBUG_PRINT("Array index range may exceed allocated elements. Marking as unsafe.");
                                        auto vmkt = dyn_cast<UnifiedMemSafe::VariableMapKeyType>(inst);
                                        if (vmkt) {
                                            if (TheState.GetPointerVariableInfo(vmkt) != NULL) {
                                                UnifiedMemSafe::VariableInfo *vmktinfo =
                                                    TheState.GetPointerVariableInfo(vmkt);
                                                heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                                DEBUG_PRINT("Pointer marked as unsafe.");
                                            }
                                        }
                                    }
                                    else {
                                        // Entire [loVal, hiVal] is within [0, size - 1]
                                        int64_t loVal = rangeValue.lvalue
                                            ? rangeValue.lvalue->getValue().sextOrTrunc(64).getSExtValue()
                                            : 0;
                                        int64_t hiVal = rangeValue.rvalue
                                            ? rangeValue.rvalue->getValue().sextOrTrunc(64).getSExtValue()
                                            : 0;
                                        DEBUG_PRINT("Array index constant range is [" << loVal <<", " 
                                                    << hiVal << "], within the array size: " << size <<". Safe access.");
                                    }
                                }

                                // 3) Existing check if upper bound is explicitly >= size
                                //    (sometimes used when rvalue alone indicates out-of-bounds)
                                if (rangeValue.rvalue && rangeValue.rvalue->uge(size)) {
                                    DEBUG_PRINT("Array index range exceeds allocated size through "
                                                "retrieving the constant value of the variable index. "
                                                "Marking as unsafe.");
                                    DEBUG_PRINT("Max variable index: " << *rangeValue.rvalue);
                                    DEBUG_PRINT("Max access range of the variable index: "
                                                << (int64_t)rangeValue.rvalue->getValue().getLimitedValue() * elmtBytes);
                                    auto vmkt = dyn_cast<UnifiedMemSafe::VariableMapKeyType>(inst);
                                    if (vmkt) {
                                        if (TheState.GetPointerVariableInfo(vmkt) != NULL) {
                                            UnifiedMemSafe::VariableInfo *vmktinfo =
                                                TheState.GetPointerVariableInfo(vmkt);
                                            heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                            DEBUG_PRINT("Pointer marked as unsafe.");
                                        }
                                    }
                                }
                            }
                            else {
                                // If we have no dataflow info about this index, mark unsafe as fallback.
                                DEBUG_PRINT("Array index range not found in state. Marking as unsafe.");
                                auto vmkt = dyn_cast<UnifiedMemSafe::VariableMapKeyType>(inst);
                                if (vmkt) {
                                    if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                        UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                        heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                        DEBUG_PRINT("Pointer marked as unsafe.");
                                    }
                                }
                            }
                        }

                        // Check derived malloc pointers within array types
                        if (hasMallocSize) {
                            if (constant) {
                                int64_t c = constant->getSExtValue();
                                DEBUG_PRINT("Derived array index constant value: " << c);
                                if (c < 0 || c >= static_cast<int64_t>(size)) {
                                    DEBUG_PRINT("Derived array index " << c << " is out of bounds. Marking as unsafe.");
                                    auto vmkt = dyn_cast<UnifiedMemSafe::VariableMapKeyType>(inst);
                                    if (vmkt) {
                                        if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                            UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                            heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                            DEBUG_PRINT("Pointer marked as unsafe.");
                                        }
                                    }
                                }
                            }
                            else {
                                auto it = state.find(index);
                                if (it != state.end()) {
                                    auto &rv2 = it->second;
                                    DEBUG_PRINT("Derived array index range kind: " << static_cast<int>(rv2.kind));
                                    if (rv2.isUnknown() || rv2.isInfinity()) {
                                        DEBUG_PRINT("Derived array index range is unknown or infinity. Marking as unsafe.");
                                        auto vmkt = dyn_cast<UnifiedMemSafe::VariableMapKeyType>(inst);
                                        if (vmkt) {
                                            if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                                UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                                heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                                DEBUG_PRINT("Pointer marked as unsafe.");
                                            }
                                        }
                                    }
                                    else if (rv2.isConstant()) {
                                        int64_t lo = rv2.lvalue->getValue().sextOrTrunc(64).getSExtValue();
                                        int64_t hi = rv2.rvalue->getValue().sextOrTrunc(64).getSExtValue();
                                        DEBUG_PRINT("Derived array index range: [" << lo << ", " << hi << "]");
                                        if (lo < 0 || hi >= static_cast<int64_t>(size)) {
                                            DEBUG_PRINT("Derived array index range exceeds bounds. Marking as unsafe.");
                                            auto vmkt = dyn_cast<UnifiedMemSafe::VariableMapKeyType>(inst);
                                            if (vmkt) {
                                                if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                                    UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                                    heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                                    DEBUG_PRINT("Pointer marked as unsafe.");
                                                }
                                            }
                                        }
                                    }
                                    else {
                                        DEBUG_PRINT("Index range is not constant. Marking as unsafe.");
                                        auto vmkt = dyn_cast<UnifiedMemSafe::VariableMapKeyType>(inst);
                                        if (vmkt) {
                                            if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                                UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                                heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                                DEBUG_PRINT("Pointer marked as unsafe.");
                                            }
                                        }
                                    }
                                }
                                else {
                                    DEBUG_PRINT("Derived array index range not found in state. Marking as unsafe.");
                                    auto vmkt = dyn_cast<UnifiedMemSafe::VariableMapKeyType>(inst);
                                    if (vmkt) {
                                        if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                            UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                            heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                            DEBUG_PRINT("Pointer marked as unsafe.");
                                        }
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
                        DEBUG_PRINT("Struct GEP index operand: " << *index);

                        const llvm::StructLayout* structureLayout = layout.getStructLayout(structTy);
                        auto constant = dyn_cast<ConstantInt>(index);
                        if (constant) {
                            auto intIndex = (uint64_t)constant->getValue().getLimitedValue();
                            DEBUG_PRINT("Struct index is a constant: " << intIndex);
                            if(intIndex < size){
                                auto offset = structureLayout->getElementOffset(intIndex);
                                DEBUG_PRINT("Struct element offset: " << offset);
                                DEBUG_PRINT("Struct total size: " << numBytes);
                                if (!constant->isNegative() && intIndex < size) {
                                    if (numBytes >= offset + layout.getTypeAllocSize(structTy->getElementType(intIndex))){
                                        DEBUG_PRINT("Struct index within bounds based on offset. Safe access.");
                                    }
                                    else{
                                        DEBUG_PRINT("Struct index offset exceeds allocated bytes. Marking as unsafe.");
                                        auto vmkt = dyn_cast<UnifiedMemSafe::VariableMapKeyType>(inst);
                                        if (vmkt) {
                                            if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                                UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                                heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                                DEBUG_PRINT("Pointer marked as unsafe.");
                                            }
                                        }
                                    }
                                }
                            }
                            else{
                                DEBUG_PRINT("Struct index exceeds number of elements. Marking as unsafe.");
                                auto vmkt = dyn_cast<UnifiedMemSafe::VariableMapKeyType>(inst);
                                if (vmkt) {
                                    if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                        UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                        heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                        DEBUG_PRINT("Pointer marked as unsafe.");
                                    }
                                }
                            }
                        }
                        else {
                            auto it = state.find(index);
                            if (it != state.end()) {
                                auto &rangeValue = it->second;
                                DEBUG_PRINT("Struct index is not a constant. Range kind: " 
                                            << static_cast<int>(rangeValue.kind));
                                if (rangeValue.isUnknown() ||
                                    rangeValue.isInfinity() ||
                                    (rangeValue.lvalue && rangeValue.lvalue->isNegative()) ||
                                    (rangeValue.rvalue && rangeValue.rvalue->uge(size))) {
                                    DEBUG_PRINT("Struct index range is unsafe. Marking as unsafe.");
                                    auto vmkt = dyn_cast<UnifiedMemSafe::VariableMapKeyType>(inst);
                                    if (vmkt) {
                                        if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                            UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                            heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                            DEBUG_PRINT("Pointer marked as unsafe.");
                                        }
                                    }
                                }
                            }
                            else {
                                DEBUG_PRINT("Struct index range not found in state. Marking as unsafe.");
                                auto vmkt = dyn_cast<UnifiedMemSafe::VariableMapKeyType>(inst);
                                if (vmkt) {
                                    if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                        UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                        heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                        DEBUG_PRINT("Pointer marked as unsafe.");
                                    }
                                }
                            }
                        }

                        // Check derived malloc pointers within struct types
                        if (hasMallocSize) {
                            if (constant) {
                                int64_t c = constant->getSExtValue();
                                DEBUG_PRINT("Derived struct index constant value: " << c);
                                if (c < 0 || c >= static_cast<int64_t>(size)) {
                                    DEBUG_PRINT("Derived struct index " << c 
                                                << " is out of bounds. Marking as unsafe.");
                                    auto vmkt = dyn_cast<UnifiedMemSafe::VariableMapKeyType>(inst);
                                    if (vmkt) {
                                        if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                            UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                            heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                            DEBUG_PRINT("Pointer marked as unsafe.");
                                        }
                                    }
                                }
                            }
                            else {
                                auto it = state.find(index);
                                if (it != state.end()) {
                                    auto &rv2 = it->second;
                                    DEBUG_PRINT("Derived struct index range kind: " 
                                                << static_cast<int>(rv2.kind));
                                    if (rv2.isUnknown() || rv2.isInfinity()) {
                                        DEBUG_PRINT("Derived struct index range is unknown or infinity. Marking as unsafe.");
                                        auto vmkt = dyn_cast<UnifiedMemSafe::VariableMapKeyType>(inst);
                                        if (vmkt) {
                                            if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                                UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                                heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                                DEBUG_PRINT("Pointer marked as unsafe.");
                                            }
                                        }
                                    }
                                    else if (rv2.isConstant()) {
                                        int64_t lo = rv2.lvalue->getValue().sextOrTrunc(64).getSExtValue();
                                        int64_t hi = rv2.rvalue->getValue().sextOrTrunc(64).getSExtValue();
                                        DEBUG_PRINT("Derived struct index range: [" << lo << ", " << hi << "]");
                                        if (lo < 0 || hi >= static_cast<int64_t>(size)) {
                                            DEBUG_PRINT("Derived struct index range exceeds bounds. Marking as unsafe.");
                                            auto vmkt = dyn_cast<UnifiedMemSafe::VariableMapKeyType>(inst);
                                            if (vmkt) {
                                                if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                                    UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                                    heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                                    DEBUG_PRINT("Pointer marked as unsafe.");
                                                }
                                            }
                                        }
                                    }
                                    else {
                                        DEBUG_PRINT("Index range is not constant. Marking as unsafe.");
                                        auto vmkt = dyn_cast<UnifiedMemSafe::VariableMapKeyType>(inst);
                                        if (vmkt) {
                                            if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                                UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                                heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                                DEBUG_PRINT("Pointer marked as unsafe.");
                                            }
                                        }
                                    }
                                }
                                else {
                                    DEBUG_PRINT("Derived struct index range not found in state. Marking as unsafe.");
                                    auto vmkt = dyn_cast<UnifiedMemSafe::VariableMapKeyType>(inst);
                                    if (vmkt) {
                                        if (TheState.GetPointerVariableInfo(vmkt) != NULL){
                                            UnifiedMemSafe::VariableInfo *vmktinfo = TheState.GetPointerVariableInfo(vmkt);
                                            heapUnsafeSeqPointerSet[vmkt] = *vmktinfo;
                                            DEBUG_PRINT("Pointer marked as unsafe.");
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // Further processing can be done as needed
    }
    errs() << GREEN <<"Unsafe Seq Pointer After Value Range Analysis:\t\t"
               << DETAIL << heapUnsafeSeqPointerSet.size() << NORMAL << "\n";
    for (const auto &entry : heapUnsafeSeqPointerSet) {
        const UnifiedMemSafe::VariableMapKeyType *vmkt = entry.first;
        const UnifiedMemSafe::VariableInfo &info = entry.second;

        // Print the instruction
        if (const llvm::Instruction *inst = llvm::dyn_cast<llvm::Instruction>(vmkt)) {
            DEBUG_PRINT(*inst);
        } else {
            DEBUG_PRINT("Non-instruction entry in heapUnsafeSeqPointerSet.\n");
        }
    }
}
