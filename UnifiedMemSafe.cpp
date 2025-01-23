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
 
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/ADT/StringMap.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/DebugInfoMetadata.h"

#include "llvm/Transforms/Instrumentation.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/TargetFolder.h"
#include "llvm/Analysis/TargetLibraryInfo.h" 
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Intrinsics.h"

#include "llvm/IR/ValueSymbolTable.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/DebugInfo.h"

#include "llvm/IR/DerivedTypes.h"
#include "Utils.hpp"
#include "program-dependence-graph/include/PTAWrapper.hh"
#include "program-dependence-graph/include/Graph.hh"
#include "program-dependence-graph/include/PDGEnums.hh"
#include "ProgramDependencyGraph.hh" 
#include "ValueRange.hpp" 
#include "DataGuard.hpp"
#include "Uriah.hpp"
//#include "PointerUtils.hpp"


#include <list>
#include <chrono>
#include <time.h>
#include <unistd.h>
using namespace llvm;


#define IS_DEBUGGING 1
#define IS_NAIVE 0

#define DEBUG_TYPE "UnifiedMemSafe"

#define CONTAINS(v, e) (std::find(v.begin(), v.end(), e) != v.end())

unsigned int CCuredSafePtrs = 0;
unsigned int CCuredSeqPtrs = 0;
unsigned int CCuredDynPtrs = 0;

std::map<const UnifiedMemSafe::VariableMapKeyType *, UnifiedMemSafe::VariableInfo>heapPointerSet;


namespace 
{

	class UnifiedMemSafePass : public ModulePass
	{

	public:
		UnifiedMemSafePass() : ModulePass(ID) {}
		static char ID; // Pass identification, replacement for typeid
		StringRef getPassName() const override { return "UnifiedMemSafePass"; }

	private:
		Module *CurrentModule;
		const DataLayout *CurrentDL;
		ObjectSizeOffsetEvaluator *ObjSizeEval;

		UnifiedMemSafe::AnalysisState TheState;
		Type *MySizeType;
		ConstantInt *UnknownSizeConstInt;

		std::vector<std::string> WhitelistedFunctions;
		bool isCurrentFunctionWhitelisted = false;                   // function excluded from both analysis and instrumentation
		bool isCurrentFunctionWhitelistedForInstrumentation = false; // function excluded from instrumentation but included in analysis

		//BasicBlock *TrapBB = nullptr;

		//std::vector<Instruction *> InstrumentationWorkList;
		std::vector<Function *> FunctionsAddedWithNewReturnType; 

		Function *MyPrintErrorLineFn;
		Function *MyPrintCheckFn;
		Function *setMetadataFunction;
		Function *lookupMetadataFunction;

		std::set<pdg::EdgeType> edge_types = {
			pdg::EdgeType::DATA_DEF_USE,
			pdg::EdgeType::DATA_RAW,
			pdg::EdgeType::DATA_READ,
			pdg::EdgeType::DATA_ALIAS,
		};

		std::set<const llvm::Value*> AliasedWithHeapSeqPointers;
    	std::set<const llvm::Value*> AliasedWithHeapDynPointers;

		// alias map
		std::unordered_map<Value*, std::unordered_set<Value*>> MallocAliasMap;

		// counts the number of pointer indirection for a type (e.g. for "int**" would be 2)
		
		int countIndirections(Type *T){
			if (!(T->isPointerTy()))
				return 0;
			PointerType *innerT = dyn_cast_or_null<PointerType>(T);
			return countIndirections(innerT->getElementType()) + 1;
		}
		// unwraps a pointer until the innermost type
		Type *unwrapPointer(Type *T){
			if (!(T->isPointerTy()))
				return T;
			PointerType *innerT = dyn_cast_or_null<PointerType>(T);
			return unwrapPointer(innerT->getElementType());
		}
		

		Value *getSizeForValue(Value *v){
			Value *size = ConstantInt::get(MySizeType, 0);
			SizeOffsetEvalType SizeOffset = ObjSizeEval->compute(v);
			if (ObjSizeEval->knownSize(SizeOffset)){
				errs() << "\tUsing Size from ObjSizeEval = " << *(SizeOffset.first) << "\n";
				size = SizeOffset.first;
			}
			else{
				Type *t = v->getType();
				if (!isa<Function>(v))
					errs() << "\tUsing manual Size (ObjSizeEval failed) for " << *v << " - type:" << *t << "\n";
				else
					errs() << "\tUsing manual Size (ObjSizeEval failed) for " << ((Function *)v)->getName() << " - type:" << *t << "\n";

				if (t->isPointerTy())
					t = ((PointerType *)t)->getElementType();
				if (ArrayType *arrT = dyn_cast<ArrayType>(t)){
					errs() << "\t\tarray[" << arrT->getNumElements() << " x " << *(arrT->getElementType()) << "]\n";
					
					Constant *arraysize = ConstantInt::get(MySizeType, arrT->getNumElements());
					Constant *totalsize = ConstantInt::get(arraysize->getType(), CurrentDL->getTypeAllocSize(arrT->getElementType()));
					size = llvm::ConstantExpr::getMul(arraysize,totalsize);;
					errs() << "Newly size" << *size << "\n";
				}
				else if (isa<FunctionType>(t)){
					errs() << "\t\t" << *t << " is a FunctionType\n";
					size = ConstantInt::get(MySizeType, 8); // hardcode size to pointer size (i.e., 8)
				}
				else if ((isa<CallInst>(v) || isa<InvokeInst>(v)) && v->getType()->isPointerTy()){
					errs() << "\t\t" << *t << " is a CallInst/InvokeInst returning a pointer type\n";
					// if this is a call to an unininstrumented function that returns a pointer, we don't have info
					size = UnknownSizeConstInt;
				}
				else{
					errs() << "\t\t" << *t << " is not a special-case type for manual sizing\n";
					// last attempt at getting size (for structs)
					if (t->isSized())
						size = ConstantInt::get(MySizeType, CurrentDL->getTypeAllocSize(t));
				}
				errs() << "\tManual Size is " << *size << "\n";
			}
		  return size;
		}

		Value *getOffsetForGEPInst(GetElementPtrInst *GEPInstr) {
			// Quick helper: for a LoadInst of an alloca in the same function, 
			// scan instructions up to that load, picking the last store of a constant.
			// Returns -1 if not resolvable, else the constant.
			auto getLastConstantStore = [&](LoadInst *L, AllocaInst *AI) -> int64_t {
				// If load is in a different function from alloca, bail out
				Function *LF = L->getFunction();
				Function *AF = AI->getFunction();
				if (LF != AF)
					return -1;

				// Track the last constant store we see (in textual order) before the load
				StoreInst *lastStore = nullptr;
				bool foundLoad = false;

				// We do a simple top-down scan of instructions in the function
				// until we reach the load in question.
				for (BasicBlock &BB : *LF) {
					for (Instruction &Inst : BB) {
						// If we’ve just hit the load in question, stop scanning
						if (&Inst == L) {
							foundLoad = true;
							break;
						}
						// If this is a StoreInst to AI, record it
						if (auto *SI = dyn_cast<StoreInst>(&Inst)) {
							if (SI->getPointerOperand() == AI) {
								lastStore = SI;
							}
						}
					}
					if (foundLoad) 
						break;
				}

				// If we found a last store, check if it stores a ConstantInt
				if (lastStore) {
					if (ConstantInt *cst = dyn_cast<ConstantInt>(lastStore->getValueOperand())) {
						return cst->getSExtValue();
					}
				}
				return -1;
			};

			// Helper to see if an alloca has a single integer constant store or to pick the "last" one
			// We first see if there's a single store. If not, we pick the textual last store in the same function.
			auto resolveAllocaStore = [&](LoadInst *L, AllocaInst *AI) -> int64_t {
				// Step A: Try to detect if there's exactly one store overall
				// and it's a constant. If so, return it. If there's more than one,
				// we do the textual "last store" approach.
				StoreInst *uniqueStore = nullptr;
				for (User *U : AI->users()) {
					if (StoreInst *SI = dyn_cast<StoreInst>(U)) {
						if (uniqueStore && uniqueStore != SI) {
							// more than one store -> break
							uniqueStore = nullptr;
							break;
						}
						uniqueStore = SI;
					}
				}
				// If exactly one store was found, see if it’s a constant int
				if (uniqueStore) {
					if (uniqueStore->getPointerOperand() == AI) {
						if (ConstantInt *storeC = dyn_cast<ConstantInt>(uniqueStore->getValueOperand())) {
							return storeC->getSExtValue(); 
						}
					}
				}

				// Step B: If there’s either multiple stores or the single store isn’t constant,
				// we pick the last store *in textual order* before the load in the same function.
				return getLastConstantStore(L, AI);
			};

			// Recursively peel away casts and try to resolve a single constant integer
			std::function<int64_t(Value *)> resolveConstantIndex = [&](Value *V) -> int64_t {
				// Case 1: Direct constant int
				if (auto *CI = dyn_cast<ConstantInt>(V))
					return CI->getSExtValue();

				// Case 2: A load from an alloca (possibly with multiple stores)
				if (auto *LI = dyn_cast<LoadInst>(V)) {
					if (auto *AI = dyn_cast<AllocaInst>(LI->getPointerOperand())) {
						return resolveAllocaStore(LI, AI);
					}
				}

				// Case 3: Some kind of cast instruction (sext, zext, trunc, bitcast, etc.)
				if (auto *castI = dyn_cast<CastInst>(V)) {
					return resolveConstantIndex(castI->getOperand(0));
				}

				// Otherwise, not resolvable
				return -1;
			};

			// 0) Bail out if it’s a vector GEP
			if (GEPInstr->getType()->isVectorTy()) {
				return UnknownSizeConstInt;
			}

			// 1) Try ObjSizeEval
			SizeOffsetEvalType SizeOffset = ObjSizeEval->compute(GEPInstr);
			if (ObjSizeEval->knownOffset(SizeOffset)) {
				errs() << "\tUsing Offset from ObjSizeEval = " << *(SizeOffset.second) << "\n";
				return SizeOffset.second;
			}

			// 2) Try accumulateConstantOffset
			APInt Off(CurrentDL->getPointerTypeSizeInBits(GEPInstr->getType()), 0);
			if (GEPInstr->accumulateConstantOffset(*CurrentDL, Off)) {
				errs() << "\tUsing Offset from GEP.accumulateConstantOffset() = " << Off << "\n";
				return ConstantInt::get(MySizeType, Off);
			}

			// 3) Manual fallback
			uint64_t typeStoreSize = CurrentDL->getTypeStoreSize(GEPInstr->getResultElementType());
			errs() << "\tSize of type of Ptr = " << typeStoreSize << "\n";
			uint64_t totalOffset = 0;

			// Indices start at operand 1
			for (unsigned i = 1; i < GEPInstr->getNumOperands(); ++i) {
				Value *Idx = GEPInstr->getOperand(i);
				int64_t cVal = resolveConstantIndex(Idx);
				if (cVal == -1) {
					errs() << "\tIndex " << i << " not a single constant. Returning unknown.\n";
					return UnknownSizeConstInt;
				}
				errs() << "\tResolved index " << i << " to constant " << cVal << "\n";
				totalOffset += (cVal * typeStoreSize);
			}

			Constant *OffsetConst = ConstantInt::get(MySizeType, totalOffset);
			errs() << "\tUsing Offset from manual evaluation = " << *OffsetConst << "\n";
			return OffsetConst;
		}


		// Helper 1 of processInstruction
		// Logs the start of processing an instruction.
		void logInstructionStart(Instruction *I) {
			std::string addr;
			llvm::raw_string_ostream ss(addr);
			ss << (const void *)I;
			if (I != nullptr){
				errs() << BLUE << "[" << ss.str() << "] " << NORMAL;
			}
		}

		// Helper 2 of processInstruction
		// Processes global variables in the operands of the instruction.
		void processGlobalVariables(Instruction *I) {
			for (Use &U : I->operands()) {
				if (GlobalVariable *GV = dyn_cast<GlobalVariable>(&U)) {
					TheState.Variables[GV].dependentFunctions.insert(
						TheState.Variables[GV].dependentFunctions.begin(),
						I->getFunction()->getName());
				} else if (GEPOperator *gepo = dyn_cast<GEPOperator>(&U)) {
					if (GlobalVariable *GV = dyn_cast<GlobalVariable>(gepo->getPointerOperand())) {
						TheState.Variables[GV].dependentFunctions.insert(
							TheState.Variables[GV].dependentFunctions.begin(),
							I->getFunction()->getName());
					}
					for (auto it = gepo->idx_begin(), et = gepo->idx_end(); it != et; ++it) {
						if (GlobalVariable *GV = dyn_cast<GlobalVariable>(*it)) {
							TheState.Variables[GV].dependentFunctions.insert(
								TheState.Variables[GV].dependentFunctions.begin(),
								I->getFunction()->getName());
						}
					}
				}
			}
		}

		// Helper 3 of processInstruction
		// Processes an `AllocaInst`.
		bool processAllocaInst(AllocaInst *II) {
			bool isArray = II->isArrayAllocation() || II->getType()->getElementType()->isArrayTy();
			errs() << "(+) " << *II << "\t" << DETAIL << " // {";
			if (isArray)
				errs() << " array[" << *(II->getArraySize()) << "]";
			errs() << " (" << *(II->getAllocatedType()) << ") "
				<< "}" << NORMAL << "\n";

			if (II->getAllocatedType()->isPointerTy()) {
				TheState.RegisterVariable(II);
			} 
			else {
				if (Constant *arraysize = dyn_cast_or_null<Constant>(II->getArraySize())) {
					Constant *totalsize = ConstantInt::get(arraysize->getType(),
														CurrentDL->getTypeAllocSize(II->getAllocatedType()));
					totalsize = llvm::ConstantExpr::getMul(arraysize, totalsize);
					TheState.SetSizeForPointerVariable(II, totalsize);
				} else {
					Value *unknownsize = ConstantInt::get(MySizeType, 10000);
					TheState.SetSizeForPointerVariable(II, unknownsize);
				}
			}
			return true;
		}

		// Helper 4 of processInstruction
		// Processes a `CallInst`.
		bool processCallInst(CallInst *II) {
			if (II->getCalledFunction() != NULL) {
				// This code block is not relavant to the core of the analysis.
				// It is the legacy code from NesCheck Pass.
				// Having it here would be helpful if you want to debug heap allocations.
				// Certainly it cannot catch all cases, please customize it based on your use.
				// Or comment it out to save a little bit of analysis time.
				auto funcName = II->getCalledFunction()->getName();
				if (funcName.contains("malloc") && II->getCalledFunction()->arg_size() == 1) {
					errs() << "(M) " << *II << "\n";
					TheState.SetSizeForPointerVariable(II, II->getArgOperand(0));
				} else if (funcName.contains("realloc") && II->getCalledFunction()->arg_size() == 2) {
					errs() << "(M) " << *II << "\n";
					TheState.SetSizeForPointerVariable(II, II->getArgOperand(1));
				} else if (funcName.contains("free") && II->getCalledFunction()->arg_size() == 1) {
					errs() << "(F) " << *II << "\n";
					TheState.SetSizeForPointerVariable(II->getArgOperand(0), NULL);
					propagateFreedSize(II->getArgOperand(0));
				} else {
					errs() << "( ) " << *II << "\n";
					if (II->getType()->isPointerTy())
						TheState.SetSizeForPointerVariable(II, getSizeForValue(II));
				}
				// Until this line

				// This is really important - Propagating return classification.
				updateRewrittenFunctionCall(II);
			}
			return true;
		}

		// Helper 5 of processInstruction
		// Propagates freed size backwards through the chain of instructions.
		void propagateFreedSize(Value *var) {
			while (true) {
				if (LoadInst *LI = dyn_cast<LoadInst>(var)) {
					var = LI->getPointerOperand();
				} else if (BitCastInst *BCI = dyn_cast<BitCastInst>(var)) {
					var = BCI->getOperand(0);
				} else {
					break;
				}
				TheState.SetSizeForPointerVariable(var, NULL);
			}
		}

		// Helper 6 of processInstruction
		// Updates the function call if it was rewritten.
		void updateRewrittenFunctionCall(CallInst *II) {
			if (Function *calledFunc = II->getCalledFunction()) {
				std::string rewrittenName = calledFunc->getName().str() + "_UnifiedMemSafe";
				if (Function *rewrittenFunc = CurrentModule->getFunction(rewrittenName)) {
					for (inst_iterator i = inst_begin(*rewrittenFunc), e = inst_end(*rewrittenFunc); i != e; ++i) {
						if (ReturnInst *RI = dyn_cast_or_null<ReturnInst>(&*i)) {
							if (UnifiedMemSafe::VariableInfo *varinfo = TheState.GetPointerVariableInfo(RI->getOperand(0))) {
								TheState.ClassifyPointerVariable(II, varinfo->classification);
							}
						}
					}
				}
			}
		}

		
		// Helper 7 of processInstruction
		// Processes a `StoreInst`.
		bool processStoreInst(StoreInst *II) {
			Value *valoperand = II->getValueOperand();
			// propagate size metadata
			if (!isa<Function>(valoperand))
				errs() << "(~) " << *II << "\t" << DETAIL << " // {" << *valoperand
					<< " -> " << *(II->getPointerOperand()) << *(II->getPointerOperandType()) << " }" << NORMAL << "\n";
			else
				errs() << "(~) " << *II << "\t" << DETAIL << " // {" << ((Function *)valoperand)->getName()
					<< " -> " << *(II->getPointerOperand()) << " }" << NORMAL << "\n";

			// If we're storing a pointer, propagate its size to the pointer-typed location
			if (valoperand->getType()->isPointerTy()) {
				UnifiedMemSafe::VariableInfo *varinfo = TheState.GetPointerVariableInfo(valoperand);

				// --- FIX: if the pointer hasn't been registered, do it now ---
				if (!varinfo && isa<Constant>(valoperand)) {
					varinfo = TheState.SetSizeForPointerVariable(valoperand, getSizeForValue(valoperand));
				}
				else if (!varinfo) {
					// Even if it's not a constant, attempt a fallback
					varinfo = TheState.SetSizeForPointerVariable(valoperand, getSizeForValue(valoperand));
				}

				if (varinfo != NULL) {
					TheState.ClassifyPointerVariable(II->getPointerOperand(), varinfo->classification);
					TheState.SetSizeForPointerVariable(II->getPointerOperand(), varinfo->size);
				}
			}
			return true;
		}


		// Helper 8 of processInstruction
		// Processes a `LoadInst`.
		bool processLoadInst(LoadInst *II) {
			// propagate size metadata
			errs() << " (~) " << *II << "\n";
			if (II->getType()->isPointerTy()){
				//errs() << " Load Instruction Type: " << *(II->getType()) << "\n";
				Value *ptroperand = II->getPointerOperand();
				UnifiedMemSafe::VariableInfo *varinfo = TheState.GetPointerVariableInfo(ptroperand);
				//                errs()<<"The PTR Operand is: "<<*ptroperand<<" and its classification is : ";
				if (!varinfo && isa<Constant>(ptroperand))
					varinfo = TheState.SetSizeForPointerVariable(ptroperand, getSizeForValue(ptroperand));
				if (varinfo != NULL){
					if (varinfo->hasExplicitSizeVariable && (!varinfo->instantiatedExplicitSizeVariable ||
															(isa<Instruction>(varinfo->size) && ((Instruction *)varinfo->size)->getParent() != II->getParent()))){
						TheState.SetSizeForPointerVariable(ptroperand, varinfo->explicitSizeVariable);
						TheState.SetInstantiatedExplicitSizeVariable(ptroperand, true);
					}
					//errs() << PtrTypeToString(varinfo->classification) << " \n";
					TheState.ClassifyPointerVariable(II, varinfo->classification);
					TheState.SetSizeForPointerVariable(II, varinfo->size);
				}
			}
			else{
			}
			return true;
		}

		// Helper 9 of processInstruction
		// Processes a `GetElementPtrInst`.
		bool processGetElementPtrInst(GetElementPtrInst *II) {
			Value *Ptr = II->getPointerOperand();

			errs() << "(*) " << *II << "\t" << DETAIL << " // {" << *(Ptr) << " (" << *(II->getPointerOperandType()) << ") | " << *(II->getType()) << " -> " << *(II->getResultElementType()) << " }" << NORMAL << "\n";

			errs() << "\tIndices = " << (II->getNumOperands() - 1) << ": ";
			errs() << "\t";
			for (unsigned int operd = 1; operd < II->getNumOperands(); operd++)
				errs() << *(II->getOperand(operd)) << " ; ";
			errs() << "\n";

			// we're accessing the pointer at an offset != 0, classify it as SEQ
			if (!(II->hasAllZeroIndices())){
				TheState.ClassifyPointerVariable(Ptr, UnifiedMemSafe::VariableStates::Seq);
				TheState.ClassifyPointerVariable(II, UnifiedMemSafe::VariableStates::Seq);
			}
			// register the new variable and set size for resulting value
			TheState.RegisterVariable(II);
			if (II->getResultElementType()->isPointerTy()){
				// this GEP needs metadata
				Value* valoperand = II->getPointerOperand();
				UnifiedMemSafe::VariableInfo* varinfo = TheState.GetPointerVariableInfo(valoperand);
			}
			else{
				// set size as originalPtr-offset
				Value* valoperand = Ptr; 
				UnifiedMemSafe::VariableInfo *varinfo = TheState.GetPointerVariableInfo(valoperand);
				//errs() << "\tvarinfo at " << varinfo << "\n ";
			if (varinfo != NULL) {
				Value *otherSize = varinfo->size;

				// Check if the size is zero and fallback to DataLayout or array size
				if (auto *constInt = dyn_cast<ConstantInt>(otherSize)) {
					if (constInt->isZero()) {
						// If size is 0, use DataLayout or the underlying array size
						Type *elementType = II->getSourceElementType();
						if (elementType->isArrayTy()) {
							auto arrayType = cast<ArrayType>(elementType);
							uint64_t arraySize = arrayType->getNumElements();
							uint64_t elementSize = CurrentDL->getTypeAllocSize(arrayType->getElementType());
							otherSize = ConstantInt::get(Type::getInt64Ty(II->getContext()), arraySize * elementSize);
						} else {
							// Fallback to DataLayout for other types
							uint64_t typeSize = CurrentDL->getTypeAllocSize(elementType);
							otherSize = ConstantInt::get(Type::getInt64Ty(II->getContext()), typeSize);
						}
						
						// Use SetSizeForPointerVariable to update the size
						TheState.SetSizeForPointerVariable(valoperand, otherSize);
					}
				}

				if (!(II->hasAllZeroIndices())) {
					Value *Offset = getOffsetForGEPInst(II);
					if (varinfo->size->getType() != Offset->getType()) {
						errs() << RED << "\t!!! varinfo->size->getType() (" << *(varinfo->size->getType()) << ") != Offset->getType() (" << *(Offset->getType()) << ")\n"
							<< NORMAL;
						errs() << GREEN <<"\t Converting Offset and calculating new size\n" << NORMAL; 
					}
					Constant *offset = dyn_cast_or_null<Constant>(Offset);
					Constant *othersize = dyn_cast_or_null<Constant>(otherSize);
					if (offset && othersize) {
						// Increment the offset of the resulting pointer, only for resulting pointer, base pointer stays the same.
						otherSize = llvm::ConstantExpr::getSub(othersize, offset);
					}
				}
				TheState.SetSizeForPointerVariable(II, otherSize);
			}
			}
			return true;
		}

		// Helper 10 of processInstruction
		// Processes a `CastInst`.
		bool processCastInst(CastInst *II) {
			if (!II)
				return false;

			// Log cast instruction details
			logCastInstructionDetails(II);

			Type *srcT = II->getSrcTy();
			Type *dstT = II->getDestTy();

			if (!srcT || !dstT) {
				errs() << "Invalid source or destination type for CastInst: " << *II << "\n";
				return false;
			}
			if (!II->getOperand(0)) {
				errs() << "Null operand for instruction: " << *II << "\n";
				return false;
			}

			// Attempt to retrieve pointer info for the operand
			UnifiedMemSafe::VariableInfo *varinfo = TheState.GetPointerVariableInfo(II->getOperand(0));
			if (!varinfo) {
				errs() << "\tPointerVariableInfo not found for operand: " << *(II->getOperand(0)) << "\n\tCreating and Recheck\n";
				// --- FIX: if the operand is a pointer, create a VariableInfo now ---
				if (II->getOperand(0)->getType()->isPointerTy()) {
					varinfo = TheState.SetSizeForPointerVariable(II->getOperand(0),
																getSizeForValue(II->getOperand(0)));
				}
				// If still no varinfo, bail out
				if (!varinfo)
					return false;
			}

			Type *innerSrcT = unwrapPointer(srcT);
			Type *innerDstT = unwrapPointer(dstT);

			if (isCastOfInterest(srcT, dstT, innerSrcT, innerDstT)) {
				errs() << *II << "  Cast of Interest!\n";

				// If the source isn't a pointer type, handle integer-based casts
				if (!srcT->isPointerTy()) {
					if (isa<ZExtInst>(II) || isa<SExtInst>(II) || isa<TruncInst>(II)) {
						classifyExtOrTruncInst(cast<UnaryInstruction>(II));
					}
					return true;
				}

				// Handle various operand types for the cast
				if (LoadInst *III = dyn_cast_or_null<LoadInst>(II->getOperand(0))) {
					processLoadOperand(II, III, innerSrcT, innerDstT);
				}
				else if (GetElementPtrInst *III = dyn_cast_or_null<GetElementPtrInst>(II->getOperand(0))) {
					processGEPOperand(II, III, innerSrcT, innerDstT);
				}
				else if (CastInst *CInst = dyn_cast_or_null<CastInst>(II->getOperand(0))) {
					processCastOperand(II, CInst, innerSrcT, innerDstT);
				}
				else if (isa<CallInst>(II->getOperand(0))) {
					processCallOperand(II, varinfo);
				}
				else {
					errs() << "\tIgnored classification of variable since we have no operand\n";
				}

				// Propagate size metadata from the operand to the cast
				propagateSizeMetadata(II, varinfo);
			}

			return true;
		}


		// Logs the details of the cast instruction
		void logCastInstructionDetails(CastInst *II) {
			Type *srcT = II->getSrcTy();
			Type *dstT = II->getDestTy();
			errs() << "(>) " << *II << "\t" << DETAIL << " // { " << *srcT << " " << countIndirections(srcT)
				<< " into " << *dstT << " " << countIndirections(dstT) << " }" << NORMAL << "\n";
		}

		// Determines if a cast is of interest based on types
		bool isCastOfInterest(Type *srcT, Type *dstT, Type *innerSrcT, Type *innerDstT) {
			//return true;

			// Change it to always true if you would like to analyze integer type cast.
			// Results will be largely overapproximated since LLVM treats char* as integer type as well.
			return countIndirections(srcT) != countIndirections(dstT) || !innerSrcT->isIntegerTy() || !innerDstT->isIntegerTy();
		}

		// Processes a `LoadInst` operand for a cast
		void processLoadOperand(CastInst *II, LoadInst *III, Type *innerSrcT, Type *innerDstT) {
			TheState.ClassifyPointerVariable(II->getOperand(0), UnifiedMemSafe::VariableStates::Dyn);
			TheState.ClassifyPointerVariable(II, UnifiedMemSafe::VariableStates::Dyn);

			Type *realSrcType = unwrapPointer(III->getType());
			Type *realDstType = findRealDstType(II, innerDstT);

			logDowncastAnalysis(II, realSrcType, realDstType, innerSrcT, innerDstT);
		}

		// Processes a `GetElementPtrInst` operand for a cast
		void processGEPOperand(CastInst *II, GetElementPtrInst *III, Type *innerSrcT, Type *innerDstT) {
			TheState.ClassifyPointerVariable(II->getOperand(0), UnifiedMemSafe::VariableStates::Dyn);
			TheState.ClassifyPointerVariable(II, UnifiedMemSafe::VariableStates::Dyn);

			Type *realSrcType = unwrapPointer(III->getResultElementType());
			Type *realDstType = findRealDstType(II, innerDstT);

			logDowncastAnalysis(II, realSrcType, realDstType, innerSrcT, innerDstT);
		}

		// Processes a `CastInst` operand for a cast
		void processCastOperand(CastInst *II, CastInst *CInst, Type *innerSrcT, Type *innerDstT) {
			TheState.ClassifyPointerVariable(II->getOperand(0), UnifiedMemSafe::VariableStates::Dyn);
			TheState.ClassifyPointerVariable(II, UnifiedMemSafe::VariableStates::Dyn);

			Type *realSrcType = unwrapPointer(CInst->getSrcTy());
			Type *realDstType = findRealDstType(II, innerDstT);

			logDowncastAnalysis(II, realSrcType, realDstType, innerSrcT, innerDstT);
		}

		// Processes a `CallInst` operand for a cast
		void processCallOperand(CastInst *II, UnifiedMemSafe::VariableInfo *varinfo) {
			if (isa<BitCastInst>(II) && isa<ConstantInt>(varinfo->size) &&
				((ConstantInt *)varinfo->size)->getZExtValue() == 1) {
				TheState.SetSizeForPointerVariable(II->getOperand(0), getSizeForValue(II));
			}
			TheState.ClassifyPointerVariable(II->getOperand(0), UnifiedMemSafe::VariableStates::Dyn);
			TheState.ClassifyPointerVariable(II, UnifiedMemSafe::VariableStates::Dyn);
		}

		// Finds the real destination type after a cast operation
		Type *findRealDstType(CastInst *II, Type *innerDstT) {
			Type *realDstType = NULL;

			for (Use &use : II->uses()) {
				User *user = use.getUser();
				Instruction *userInst = dyn_cast<Instruction>(user);

				if (StoreInst *SI = dyn_cast_or_null<StoreInst>(userInst)) {
					realDstType = unwrapPointer(SI->getPointerOperandType());
					errs() << "LoadCast: Found Store Inst After Cast!\n"
						<< *II << "\t" << *SI << "\t" << *realDstType << "\n";
					break;
				} else if (LoadInst *LI = dyn_cast_or_null<LoadInst>(userInst)) {
					realDstType = findLoadDstType(LI, II);
					break;
				} else if (CastInst *CI = dyn_cast_or_null<CastInst>(userInst)) {
					realDstType = unwrapPointer(CI->getDestTy());
					errs() << "LoadCast: Found Cast Inst After Cast!\n" << *II << "\n" << *CI << "\n";
					break;
				}
			}

			return realDstType ? realDstType : innerDstT;
		}

		// Finds the real destination type after a `LoadInst`
		Type *findLoadDstType(LoadInst *LI, CastInst *II) {
			Type *realDstType = unwrapPointer(LI->getType());
			for (Use &LIuse : LI->uses()) {
				User *LIuser = LIuse.getUser();
				Instruction *LIuserInst = dyn_cast<Instruction>(LIuser);
				if (CastInst *CII = dyn_cast_or_null<CastInst>(LIuserInst)) {
					realDstType = unwrapPointer(CII->getDestTy());
					errs() << "LoadCast: Found Cast Inst for After Load Cast!\n" << *II << "\n" << *CII << "\n";
					break;
				}
			}
			errs() << "LoadCast: Found Load Inst After Cast!\n" << *II << "\n" << *LI << "\n";
			return realDstType;
		}

		// Logs downcast analysis results
		void logDowncastAnalysis(CastInst *II, Type *realSrcType, Type *realDstType, Type *innerSrcT, Type *innerDstT) {
			for (Type::subtype_iterator STI = realSrcType->subtype_begin(),
										STE = realSrcType->subtype_end();
				STI != STE; ++STI) {
				if ((llvm::Type *)STI == realDstType) {
					errs() << "Load Downcast: " << *II << " From: " << *realSrcType << " To: " << *realDstType << "\n";
					return;
				}
			}

			errs() << "No Load Downcast: " << *II << " From: " << *realSrcType << " To: " << *realDstType << "\n";

			if (realSrcType->isIntegerTy() && innerSrcT->isIntegerTy() &&
				(!realDstType->isIntegerTy() || !innerDstT->isIntegerTy())) {
				errs() << "Potential Downcast: " << *II << " From: " << *realSrcType << " To: " << *realDstType << "\n";
			}
		}

		// Propagates size metadata
		void propagateSizeMetadata(CastInst *II, UnifiedMemSafe::VariableInfo *varinfo) {
			if (varinfo != 0x0) {
				TheState.SetSizeForPointerVariable(II, varinfo->size);
			} else {
				errs() << "!!! DON'T KNOW variable or doesn't have size\n";
			}
		}

		void classifyExtOrTruncInst(Instruction *I) {
			if (!I)
				return;

			// Log the instruction
			errs() << "(EXTENSION/TRUNCATION) " << *I << "\n";

			// Determine if the instruction could change the value
			bool couldChangeValue = false;

			if (ZExtInst *ZExt = dyn_cast<ZExtInst>(I)) {
					// Zero extension only adds bits, so value never gets larger or become negative.
					couldChangeValue = false; 
			} 
			
			else if (SExtInst *SExt = dyn_cast<SExtInst>(I)) {
				errs() << "Handling SExtInst: " << *SExt << "\n";

				Type *srcType = SExt->getSrcTy();
				Type *dstType = SExt->getDestTy();
				
				// Signed Extension can change value to make it larger or become negative.
				if (srcType->isIntegerTy() && dstType->isIntegerTy()) {
					couldChangeValue = true;
				}
			} 
			
			else if (TruncInst *Trunc = dyn_cast<TruncInst>(I)) {
				errs() << "Handling TruncInst: " << *Trunc << "\n";

				Type *srcType = Trunc->getSrcTy();
				Type *dstType = Trunc->getType();

				if (srcType->isIntegerTy() && dstType->isIntegerTy()) {
					unsigned srcBitWidth = srcType->getIntegerBitWidth();
					unsigned dstBitWidth = dstType->getIntegerBitWidth();

					if (srcBitWidth > dstBitWidth) {
						Value *operand = Trunc->getOperand(0);
						errs() << "Operand of TruncInst: " << *operand << "\n";

						if (auto *loadInst = dyn_cast<LoadInst>(operand)) {
							Value *pointerOperand = loadInst->getPointerOperand();
							errs() << "Pointer operand of LoadInst: " << *pointerOperand << "\n";

							for (User *user : pointerOperand->users()) {
								if (auto *storeInst = dyn_cast<StoreInst>(user)) {
									Value *storedValue = storeInst->getValueOperand();
									errs() << "Found StoreInst: " << *storeInst << "\n";
									errs() << "Stored value: " << *storedValue << "\n";
									// Truncating constant value could result in value change.
									// Positive to negative can make the result be negative.
									// Negative to Positive can make the result be very large.
									// LLVM IR does not carry the signedness of resulting value.
									// Assuming all unsafe for soundness.
									if (auto *constantInt = dyn_cast<ConstantInt>(storedValue)) {
											couldChangeValue = true;
									}
									// Non-constant value can change.
									else {
										couldChangeValue = true;
									}
									break;
								}
							}
						} 
						else {
							errs() << "Operand is neither a LoadInst nor a constant, assuming potential signedness change.\n";
							couldChangeValue = true;
						}
					}
				}
			}

			// Perform classification if the value could change
			if (couldChangeValue) {
				TheState.ClassifyPointerVariable(I->getOperand(0), UnifiedMemSafe::VariableStates::Dyn);
				TheState.ClassifyPointerVariable(I, UnifiedMemSafe::VariableStates::Dyn);
			}
		}



		bool processInstruction(Instruction *I) {
			if (!I)
				return false;

			bool changed = false;
			logInstructionStart(I);

			// Process global variables in operands
			processGlobalVariables(I);

			// Handle specific instruction types
			if (AllocaInst *II = dyn_cast_or_null<AllocaInst>(I)) {
				changed = processAllocaInst(II);
			} else if (CallInst *II = dyn_cast_or_null<CallInst>(I)) {
				changed = processCallInst(II);
			} else if (ReturnInst *RI = dyn_cast_or_null<ReturnInst>(I)) {
				// Classification is already propagated, print it here for reference.
    			errs() << "(R) " << *RI << "\n";
			} else if (StoreInst *II = dyn_cast_or_null<StoreInst>(I)) {
				changed = processStoreInst(II);
			} else if (LoadInst *II = dyn_cast_or_null<LoadInst>(I)) {
				changed = processLoadInst(II);
			} else if (GetElementPtrInst *II = dyn_cast_or_null<GetElementPtrInst>(I)) {
				changed = processGetElementPtrInst(II);
			} else if (CastInst *II = dyn_cast_or_null<CastInst>(I)) {
				changed = processCastInst(II);
			} else {
				errs() << DETAIL << " " << *I << NORMAL << "\n";
			}

			return changed;
		}

		void analyzeFunction(Function *F){
			errs() << "\n\n*********\n ANALYZING FUNCTION: " << F->getName() << "\n";
			if (isCurrentFunctionWhitelisted){
				errs() << "\t[whitelisted]\n";
			}
			if (isCurrentFunctionWhitelistedForInstrumentation){
				errs() << "\t[whitelisted for instrumentation]\n";
			}

			TheState.RegisterFunction(F);

			//TrapBB = nullptr;

			std::vector<Instruction *> instructionsToAnalyze;
			for (inst_iterator i = inst_begin(*F), e = inst_end(*F); i != e; ++i){
				Instruction *I = &*i;
				instructionsToAnalyze.push_back(I);
			}
			for (Instruction *I : instructionsToAnalyze){
				processInstruction(I);
			}
		}

		void printStats(){
			errs() << NORMAL << "\n\n\n-------------CCured MEMORY SAFETY ANALYSIS RESULTS-------------\n\n";
			errs() << TheState.GetVariablesStateAsString() << "\n";

			CCuredSafePtrs += TheState.GetSafePointerCount();
			CCuredSeqPtrs += TheState.GetSeqPointerCount();
			CCuredDynPtrs += TheState.GetDynPointerCount();
			errs() << "\n\n";
		}


		void registerGlobals(Module &M)
		{
			// Registering globals
			for (auto i = M.global_begin(), e = M.global_end(); i != e; ++i)
			{
				Value *gv = &*i;
				TheState.RegisterVariable(gv);
				TheState.Variables[gv].isGlobal = true;
				if (gv->getType()->isPointerTy())
				{
					TheState.SetSizeForPointerVariable(gv, getSizeForValue(gv));
				}
			}
		}

		void collectFunctionsToAnalyze(Module &M, std::vector<Function *> &FunctionsToAnalyze)
		{
    		// DO NOT store a pointer to a local ObjectSizeOffsetEvaluator here
			// Rely on the one created in runOnModule.
			for (auto i = M.begin(), e = M.end(); i != e; ++i)
			{
				Function *F = &*i;
				// skip declarations and specific library functions
				if (F->isDeclaration())
					continue;

				// If need function-specific TLI:
				// const TargetLibraryInfo *FuncTLI = &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI(*F);

				StringRef fname = F->getName();
				if (fname == "printCheck" || fname == "printErrorLine" || fname == "printFaultInjectionExecuted" ||
					fname == "setMetadataTableEntry" || fname == "lookupMetadataTableEntry" || fname == "findMetadataTableEntry")
					continue;

				FunctionsToAnalyze.push_back(F);
			}
		}

		void analyzeAllFunctions(std::vector<Function *> &FunctionsToAnalyze)
		{
			// Analyze all functions (populate Instrumentation WorkList, etc.)
			for (Function *F : FunctionsToAnalyze)
			{
				analyzeFunction(F);
			}
		}

		void classificationPropagation(Module &M, pdg::PTAWrapper &ptaw)
		{
			std::set<StringRef> functionsToAnalyze;
			Function *F = nullptr;

			// For each variable, if it's global and classification changed
			for (auto it = TheState.Variables.begin(); it != TheState.Variables.end(); it++) {
				if (it->second.isGlobal && it->second.didClassificationChange) {
					// Insert dependent functions
					for (auto &depFuncName : it->second.dependentFunctions) {
						functionsToAnalyze.insert(functionsToAnalyze.begin(), depFuncName);
						errs() << depFuncName << " ";
					}
					errs() << "\n";

					// Reset the flag
					it->second.didClassificationChange = false;

					// Re-scan each function that needs analyzing
					for (auto &funcName : functionsToAnalyze) {
						F = M.getFunction(funcName);
						if (F == nullptr) 
							continue;

						// Iterate over all instructions
						for (inst_iterator i = inst_begin(*F), e = inst_end(*F); i != e; ++i) {
							// Check each operand
							for (Use &U : (&*i)->operands()) {
								// If the operand is exactly the global var that changed
								if (it->first == dyn_cast<GlobalVariable>(U)) {
									// Re-iterate instructions to check aliasing
									for (inst_iterator inst = inst_begin(*F), ie = inst_end(*F); inst != ie; ++inst) {
										if (&*i == &*inst)
											continue;

										Instruction *InstGlobalOperand = &*i;
										Instruction *InstReAnalyze     = &*inst;

										// Ensure SVF sees these instructions
											//Prevent this scenario from happening
											if (!(ptaw._ander_pta)||
												!(ptaw._ander_pta->getPAG()->hasValueNode(InstGlobalOperand)) || 
												!(ptaw._ander_pta->getPAG()->hasValueNode(InstReAnalyze)))
												continue;

										// Query alias
										auto aliasResult = ptaw.queryAlias(*InstGlobalOperand, *InstReAnalyze);
										if (aliasResult != NoAlias) {
											// Process if alias found
											processInstruction(InstReAnalyze);
										}
									}
								}
							}
						}
					}
					// Clear set before the next global
					functionsToAnalyze.clear();
				}
    		}
		}

		void getAnalysisUsage(AnalysisUsage &AU) const override{
			AU.addRequired<TargetLibraryInfoWrapperPass>();
			AU.addRequired<pdg::ProgramDependencyGraph>();
			//AU.addRequired<LoopInfoWrapperPass>();
			//AU.setPreservesAll();
		}

		bool runOnModule(Module &M) override{
			srand(time(NULL));

			errs() << "\n\n#############\n MODULE: " << M.getName() << "\n";

			// Example: retrieve ProgramDependencyGraph
			pdg::ProgramGraph *pdgraph = getAnalysis<pdg::ProgramDependencyGraph>().getPDG();

			// Retrieve the PTAWrapper instance
			pdg::PTAWrapper &ptaw = pdg::PTAWrapper::getInstance();

			// Retrieve TLI for the *first* function (often used for a module-level default).
			const TargetLibraryInfo *TLI = &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI(*M.begin());

			CurrentModule = &M;
			CurrentDL = &M.getDataLayout();

			// For example, a 64-bit integer type for sizing
			MySizeType = Type::getInt64Ty(M.getContext());

			// Create one permanent ObjectSizeOffsetEvaluator for the entire pass:
			static ObjectSizeOffsetEvaluator TheObjSizeEval(*CurrentDL, TLI, M.getContext());
			// Store its address in our class member
			ObjSizeEval = &TheObjSizeEval;

			// Example of whitelisted functions
			WhitelistedFunctions = {
				"active_message_deliver", "arrangeKey", "fillInOutput",
				"is_empty", "makeNoiseModel", "makePmfDistr",
				"RandomInitialise", "RandomUniform"
			};

			// Example of a big constant int
			UnknownSizeConstInt = cast<ConstantInt>(ConstantInt::get(MySizeType, 10000000));

			// Set up TheState
			TheState.SetSizeType(MySizeType);

			// 1) Register all globals
			registerGlobals(M);

			// 2) Collect functions to analyze
			std::vector<Function *> FunctionsToAnalyze;
			collectFunctionsToAnalyze(M, FunctionsToAnalyze);

			// 3) Analyze them
			analyzeAllFunctions(FunctionsToAnalyze);

			// 4) Classification propagation
			classificationPropagation(M, ptaw);

			// 5) Print stats (and do your final steps)
			printStats();

			
			UnifiedMemSafe::Uriah::identifyDifferentKindsOfUnsafeHeapPointers(
				heapPointerSet,
				TheState,
				CurrentModule,
				TLI,
				ptaw,
				pdgraph,
				edge_types,
				AliasedWithHeapSeqPointers,
				AliasedWithHeapDynPointers
			);

			UnifiedMemSafe::DataGuard::identifyDifferentKindsOfUnsafeStackPointers(
				heapPointerSet,
				TheState,
				CurrentModule,
				TLI,
				ptaw
			);

			return false;
		}
	};
}

char UnifiedMemSafePass::ID = 0;
static RegisterPass<UnifiedMemSafePass> X("unified", "Unified memory safety validation", false, false);