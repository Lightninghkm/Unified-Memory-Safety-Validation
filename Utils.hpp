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
 
#pragma once

#include "llvm/IR/Instructions.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Constants.h"
#include "llvm/Support/raw_ostream.h"

#include <sstream>
#include <string>
#include <set>
#include <stdio.h>
#include <stdlib.h>


#define USE_COLORED_OUTPUT 1
#if USE_COLORED_OUTPUT
    #define RED     "\033[0;31m"
    #define GREEN   "\033[0;32m"
    #define BLUE    "\033[0;34m"
    #define GRAY    "\033[1;30m"
    #define DETAIL  "\033[1;36m"
    #define NORMAL  "\033[0m"
#else
    #define RED     ""
    #define GREEN   ""
    #define BLUE    ""
    #define GRAY    ""
    #define DETAIL  ""
    #define NORMAL  ""
#endif


using namespace llvm;

namespace UnifiedMemSafe {

	typedef llvm::Value VariableMapKeyType;

	enum class VariableStates {
		Unknown = -1,
		Safe = 0,
		Seq = 1,
		Dyn = 2,
	};
	inline static std::string PtrTypeToString(VariableStates ptrType){
	    return ptrType == VariableStates::Safe ? "SAFE" :
	            (ptrType == VariableStates::Seq ? "SEQ" :
	                (ptrType == VariableStates::Dyn ? "DYN" : "UNKNOWN")
	            );
	}

	inline static std::string getIdentifyingName(const VariableMapKeyType *Decl) {
	    std::string addr;
	    llvm::raw_string_ostream ss(addr);
	    ss << (const void *)Decl;
	    if (Decl != nullptr)
	    	return Decl->getName().str() + "[" + ss.str() + "]";
	    return "";
	}


	typedef struct {
		VariableStates classification;
		Value* size;
		bool hasMetadataTableEntry;
		bool hasExplicitSizeVariable;
		bool instantiatedExplicitSizeVariable;
		Value* explicitSizeVariable;
		//Fix  - to address the worklist issue
		bool isGlobal=false;
		bool didClassificationChange=false;
		std::set<StringRef> dependentFunctions;
	} VariableInfo;


 

	class AnalysisState {
	private:
		int numFunctions = 0;
	public:
        std::map<VariableMapKeyType const *, VariableInfo> Variables;
        AnalysisState();
		void SetSizeType(llvm::Type* st);
		void RegisterFunction(Function *func);
	    void RegisterVariable(const VariableMapKeyType *Decl);
	    void ClassifyPointerVariable(const VariableMapKeyType *Ref, VariableStates ptrType);
	    VariableInfo * SetSizeForPointerVariable(const VariableMapKeyType *Ref, Value *size);
	    void SetExplicitSizeVariableForPointerVariable(const VariableMapKeyType *Ref, Value *explicitSize);
	    void SetInstantiatedExplicitSizeVariable(const VariableMapKeyType *Ref, bool v);
	    void SetHasMetadataTableEntry(const VariableMapKeyType *Ref);
	    VariableInfo * GetPointerVariableInfo(VariableMapKeyType *Ref);

	    std::string GetVariablesStateAsString();
	    int GetSafePointerCount();
	    int GetSeqPointerCount();
	    int GetDynPointerCount();
	    int GetHasMetadataTableEntryCount();
	};

}




