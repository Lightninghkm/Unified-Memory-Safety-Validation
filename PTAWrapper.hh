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
 
#ifndef _PTAWRAPPER_H_
#define _PTAWRAPPER_H_
#include "LLVMEssentials.hh"
#include "SVF-FE/PAGBuilder.h"
#include "WPA/Andersen.h"
#include "SVF-FE/LLVMUtil.h"


namespace alias
{
  class PTAWrapper final
  {
  public:
    PTAWrapper() = default;
    PTAWrapper(const PTAWrapper &) = delete;
    PTAWrapper(PTAWrapper &&) = delete;
    PTAWrapper &operator=(const PTAWrapper &) = delete;
    PTAWrapper &operator=(PTAWrapper &&) = delete;
    static PTAWrapper &getInstance()
    {
      static PTAWrapper ptaw{};
      return ptaw;
    }
    void setupPTA(llvm::Module &M);
    bool hasPTASetup() { return (_ander_pta != nullptr); }
    llvm::AliasResult queryAlias(llvm::Value &v1, llvm::Value &v2);
    //SVF::PAG* getPAG();
    SVF::AndersenWaveDiff *_ander_pta;
  };
} 

#endif
