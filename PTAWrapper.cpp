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
 
#include "PTAWrapper.hh"

using namespace llvm;
using namespace SVF;

void alias::PTAWrapper::setupPTA(Module &M)
{
  SVFModule *module = LLVMModuleSet::getLLVMModuleSet()->buildSVFModule(M);
  PAGBuilder builder;
  PAG *pag = builder.build(module);
  _ander_pta = AndersenWaveDiff::createAndersenWaveDiff(pag);
}

AliasResult alias::PTAWrapper::queryAlias(Value &v1, Value &v2)
{
  assert(_ander_pta != nullptr && "cannot obtain ander pointer analysis!\n");
  return _ander_pta->alias(&v1, &v2);
}
  //PAG* alias::PTAWrapper::getPAG() override
	//{
	//	return pag;
	//}
