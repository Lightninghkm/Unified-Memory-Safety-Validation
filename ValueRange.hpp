#ifndef _ValueRange_
#define _ValueRange_
#include "DataflowAnalysis.h"
#include "Utils.hpp"
using namespace llvm;
void valueRangeAnalysis(Module *, std::map<const UnifiedMemSafe::VariableMapKeyType *, UnifiedMemSafe::VariableInfo>, UnifiedMemSafe::AnalysisState);
#endif
