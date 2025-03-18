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

#ifndef DATAFLOW_ANALYSIS_H
#define DATAFLOW_ANALYSIS_H

#include <algorithm>
#include <deque>
#include <numeric>

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Analysis/LoopInfo.h"
//#include "llvm/Analysis/Dominators.h"

namespace llvm {

template<unsigned long Size>
struct DenseMapInfo<std::array<llvm::Instruction*, Size>> {
  using Context = std::array<llvm::Instruction*, Size>;
  static inline Context
  getEmptyKey() {
    Context c;
    std::fill(c.begin(), c.end(),
              llvm::DenseMapInfo<llvm::Instruction*>::getEmptyKey());
    return c;
  }
  static inline Context
  getTombstoneKey() {
    Context c;
    std::fill(c.begin(), c.end(),
              llvm::DenseMapInfo<llvm::Instruction*>::getTombstoneKey());
    return c;
  }
  static unsigned
  getHashValue(const Context& c) {
    return llvm::hash_combine_range(c.begin(), c.end());
  }
  static bool
  isEqual(const Context& lhs, const Context& rhs) {
    return lhs == rhs;
  }
};

} // end namespace llvm


namespace analysis {

//A simple worklist class that ensures each element is enqueued at most once.

template<typename T>
class WorkList {
public:
  template<typename IterTy>
  WorkList(IterTy i, IterTy e)
    : inList{},
      work{i, e} {
    inList.insert(i, e);
    // Debug prints for initial population
    /*
    for (auto it = i; it != e; ++it) {
      llvm::errs() << "[WorkList ctor] Enqueued initially: " << printElement(*it) << "\n";
    }
    */
  }

  WorkList()
    : inList{},
      work{} { }

  bool empty() const { return work.empty(); }
  bool contains(T elt) const { return inList.count(elt); }

  // Insert debug prints to see which items get added
  void add(T elt) {
    if (!inList.count(elt)) {
      work.push_back(elt);
      inList.insert(elt);
      //llvm::errs() << "[WorkList::add] Enqueued: " << printElement(elt) << "\n";
    }
  }

  // Insert debug prints to see which items get taken
  T take() {
    T front = work.front();
    work.pop_front();
    inList.erase(front);
    //llvm::errs() << "[WorkList::take] Dequeued: " << printElement(front) << "\n";
    return front;
  }

private:
  llvm::DenseSet<T> inList;
  std::deque<T> work;

  // ---------- Debug-print helpers ----------
  template <typename U>
  std::string printElement(const U &elt) const {
    std::string result;
    llvm::raw_string_ostream stream(result);
    stream << elt;
    return result;
  }

  // Overload for std::pair<Context,llvm::Function*>
  template <typename U1, typename U2>
  std::string printElement(const std::pair<U1, U2> &p) const {
    // U2 is likely llvm::Function*
    // Handle printing U1 (std::array<Instruction*,Size>) below
    std::string result;
    llvm::raw_string_ostream stream(result);
    stream << "(" << printElement(p.first) << ", ";

    if (p.second) {
      stream << p.second->getName();
    } else {
      stream << "nullfunction";
    }
    stream << ")";
    return result;
  }

  // Overload for std::array<llvm::Instruction*, Size>
  template <typename U, std::size_t N>
  std::string printElement(const std::array<U, N> &arr) const {
    std::string result;
    llvm::raw_string_ostream stream(result);
    stream << "[";
    for (std::size_t i = 0; i < N; i++) {
      if (i > 0) stream << ",";
      if (arr[i]) {
        stream << (void*)arr[i];
      } else {
        stream << "nullinst";
      }
    }
    stream << "]";
    return result;
  }
};

using BasicBlockWorklist = WorkList<llvm::BasicBlock*>;



// AbstractValue, AbstractState, and DataflowResult definitions
// The dataflow analysis computes three different granularities of results.
// An AbstractValue represents information in the abstract domain for a single
// LLVM Value. An AbstractState is the abstract representation of all values
// relevent to a particular point of the analysis. A DataflowResult contains
// the abstract states before and after each instruction in a function. The
// incoming state for one instruction is the outgoing state from the previous
// instruction. For the first instruction in a BasicBlock, the incoming state is
// keyed upon the BasicBlock itself.
//
// Note: In all cases, the AbstractValue should have a no argument constructor
// that builds constructs the initial value within the abstract domain.

template <typename AbstractValue>
using AbstractState = llvm::DenseMap<llvm::Value*, AbstractValue>;

template <typename AbstractValue>
using DataflowResult = llvm::DenseMap<llvm::Value*, AbstractState<AbstractValue>>;

template <typename AbstractValue>
bool
operator==(const AbstractState<AbstractValue>& s1,
           const AbstractState<AbstractValue>& s2) {
  if (s1.size() != s2.size()) {
    return false;
  }
  return std::all_of(s1.begin(), s1.end(),
                     [&s2](auto &kvPair) {
                       auto found = s2.find(kvPair.first);
                       return found != s2.end() && found->second == kvPair.second;
                     });
}

template <typename AbstractValue>
AbstractState<AbstractValue>&
getIncomingState(DataflowResult<AbstractValue>& result, llvm::Instruction& i) {
  auto* bb = i.getParent();
  auto* key = (&bb->front() == &i)
    ? static_cast<llvm::Value*>(bb)
    : static_cast<llvm::Value*>(&*--llvm::BasicBlock::iterator{i});
  return result[key];
}


// A dummy Transfer policy example (for reference).
// NOTE: This class is not intended to be used. It is only intended to
// to document the structure of a Transfer policy object as used by the
// DataflowAnalysis class. For a specific analysis, you should implement
// a class with the same interface.

template <typename AbstractValue>
class Transfer {
public:
  void
  operator()(llvm::Value& v, AbstractState<AbstractValue>& s) {
    llvm_unreachable("unimplemented transfer");
  }
};


// Meet operator base class using CRTP.

// This class can be extended with a concrete implementation of the meet
// operator for two elements of the abstract domain. Implementing the
// meetPair() method in the subclass will enable it to be used within the
// general meet operator because of the curiously recurring template pattern.
template <typename AbstractValue, typename SubClass>
class Meet {
public:
  AbstractValue
  operator()(llvm::ArrayRef<AbstractValue> values) {
    return std::accumulate(values.begin(), values.end(),
                           AbstractValue(),
                           [this](auto v1, auto v2) {
                             return this->asSubClass().meetPair(v1, v2);
                           });
  }

  AbstractValue
  meetPair(AbstractValue& v1, AbstractValue& v2) const {
    llvm_unreachable("unimplemented meet");
  }

private:
  SubClass& asSubClass() { return static_cast<SubClass&>(*this); }
};


template <typename AbstractValue,
          typename Transfer,
          typename Meet,
          unsigned long ContextSize=1ul>
class ForwardDataflowAnalysis {
public:
  using State   = AbstractState<AbstractValue>;
  using Context = std::array<llvm::Instruction*, ContextSize>;

  using FunctionResults = DataflowResult<AbstractValue>;
  using ContextFunction = std::pair<Context, llvm::Function*>;
  using ContextResults  = llvm::DenseMap<llvm::Function*, FunctionResults>;
  using ContextWorklist = WorkList<ContextFunction>;

  using ContextMapInfo =
    llvm::DenseMapInfo<std::array<llvm::Instruction*, ContextSize>>;
  using AllResults = llvm::DenseMap<Context, ContextResults, ContextMapInfo>;

  ForwardDataflowAnalysis(llvm::Module& m,
                          llvm::ArrayRef<llvm::Function*> entryPoints) {
    //llvm::errs() << "[ForwardDataflowAnalysis ctor] EntryPoints: "<< entryPoints.size() << "\n";
    for (auto* entry : entryPoints) {
      //llvm::errs() << "  - Queuing entry function: " << entry->getName() << "\n";
      contextWork.add({Context{}, entry});
    }
  }


  // computeForwardDataflow collects the dataflow facts for all instructions
  // in the program reachable from the entryPoints passed to the constructor.

  AllResults
  computeForwardDataflow() {
    //llvm::errs() << "[computeForwardDataflow] Starting main loop...\n";
    while (!contextWork.empty()) {
      auto [context, function] = contextWork.take();
      //llvm::errs() << "[computeForwardDataflow] Dequeued (Context,Function): "<< function->getName() << "\n";
      computeForwardDataflow(*function, context);
    }
    //llvm::errs() << "[computeForwardDataflow] Done.\n";
    return allResults;
  }

  // computeForwardDataflow collects the dataflowfacts for all instructions
  // within Function f with the associated execution context. Functions whose
  // results are required for the analysis of f will be transitively analyzed.

  DataflowResult<AbstractValue>
  computeForwardDataflow(llvm::Function& f, const Context& context) {
    //llvm::errs() << "[computeForwardDataflow(Function)] Start: "<< f.getName() << "\n";

    active.insert({context, &f});

    // Create or retrieve the current function-level results
    // First compute the initial outgoing state of all instructions
    FunctionResults &fnResultsRef =
      allResults.FindAndConstruct(context).second.FindAndConstruct(&f).second;
    // NOTE: Reference fnResultsRef to mutate it in-place.

    // 1. Pre-populate result entries for all instructions & blocks
    //    to not keep "discovering" them and re-queueing.
    if (fnResultsRef.find(&f) == fnResultsRef.end()) {
      for (auto& I : llvm::instructions(f)) {
        fnResultsRef.FindAndConstruct(&I);
      }
      for (auto& BB : f) {
        fnResultsRef.FindAndConstruct(&BB);
        if (auto *T = BB.getTerminator()) {
          fnResultsRef.FindAndConstruct(T);
        }
      }
      // Also store an entry for the function itself (for the summary)
      fnResultsRef.FindAndConstruct(&f);
    }

    // Add all blocks to the worklist in topological order for efficiency
    // Reverse postorder traversal to initialize our block worklist
    llvm::ReversePostOrderTraversal<llvm::Function*> rpot(&f);
    BasicBlockWorklist work(rpot.begin(), rpot.end());

    // Keep track of how many times of revisiting each block
    std::map<llvm::BasicBlock*, long> blackmap;
    for (llvm::BasicBlock* BBB : rpot) {
      blackmap[BBB] = 0;
    }

    // Main fixpoint iteration over basic blocks
    while (!work.empty()) {
      auto* bb = work.take();
      //llvm::errs() << "  [Block] " << bb->getName() << " in " << f.getName() << "\n";

      // old states
      // Save a copy of the outgoing abstract state to check for changes
      const auto& oldEntryState = fnResultsRef[bb];
      const auto  oldExitState  = fnResultsRef[bb->getTerminator()];

      // Merge from preds
      // Merge the state coming in from all predecessors
      auto state = mergeStateFromPredecessors(bb, fnResultsRef);
      //mergeInState(state, results[&f]);

      // If no change at entry => skip
      // If we have already processed the block and no changes have been made to
      // the abstract input, we can skip processing the block. Otherwise, save
      // the new entry state and proceed processing this block.
      if (state == oldEntryState && !state.empty()) {
        //llvm::errs() << "    [Block] No change at entry, skipping.\n";
        continue;
      }
      fnResultsRef[bb] = state; // update the block's "entry"

      // Propagate through instructions in the block
      for (auto& I : *bb) {
        llvm::CallSite cs(&I);
        if (isAnalyzableCall(cs)) {
          //llvm::errs() << "    [Block] Analyzing call: " << I << "\n";
          analyzeCall(cs, state, context);
        } else {
          transfer(I, state);
        }
        fnResultsRef[&I] = state; // store post-instruction state
      }

      // If no change at exit => skip
      // If the abstract state for this block did not change, then we are done
      // with this block. Otherwise, we must update the abstract state and
      // consider changes to successors.
      if (state == oldExitState) {
        //llvm::errs() << "    [Block] No change at exit, done with block.\n";
        continue;
      }

      // Re-queue successors
      for (auto* s : llvm::successors(bb)) {
        blackmap[s]++;
        //llvm::errs() << "    [Block] Scheduling successor: " << s->getName()<< " (#" << blackmap[s] << " visits)\n";
        // Simple iteration limit
        if (blackmap[s] <= 10) {
          work.add(s);
        } else {
          //llvm::errs() << "      [Block] Reached iteration limit for "<< s->getName() << ", skipping.\n";
        }
      }

      // If it's a return, merge into function summary
      if (auto* ret = llvm::dyn_cast<llvm::ReturnInst>(bb->getTerminator())) {
        //llvm::errs() << "    [Block] Return in " << f.getName()<< " => merging summary.\n";
        fnResultsRef[&f][&f] =
          meet({fnResultsRef[&f][&f], state[ret->getReturnValue()]});
      }
    }

    // Check if final results changed overall
    // The overall results for the given function and context are updated if
    // necessary. Updating the results for this (function,context) means that
    // all callers must be updated as well.
    auto &oldResults = allResults[context][&f];
    if (!(oldResults == fnResultsRef)) {
      //llvm::errs() << "[computeForwardDataflow(Function)] Updated results for "<< f.getName() << ", notifying callers.\n";
      oldResults = fnResultsRef;
      for (auto &caller : callers[{context, &f}]) {
        //llvm::errs() << "    [CallerNotify] Re-enqueue: "<< caller.second->getName() << "\n";
        contextWork.add(caller);
      }
    }

    active.erase({context, &f});
    //llvm::errs() << "[computeForwardDataflow(Function)] Done: " << f.getName() << "\n";
    return fnResultsRef;
  }


  // Currently we do not handle indirect calls but apply transfer directly.
  // To keep soundness, we classify variables in this case as unsafe later in value range analysis
  llvm::Function*
  getCalledFunction(llvm::CallSite cs) {
    auto* calledValue = cs.getCalledValue()->stripPointerCasts();
    return llvm::dyn_cast<llvm::Function>(calledValue);
  }

  bool
  isAnalyzableCall(llvm::CallSite cs) {
    if (!cs.getInstruction()) {
      return false;
    }
    auto* called = getCalledFunction(cs);
    return called && !called->isDeclaration();
  }

  void
  analyzeCall(llvm::CallSite cs, State &state, const Context& context) {
    // Build new context if we have any context slots
    Context newContext;
    if (newContext.size() > 0) {
      std::copy(context.begin() + 1, context.end(), newContext.begin());
      newContext.back() = cs.getInstruction();
    }

    auto* caller  = cs.getInstruction()->getFunction();
    auto* callee  = getCalledFunction(cs);

    //llvm::errs() << "    [analyzeCall] Caller=" << caller->getName()<< ", Callee=" << callee->getName() << "\n";

    auto toCall   = std::make_pair(newContext, callee);
    auto toUpdate = std::make_pair(context, caller);

    auto& calledState  = allResults[newContext][callee];
    auto& summaryState = calledState[callee];
    bool needsUpdate   = summaryState.size() == 0;

    unsigned index = 0;
    for (auto &functionArg : callee->args()) {
      auto *passedConcrete = cs.getArgument(index);
      auto passedAbstract = state.find(passedConcrete);
      if (passedAbstract == state.end()) {
        // Possibly propagate to define that operand
        transfer(*passedConcrete, state);
        passedAbstract = state.find(passedConcrete);
      }
      auto &arg = summaryState[&functionArg];
      auto  newState = meet({passedAbstract->second, arg});
      needsUpdate |= !(newState == arg);
      arg = newState;
      ++index;
    }

    if (!active.count(toCall) && needsUpdate) {
      //llvm::errs() << "    [analyzeCall] Need to update callee: "<< callee->getName() << "\n";
      computeForwardDataflow(*callee, newContext);
    }

    // Copy callee summary back to the call instruction
    state[cs.getInstruction()] = calledState[callee][callee];
    callers[toCall].insert(toUpdate);
  }

private:
  // These property objects determine the behavior of the dataflow analysis.
  // They should by replaced by concrete implementation classes on a per
  // analysis basis.
  Meet meet;
  Transfer transfer;

  AllResults allResults;
  ContextWorklist contextWork;
  llvm::DenseMap<ContextFunction, llvm::DenseSet<ContextFunction>> callers;
  llvm::DenseSet<ContextFunction> active;

  void
  mergeInState(State& destination, const State& toMerge) {
    for (auto &valueStatePair : toMerge) {
      // If an incoming Value has an AbstractValue in the already merged
      // state, meet it with the new one. Otherwise, copy the new value over,
      // implicitly meeting with bottom.
      auto [found, newlyAdded] = destination.insert(valueStatePair);
      if (!newlyAdded) {
        // Key present => meet
        found->second = meet({found->second, valueStatePair.second});
      }
    }
  }

  State
  mergeStateFromPredecessors(llvm::BasicBlock* bb, FunctionResults& results) {
    State mergedState = State{};
    mergeInState(mergedState, results[bb]); // block's own old entry
    for (auto* p : llvm::predecessors(bb)) {
      auto predecessorFacts = results.find(p->getTerminator());
      if (predecessorFacts == results.end()) {
        continue;
      }
      mergeInState(mergedState, predecessorFacts->second);
    }
    return mergedState;
  }

  // Optional if you want specialized PHI handling in your own code
  AbstractValue
  meetOverPHI(State& state, const llvm::PHINode& phi) {
    auto phiValue = AbstractValue();
    for (auto &value : phi.incoming_values()) {
      auto found = state.find(value.get());
      if (found == state.end()) {
        transfer(*value.get(), state);
        found = state.find(value.get());
      }
      phiValue = meet({phiValue, found->second});
    }
    return phiValue;
  }

  void
  applyTransfer(llvm::Instruction &i, State &state) {
    if (auto* phi = llvm::dyn_cast<llvm::PHINode>(&i)) {
      state[phi] = meetOverPHI(state, *phi);
      //llvm::errs() << "    [applyTransfer] PHI updated in "<< i.getFunction()->getName() << "\n";
    } else {
      transfer(i, state);
    }
  }
};

} // end namespace

#endif