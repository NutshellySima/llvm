//===- DomTreeUpdater.cpp - DomTree/Post DomTree Updater --------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements the DomTreeUpdater class, which provides a uniform way
// to update dominator tree related data structures.
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/DomTreeUpdater.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Support/GenericDomTree.h"
#include "llvm/Support/Timer.h"
#include <algorithm>
#include <functional>
namespace llvm {

#define DEBUG_TYPE "DTU-stats"

STATISTIC(NumNoopPruned, "Number of no-ops removed");
STATISTIC(NumDuplicatePruned, "Number of duplicates removed");
STATISTIC(NumInvalidPruned, "Number of invalid updates discarded");
STATISTIC(NumRecalculate, "Number of recalculations requested");
STATISTIC(NumLazyUpdate, "Number of lazy updates applied");

#undef DEBUG_TYPE

static TimerGroup DTTimerGroup("DomTree Timer", "DomTree Calculation");
static Timer DTApplyUpdatesTimer("domtree-au", "apply-updates -- DomTree",
                                 DTTimerGroup);
static Timer DTInsertEdgeTimer("domtree-ie", "insert-edge -- DomTree",
                               DTTimerGroup);
static Timer DTDeleteEdgeTimer("domtree-de", "delete-edge -- DomTree",
                               DTTimerGroup);
static Timer DTRecalculateTimer("domtree-re", "recalculate -- DomTree",
                                DTTimerGroup);
static Timer PDTApplyUpdatesTimer("pdomtree-au", "apply-updates -- PostDomTree",
                                  DTTimerGroup);
static Timer PDTInsertEdgeTimer("pdomtree-ie", "insert-edge -- PostDomTree",
                                DTTimerGroup);
static Timer PDTDeleteEdgeTimer("pdomtree-de", "delete-edge -- PostDomTree",
                                DTTimerGroup);
static Timer PDTRecalculateTimer("pdomtree-re", "recalculate -- PostDomTree",
                                 DTTimerGroup);
static Timers DTTimers(DTApplyUpdatesTimer, DTInsertEdgeTimer,
                       DTDeleteEdgeTimer, DTRecalculateTimer,
                       PDTApplyUpdatesTimer, PDTInsertEdgeTimer,
                       PDTDeleteEdgeTimer, PDTRecalculateTimer);
static TimerGroup DTUTimerGroup("DTU Timer", "DTU timing");
static Timer DTUApplyUpdatesTimer("domtree-au", "apply-updates -- DomTree",
                                  DTUTimerGroup);
static Timer DTUInsertEdgeTimer("domtree-ie", "insert-edge -- DomTree",
                                DTUTimerGroup);
static Timer DTUDeleteEdgeTimer("domtree-de", "delete-edge -- DomTree",
                                DTUTimerGroup);
static Timer DTURecalculateTimer("domtree-re", "recalculate -- DomTree",
                                 DTUTimerGroup);
static Timer PDTUApplyUpdatesTimer("pdomtree-au",
                                   "apply-updates -- PostDomTree",
                                   DTUTimerGroup);
static Timer PDTUInsertEdgeTimer("pdomtree-ie", "insert-edge -- PostDomTree",
                                 DTUTimerGroup);
static Timer PDTUDeleteEdgeTimer("pdomtree-de", "delete-edge -- PostDomTree",
                                 DTUTimerGroup);
static Timer PDTURecalculateTimer("pdomtree-re", "recalculate -- PostDomTree",
                                  DTUTimerGroup);
static Timer SnapshotTimer("Snapshot", "Snapshot", DTUTimerGroup);
static Timer SnapshotSortTimer("SnapshotSort", "SnapshotSort", DTUTimerGroup);
static Timer PendPushTimer("PendPush", "PendPush", DTUTimerGroup);
static Timer HintPushTimer("HintPush", "HintPush", DTUTimerGroup);
static Timer DiffTimer("Diff", "Diff", DTUTimerGroup);
static Timer DeduplicateTimer("Deduplicate", "Deduplicate", DTUTimerGroup);

bool DomTreeUpdater::isUpdateValid(
    const DominatorTree::UpdateType Update) const {
#ifdef NDEBUG
  assert(!isAuto());
#endif
  ++NumInvalidPruned;
  const auto *From = Update.getFrom();
  const auto *To = Update.getTo();
  const auto Kind = Update.getKind();

  // Discard updates by inspecting the current state of successors of From.
  // Since isUpdateValid() must be called *after* the Terminator of From is
  // altered we can determine if the update is unnecessary for batch updates
  // or invalid for a single update.
  const bool HasEdge = llvm::any_of(
      successors(From), [To](const BasicBlock *B) { return B == To; });

  // If the IR does not match the update,
  // 1. In batch updates, this update is unnecessary.
  // 2. When called by insertEdge*()/deleteEdge*(), this update is invalid.
  // Edge does not exist in IR.
  if (Kind == DominatorTree::Insert && !HasEdge)
    return false;

  // Edge exists in IR.
  if (Kind == DominatorTree::Delete && HasEdge)
    return false;
  --NumInvalidPruned;
  return true;
}

DenseSet<BasicBlock *> DomTreeUpdater::getNewCFG(llvm::BasicBlock *BB) {
  DenseSet<BasicBlock *> Ret;
  for (auto *Addr : successors(BB))
    Ret.insert(Addr);
  return Ret;
}

void DomTreeUpdater::isAboutToChange(BasicBlock *BB) {
  if (!isAuto())
    return;
  if (!DT && !PDT)
    return;
  // Have snapshoted.
  PendPushTimer.startTimer();
  if (SnapshotedCFG.find(BB) != SnapshotedCFG.end()) {
    PendPushTimer.stopTimer();
    return;
  }
  // It is a new BB.
  if (CFGPoints.find(BB) == CFGPoints.end()) {
    PendPushTimer.stopTimer();
    return;
  }
  PendPushTimer.stopTimer();
  SnapshotTimer.startTimer();
  SnapshotedCFG[BB] = getNewCFG(BB);
  SnapshotTimer.stopTimer();
}

std::vector<DominatorTree::UpdateType> DomTreeUpdater::diffCFG() {
  DiffTimer.startTimer();

  std::vector<DominatorTree::UpdateType> Updates;

  for (const auto &Edge : PendEdges) {
    if (SnapshotedCFG.find(Edge.first) == SnapshotedCFG.end())
      if (CFGPoints.find(Edge.first) != CFGPoints.end())
        continue;
    CFGPoints.insert(Edge.first);
    auto &PrevCFG = SnapshotedCFG[Edge.first];
    auto NewCFG = getNewCFG(Edge.first);
    for (auto &Update : Edge.second) {
      bool ExistinNew = NewCFG.find(Update) != NewCFG.end();
      bool ExistinOld = PrevCFG.find(Update) != PrevCFG.end();
      if (ExistinNew == ExistinOld)
        continue;
      if (ExistinNew)
        Updates.push_back({DominatorTree::Insert, Edge.first, Update});
      else
        Updates.push_back({DominatorTree::Delete, Edge.first, Update});
    }
    SnapshotedCFG[Edge.first] = std::move(NewCFG);
  }

  PendEdges.clear();
  DiffTimer.stopTimer();
  NeedCalculate = false;

  return Updates;
}

void DomTreeUpdater::snapshotCFG(CFG &Graph) {
  if (!DT && !PDT)
    return;

  PendPushTimer.startTimer();
  Graph.clear();
  PendPushTimer.stopTimer();

  SnapshotTimer.startTimer();
  if (!Func) {
    if (DT)
      Func = DT->getRoot()->getParent();
    else if (PDT)
      Func = PDT->getRoot()->getParent();
  }

  SnapshotedBB = &Func->getEntryBlock();

  CFGPoints.clear();
  for (auto &BB : Func->getBasicBlockList())
    CFGPoints.insert(&BB);
  SnapshotTimer.stopTimer();
}

bool DomTreeUpdater::isSelfDominance(
    const DominatorTree::UpdateType Update) const {
  // Won't affect DomTree and PostDomTree.
  return Update.getFrom() == Update.getTo();
}

bool DomTreeUpdater::applyLazyUpdate(DominatorTree::UpdateKind Kind,
                                     BasicBlock *From, BasicBlock *To) {
  assert((DT || PDT) &&
         "Call applyLazyUpdate() when both DT and PDT are nullptrs.");
  assert(Strategy == DomTreeUpdater::UpdateStrategy::Lazy &&
         "Call applyLazyUpdate() with Eager strategy error");
  // Analyze pending updates to determine if the update is unnecessary.
  const DominatorTree::UpdateType Update = {Kind, From, To};
  const DominatorTree::UpdateType Invert = {Kind != DominatorTree::Insert
                                                ? DominatorTree::Insert
                                                : DominatorTree::Delete,
                                            From, To};
  // Only check duplicates in updates that are not applied by both trees.
  auto I =
      PendUpdates.begin() + std::max(PendDTUpdateIndex, PendPDTUpdateIndex);
  const auto E = PendUpdates.end();

  assert(I <= E && "Iterator out of range.");

  for (; I != E; ++I) {
    if (Update == *I) {
      ++NumDuplicatePruned;
      return false; // Discard duplicate updates.
    }
    if (Invert == *I) {
      // Update and Invert are both valid (equivalent to a no-op). Remove
      // Invert from PendUpdates and discard the Update.
      ++NumNoopPruned;
      --NumLazyUpdate;
      PendUpdates.erase(I);
      return false;
    }
  }
  ++NumLazyUpdate;
  PendUpdates.push_back(Update); // Save the valid update.
  return true;
}

void DomTreeUpdater::applyDomTreeUpdates() {
  // No pending DomTreeUpdates.
  if (Strategy != UpdateStrategy::Lazy || !DT)
    return;

  // Only apply updates not are applied by DomTree.
  if (hasPendingDomTreeUpdates()) {
    const auto I = PendUpdates.begin() + PendDTUpdateIndex;
    const auto E = PendUpdates.end();
    assert(I < E && "Iterator range invalid; there should be DomTree updates.");
    DTUApplyUpdatesTimer.startTimer();
    DT->applyUpdates(ArrayRef<DominatorTree::UpdateType>(I, E));
    DTUApplyUpdatesTimer.stopTimer();
    PendDTUpdateIndex = PendUpdates.size();
  }
}

void DomTreeUpdater::flush() {
  if (!isAuto()) {
    applyDomTreeUpdates();
    applyPostDomTreeUpdates();
  } else
    applyAutoUpdates();
  dropOutOfDateUpdates();
}

void DomTreeUpdater::applyPostDomTreeUpdates() {
  // No pending PostDomTreeUpdates.
  if (Strategy != UpdateStrategy::Lazy || !PDT)
    return;

  // Only apply updates not are applied by PostDomTree.
  if (hasPendingPostDomTreeUpdates()) {
    const auto I = PendUpdates.begin() + PendPDTUpdateIndex;
    const auto E = PendUpdates.end();
    assert(I < E &&
           "Iterator range invalid; there should be PostDomTree updates.");
    PDTUApplyUpdatesTimer.startTimer();
    PDT->applyUpdates(ArrayRef<DominatorTree::UpdateType>(I, E));
    PDTUApplyUpdatesTimer.stopTimer();
    PendPDTUpdateIndex = PendUpdates.size();
  }
}

void DomTreeUpdater::tryFlushDeletedBB() {
  if (!hasPendingUpdates())
    forceFlushDeletedBB();
}

bool DomTreeUpdater::forceFlushDeletedBB() {
  if (DeletedBBs.empty())
    return false;

  for (auto *BB : DeletedBBs) {
    // After calling deleteBB or callbackDeleteBB under Lazy UpdateStrategy,
    // validateDeleteBB() removes all instructions of DelBB and adds an
    // UnreachableInst as its terminator. So we check whether the BasicBlock to
    // delete only has an UnreachableInst inside.
    assert(BB->getInstList().size() == 1 &&
           isa<UnreachableInst>(BB->getTerminator()) &&
           "DelBB has been modified while awaiting deletion.");
    BB->removeFromParent();
    eraseDelBBNode(BB);
    delete BB;
  }
  DeletedBBs.clear();
  Callbacks.clear();
  return true;
}

void DomTreeUpdater::recalculate(Function &F) {

  if (Strategy == UpdateStrategy::Eager) {
    if (DT)
      ++NumRecalculate;
    if (PDT)
      ++NumRecalculate;
    DTURecalculateTimer.startTimer();
    if (DT)
      DT->recalculate(F);
    DTURecalculateTimer.stopTimer();
    PDTURecalculateTimer.startTimer();
    if (PDT)
      PDT->recalculate(F);
    PDTURecalculateTimer.stopTimer();
    return;
  }

  // There is little performance gain if we pend the recalculation under
  // Lazy UpdateStrategy so we recalculate available trees immediately.

  // Prevent forceFlushDeletedBB() from erasing DomTree or PostDomTree nodes.
  IsRecalculatingDomTree = IsRecalculatingPostDomTree = true;

  // Because all trees are going to be up-to-date after recalculation,
  // flush awaiting deleted BasicBlocks.
  forceFlushDeletedBB();
  if (isAuto()) {
    if (SnapshotedBB == &Func->getEntryBlock()) {
      NeedCalculate = true;
      IsRecalculatingDomTree = IsRecalculatingPostDomTree = false;
      applyAutoUpdates();
      return;
    }
  }

  if (DT)
    ++NumRecalculate;
  if (PDT)
    ++NumRecalculate;
  DTURecalculateTimer.startTimer();
  if (DT)
    DT->recalculate(F);
  DTURecalculateTimer.stopTimer();
  PDTURecalculateTimer.startTimer();
  if (PDT)
    PDT->recalculate(F);
  PDTURecalculateTimer.stopTimer();

  // Resume forceFlushDeletedBB() to erase DomTree or PostDomTree nodes.
  IsRecalculatingDomTree = IsRecalculatingPostDomTree = false;
  if (!isAuto())
    PendDTUpdateIndex = PendPDTUpdateIndex = PendUpdates.size();
  dropOutOfDateUpdates();

  if (isAuto()) {
    snapshotCFG(SnapshotedCFG);
    PendEdges.clear();
    NeedCalculate = false;
  }
}

bool DomTreeUpdater::hasPendingUpdates() const {
  return hasPendingDomTreeUpdates() || hasPendingPostDomTreeUpdates();
}

bool DomTreeUpdater::hasPendingDomTreeUpdates() const {
  if (!DT)
    return false;

  if (isAuto()) {
    if (NeedCalculate)
      return true;

    return false;
  }

  return PendUpdates.size() != PendDTUpdateIndex;
}

bool DomTreeUpdater::hasPendingPostDomTreeUpdates() const {
  if (!PDT)
    return false;

  if (isAuto()) {
    if (NeedCalculate)
      return true;

    return false;
  }

  return PendUpdates.size() != PendPDTUpdateIndex;
}

bool DomTreeUpdater::isBBPendingDeletion(llvm::BasicBlock *DelBB) const {
  if (Strategy == UpdateStrategy::Eager || DeletedBBs.empty())
    return false;
  return DeletedBBs.count(DelBB) != 0;
}

// The DT and PDT require the nodes related to updates
// are not deleted when update functions are called.
// So BasicBlock deletions must be pended when the
// UpdateStrategy is Lazy. When the UpdateStrategy is
// Eager, the BasicBlock will be deleted immediately.
void DomTreeUpdater::deleteBB(BasicBlock *DelBB) {
  validateDeleteBB(DelBB);
  if (isLazy()) {
    DeletedBBs.insert(DelBB);
    return;
  }

  DelBB->removeFromParent();
  eraseDelBBNode(DelBB);
  delete DelBB;
}

void DomTreeUpdater::callbackDeleteBB(
    BasicBlock *DelBB, std::function<void(BasicBlock *)> Callback) {
  validateDeleteBB(DelBB);
  if (isLazy()) {
    Callbacks.push_back(CallBackOnDeletion(DelBB, Callback));
    DeletedBBs.insert(DelBB);
    return;
  }

  DelBB->removeFromParent();
  eraseDelBBNode(DelBB);
  Callback(DelBB);
  delete DelBB;
}

void DomTreeUpdater::eraseDelBBNode(BasicBlock *DelBB) {
  if (DT && !IsRecalculatingDomTree)
    if (DT->getNode(DelBB))
      DT->eraseNode(DelBB);

  if (PDT && !IsRecalculatingPostDomTree)
    if (PDT->getNode(DelBB))
      PDT->eraseNode(DelBB);

  PendPushTimer.startTimer();
  // Delete this FromBB in case of memory leak.
  if (isAuto())
    SnapshotedCFG.erase(DelBB);
  PendPushTimer.stopTimer();

  CFGPoints.erase(DelBB);
}

void DomTreeUpdater::validateDeleteBB(BasicBlock *DelBB) {
  assert(DelBB && "Invalid push_back of nullptr DelBB.");
  assert(pred_empty(DelBB) && "DelBB has one or more predecessors.");
  // DelBB is unreachable and all its instructions are dead.
  while (!DelBB->empty()) {
    Instruction &I = DelBB->back();
    // Replace used instructions with an arbitrary value (undef).
    if (!I.use_empty())
      I.replaceAllUsesWith(llvm::UndefValue::get(I.getType()));
    DelBB->getInstList().pop_back();
  }
  // Make sure DelBB has a valid terminator instruction. As long as DelBB is a
  // Child of Function F it must contain valid IR.
  new UnreachableInst(DelBB->getContext(), DelBB);
}

void DomTreeUpdater::applyUpdates(ArrayRef<DominatorTree::UpdateType> Updates,
                                  bool ForceRemoveDuplicates) {
  if (!DT && !PDT)
    return;

  if (isAuto()) {

    if (Updates.empty())
      return;

    HintPushTimer.startTimer();
    bool Changed = false;
    for (auto &Update : Updates) {
      if (Update.getFrom() != Update.getTo()) {
        PendEdges[Update.getFrom()].insert(Update.getTo());
        Changed = true;
      }
    }
    NeedCalculate |= Changed;
    HintPushTimer.stopTimer();
    return;
  }

  if (Strategy == UpdateStrategy::Lazy || ForceRemoveDuplicates) {
    if (isLazy())
      DeduplicateTimer.startTimer();
    SmallVector<DominatorTree::UpdateType, 8> Seen;
    for (const auto U : Updates)
      // For Lazy UpdateStrategy, avoid duplicates to applyLazyUpdate() to save
      // on analysis.
      if (llvm::none_of(
              Seen,
              [U](const DominatorTree::UpdateType S) { return S == U; }) &&
          isUpdateValid(U) && !isSelfDominance(U)) {
        Seen.push_back(U);
        if (Strategy == UpdateStrategy::Lazy)
          applyLazyUpdate(U.getKind(), U.getFrom(), U.getTo());
      }
    if (isLazy())
      DeduplicateTimer.stopTimer();
    if (Strategy == UpdateStrategy::Lazy)
      return;

    DTUApplyUpdatesTimer.startTimer();
    if (DT)
      DT->applyUpdates(Seen);
    DTUApplyUpdatesTimer.stopTimer();
    PDTUApplyUpdatesTimer.startTimer();
    if (PDT)
      PDT->applyUpdates(Seen);
    PDTUApplyUpdatesTimer.stopTimer();
    return;
  }

  DTUApplyUpdatesTimer.startTimer();
  if (DT)
    DT->applyUpdates(Updates);
  DTUApplyUpdatesTimer.stopTimer();
  PDTUApplyUpdatesTimer.startTimer();
  if (PDT)
    PDT->applyUpdates(Updates);
  PDTUApplyUpdatesTimer.stopTimer();
}

DominatorTree &DomTreeUpdater::getDomTree() {
  assert(DT && "Invalid acquisition of a null DomTree");
  if (!isAuto())
    applyDomTreeUpdates();
  else
    applyAutoUpdates();
  dropOutOfDateUpdates();
  return *DT;
}

PostDominatorTree &DomTreeUpdater::getPostDomTree() {
  assert(PDT && "Invalid acquisition of a null PostDomTree");
  if (!isAuto())
    applyPostDomTreeUpdates();
  else
    applyAutoUpdates();
  dropOutOfDateUpdates();
  return *PDT;
}

void DomTreeUpdater::insertEdge(BasicBlock *From, BasicBlock *To) {

#ifndef NDEBUG
  assert(isUpdateValid({DominatorTree::Insert, From, To}) &&
         "Inserted edge does not appear in the CFG");
#endif

  if (!DT && !PDT)
    return;

  // Won't affect DomTree and PostDomTree; discard update.
  if (From == To)
    return;

  if (isAuto()) {
    NeedCalculate = true;
    HintPushTimer.startTimer();
    PendEdges[From].insert(To);
    HintPushTimer.stopTimer();
    return;
  }

  if (Strategy == UpdateStrategy::Eager) {
    DTUInsertEdgeTimer.startTimer();
    if (DT)
      DT->insertEdge(From, To);
    DTUInsertEdgeTimer.stopTimer();
    PDTUInsertEdgeTimer.startTimer();
    if (PDT)
      PDT->insertEdge(From, To);
    PDTUInsertEdgeTimer.stopTimer();
    return;
  }

  DeduplicateTimer.startTimer();
  applyLazyUpdate(DominatorTree::Insert, From, To);
  DeduplicateTimer.stopTimer();
}

void DomTreeUpdater::insertEdgeRelaxed(BasicBlock *From, BasicBlock *To) {
  if (From == To)
    return;

  if (!DT && !PDT)
    return;

  if (isAuto()) {
    NeedCalculate = true;
    HintPushTimer.startTimer();
    PendEdges[From].insert(To);
    HintPushTimer.stopTimer();
    return;
  }

  DeduplicateTimer.startTimer();
  if (!isUpdateValid({DominatorTree::Insert, From, To})) {
    DeduplicateTimer.stopTimer();
    return;
  }
  DeduplicateTimer.stopTimer();

  if (Strategy == UpdateStrategy::Eager) {
    DTUInsertEdgeTimer.startTimer();
    if (DT)
      DT->insertEdge(From, To);
    DTUInsertEdgeTimer.stopTimer();
    PDTUInsertEdgeTimer.startTimer();
    if (PDT)
      PDT->insertEdge(From, To);
    PDTUInsertEdgeTimer.stopTimer();
    return;
  }

  DeduplicateTimer.startTimer();
  applyLazyUpdate(DominatorTree::Insert, From, To);
  DeduplicateTimer.stopTimer();
}

void DomTreeUpdater::deleteEdge(BasicBlock *From, BasicBlock *To) {

#ifndef NDEBUG
  assert(isUpdateValid({DominatorTree::Delete, From, To}) &&
         "Deleted edge still exists in the CFG!");
#endif

  if (!DT && !PDT)
    return;

  // Won't affect DomTree and PostDomTree; discard update.
  if (From == To)
    return;

  if (isAuto()) {
    NeedCalculate = true;
    HintPushTimer.startTimer();
    PendEdges[From].insert(To);
    HintPushTimer.stopTimer();
    return;
  }

  if (Strategy == UpdateStrategy::Eager) {
    DTUDeleteEdgeTimer.startTimer();
    if (DT)
      DT->deleteEdge(From, To);
    DTUDeleteEdgeTimer.stopTimer();
    PDTUDeleteEdgeTimer.startTimer();
    if (PDT)
      PDT->deleteEdge(From, To);
    PDTUDeleteEdgeTimer.stopTimer();
    return;
  }

  DeduplicateTimer.startTimer();
  applyLazyUpdate(DominatorTree::Delete, From, To);
  DeduplicateTimer.stopTimer();
}

void DomTreeUpdater::deleteEdgeRelaxed(BasicBlock *From, BasicBlock *To) {
  if (From == To)
    return;

  if (!DT && !PDT)
    return;

  if (isAuto()) {
    NeedCalculate = true;
    HintPushTimer.startTimer();
    PendEdges[From].insert(To);
    HintPushTimer.stopTimer();
    return;
  }

  DeduplicateTimer.startTimer();
  if (!isUpdateValid({DominatorTree::Delete, From, To})) {
    DeduplicateTimer.stopTimer();
    return;
  }
  DeduplicateTimer.stopTimer();

  if (Strategy == UpdateStrategy::Eager) {
    DTUDeleteEdgeTimer.startTimer();
    if (DT)
      DT->deleteEdge(From, To);
    DTUDeleteEdgeTimer.stopTimer();
    PDTUDeleteEdgeTimer.startTimer();
    if (PDT)
      PDT->deleteEdge(From, To);
    PDTUDeleteEdgeTimer.stopTimer();
    return;
  }

  DeduplicateTimer.startTimer();
  applyLazyUpdate(DominatorTree::Delete, From, To);
  DeduplicateTimer.stopTimer();
}

void DomTreeUpdater::dropOutOfDateUpdates() {
  if (Strategy == DomTreeUpdater::UpdateStrategy::Eager)
    return;

  tryFlushDeletedBB();

  // Early return in Auto mode.
  if (isAuto())
    return;

  // Drop all updates applied by both trees.
  if (!DT)
    PendDTUpdateIndex = PendUpdates.size();
  if (!PDT)
    PendPDTUpdateIndex = PendUpdates.size();

  const size_t dropIndex = std::min(PendDTUpdateIndex, PendPDTUpdateIndex);
  const auto B = PendUpdates.begin();
  const auto E = PendUpdates.begin() + dropIndex;
  assert(B <= E && "Iterator out of range.");
  DeduplicateTimer.startTimer();
  PendUpdates.erase(B, E);
  DeduplicateTimer.stopTimer();
  // Calculate current index.
  PendDTUpdateIndex -= dropIndex;
  PendPDTUpdateIndex -= dropIndex;
}

#if !defined(NDEBUG) || defined(LLVM_ENABLE_DUMP)
LLVM_DUMP_METHOD void DomTreeUpdater::dump() const {
  raw_ostream &OS = llvm::dbgs();

  OS << "Available Trees: ";
  if (DT || PDT) {
    if (DT)
      OS << "DomTree ";
    if (PDT)
      OS << "PostDomTree ";
    OS << "\n";
  } else
    OS << "None\n";

  OS << "UpdateStrategy: ";
  if (Strategy == UpdateStrategy::Eager) {
    OS << "Eager\n";
    return;
  } else
    OS << "Lazy\n";
  int Index = 0;

  auto printUpdates =
      [&](ArrayRef<DominatorTree::UpdateType>::const_iterator begin,
          ArrayRef<DominatorTree::UpdateType>::const_iterator end) {
        if (begin == end)
          OS << "  None\n";
        Index = 0;
        for (auto It = begin, ItEnd = end; It != ItEnd; ++It) {
          auto U = *It;
          OS << "  " << Index << " : ";
          ++Index;
          if (U.getKind() == DominatorTree::Insert)
            OS << "Insert, ";
          else
            OS << "Delete, ";
          BasicBlock *From = U.getFrom();
          if (From) {
            auto S = From->getName();
            if (!From->hasName())
              S = "(no name)";
            OS << S << "(" << From << "), ";
          } else {
            OS << "(badref), ";
          }
          BasicBlock *To = U.getTo();
          if (To) {
            auto S = To->getName();
            if (!To->hasName())
              S = "(no_name)";
            OS << S << "(" << To << ")\n";
          } else {
            OS << "(badref)\n";
          }
        }
      };

  if (DT) {
    const auto I = PendUpdates.begin() + PendDTUpdateIndex;
    assert(PendUpdates.begin() <= I && I <= PendUpdates.end() &&
           "Iterator out of range.");
    OS << "Applied but not cleared DomTreeUpdates:\n";
    printUpdates(PendUpdates.begin(), I);
    OS << "Pending DomTreeUpdates:\n";
    printUpdates(I, PendUpdates.end());
  }

  if (PDT) {
    const auto I = PendUpdates.begin() + PendPDTUpdateIndex;
    assert(PendUpdates.begin() <= I && I <= PendUpdates.end() &&
           "Iterator out of range.");
    OS << "Applied but not cleared PostDomTreeUpdates:\n";
    printUpdates(PendUpdates.begin(), I);
    OS << "Pending PostDomTreeUpdates:\n";
    printUpdates(I, PendUpdates.end());
  }

  OS << "Pending DeletedBBs:\n";
  Index = 0;
  for (auto BB : DeletedBBs) {
    OS << "  " << Index << " : ";
    ++Index;
    if (BB->hasName())
      OS << BB->getName() << "(";
    else
      OS << "(no_name)(";
    OS << BB << ")\n";
  }

  OS << "Pending Callbacks:\n";
  Index = 0;
  for (auto BB : Callbacks) {
    OS << "  " << Index << " : ";
    ++Index;
    if (BB->hasName())
      OS << BB->getName() << "(";
    else
      OS << "(no_name)(";
    OS << BB << ")\n";
  }
}
#endif

void DomTreeUpdater::applyAutoUpdates() {
  if (!DT && !PDT)
    return;

  if (!NeedCalculate)
    return;

  if (SnapshotedBB != &Func->getEntryBlock()) {
    // recalculate() will snapshot and reset NeedCalculate.
    recalculate(*Func);
    return;
  }

  // diffCFG will reset NeedCalculate.
  auto Updates = diffCFG();
  DTUApplyUpdatesTimer.startTimer();
  if (DT)
    DT->applyUpdates(Updates);
  DTUApplyUpdatesTimer.stopTimer();
  PDTUApplyUpdatesTimer.startTimer();
  if (PDT)
    PDT->applyUpdates(Updates);
  PDTUApplyUpdatesTimer.stopTimer();
}
} // namespace llvm
