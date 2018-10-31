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
static Timer DTUDeDuplicate("dtu-dedup", "Deduplication", DTUTimerGroup);

bool DomTreeUpdater::isUpdateValid(
    const DominatorTree::UpdateType Update) const {
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

bool DomTreeUpdater::isSelfDominance(
    const DominatorTree::UpdateType Update) const {
  // Won't affect DomTree and PostDomTree.
  return Update.getFrom() == Update.getTo();
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
  applyDomTreeUpdates();
  applyPostDomTreeUpdates();
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
  PendDTUpdateIndex = PendPDTUpdateIndex = PendUpdates.size();
  dropOutOfDateUpdates();
}

bool DomTreeUpdater::hasPendingUpdates() const {
  return hasPendingDomTreeUpdates() || hasPendingPostDomTreeUpdates();
}

bool DomTreeUpdater::hasPendingDomTreeUpdates() const {
  if (!DT)
    return false;
  return PendUpdates.size() != PendDTUpdateIndex;
}

bool DomTreeUpdater::hasPendingPostDomTreeUpdates() const {
  if (!PDT)
    return false;
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
  if (Strategy == UpdateStrategy::Lazy) {
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
  if (Strategy == UpdateStrategy::Lazy) {
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

  if (Strategy == UpdateStrategy::Lazy || ForceRemoveDuplicates) {
    SmallVector<DominatorTree::UpdateType, 8> Seen;
    for (const auto U : Updates)
      // Deduplicate updates
      if (llvm::none_of(
              Seen,
              [U](const DominatorTree::UpdateType S) { return S == U; }) &&
          isUpdateValid(U) && !isSelfDominance(U)) {
        Seen.push_back(U);
        if (Strategy == UpdateStrategy::Lazy)
          PendUpdates.push_back(U);
      }
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
  applyDomTreeUpdates();
  dropOutOfDateUpdates();
  return *DT;
}

PostDominatorTree &DomTreeUpdater::getPostDomTree() {
  assert(PDT && "Invalid acquisition of a null PostDomTree");
  applyPostDomTreeUpdates();
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

  PendUpdates.push_back({DominatorTree::Insert, From, To});
}

void DomTreeUpdater::insertEdgeRelaxed(BasicBlock *From, BasicBlock *To) {
  if (From == To)
    return;

  if (!DT && !PDT)
    return;

  if (!isUpdateValid({DominatorTree::Insert, From, To}))
    return;

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

  PendUpdates.push_back({DominatorTree::Insert, From, To});
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

  PendUpdates.push_back({DominatorTree::Delete, From, To});
}

void DomTreeUpdater::deleteEdgeRelaxed(BasicBlock *From, BasicBlock *To) {
  if (From == To)
    return;

  if (!DT && !PDT)
    return;

  if (!isUpdateValid({DominatorTree::Delete, From, To}))
    return;

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

  PendUpdates.push_back({DominatorTree::Delete, From, To});
}

void DomTreeUpdater::dropOutOfDateUpdates() {
  if (Strategy == DomTreeUpdater::UpdateStrategy::Eager)
    return;

  tryFlushDeletedBB();

  // Drop all updates applied by both trees.
  if (!DT)
    PendDTUpdateIndex = PendUpdates.size();
  if (!PDT)
    PendPDTUpdateIndex = PendUpdates.size();

  const size_t dropIndex = std::min(PendDTUpdateIndex, PendPDTUpdateIndex);
  const auto B = PendUpdates.begin();
  const auto E = PendUpdates.begin() + dropIndex;
  assert(B <= E && "Iterator out of range.");
  PendUpdates.erase(B, E);
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
} // namespace llvm
