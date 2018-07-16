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

STATISTIC(NumUpdatePruned, "number of no-ops removed");
STATISTIC(NumduplictePruned, "number of duplicate removed");
STATISTIC(NumInvalidPruned, "number of invalid update discarded");
STATISTIC(NumRecalculate, "number of recalculations requested");
STATISTIC(NumLazyUpdate, "number of lazy updates applied");

#undef DEBUG_TYPE

static TimerGroup DTTimerGroup("dom-tree-timer", "dom-tree calculation");
static Timer DTApplyUpdatesTimer("domtree-au", "apply-updates", DTTimerGroup);
static Timer DTInsertEdgeTimer("domtree-ie", "insert-edge", DTTimerGroup);
static Timer DTDeleteEdgeTimer("domtree-de", "delete-edge", DTTimerGroup);
static Timer DTRecalculateTimer("domtree-re", "recalculate", DTTimerGroup);
static Timer PDTApplyUpdatesTimer("pdomtree-au", "papply-updates",
                                  DTTimerGroup);
static Timer PDTInsertEdgeTimer("pdomtree-ie", "pinsert-edge", DTTimerGroup);
static Timer PDTDeleteEdgeTimer("pdomtree-de", "pdelete-edge", DTTimerGroup);
static Timer PDTRecalculateTimer("pdomtree-re", "precalculate", DTTimerGroup);
static Timers T(DTApplyUpdatesTimer, DTInsertEdgeTimer, DTDeleteEdgeTimer,
                DTRecalculateTimer, PDTApplyUpdatesTimer, PDTInsertEdgeTimer,
                PDTDeleteEdgeTimer, PDTRecalculateTimer);
static TimerGroup DTUTimerGroup("DTU-timer", "DTU timing");
static Timer DTUApplyUpdatesTimer("domtree-au", "apply-updates", DTUTimerGroup);
static Timer DTUInsertEdgeTimer("domtree-ie", "insert-edge", DTUTimerGroup);
static Timer DTUDeleteEdgeTimer("domtree-de", "delete-edge", DTUTimerGroup);
static Timer DTURecalculateTimer("domtree-re", "recalculate", DTUTimerGroup);
static Timer PDTUApplyUpdatesTimer("pdomtree-au", "papply-updates",
                                   DTUTimerGroup);
static Timer PDTUInsertEdgeTimer("pdomtree-ie", "pinsert-edge", DTUTimerGroup);
static Timer PDTUDeleteEdgeTimer("pdomtree-de", "pdelete-edge", DTUTimerGroup);
static Timer PDTURecalculateTimer("pdomtree-re", "precalculate", DTUTimerGroup);
static Timer SnapshotTimer("Snapshot", "Snapshot", DTUTimerGroup);
static Timer DiffTimer("Diff", "Diff", DTUTimerGroup);
static Timer DeduplicateTimer("Deduplicate", "Deduplicate", DTUTimerGroup);

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


std::vector<DominatorTree::UpdateType> DomTreeUpdater::diffCFG(){
  auto getNewCFG=[&](BasicBlock* BB){
    std::vector<BasicBlock*> Ret;
    Ret.reserve(succ_size(BB));
    for(auto* Addr:successors(BB))
        Ret.push_back(Addr);
    llvm::sort(Ret.begin(),Ret.end());
    Ret.erase(std::unique(Ret.begin(),Ret.end()),Ret.end());
    return Ret;
  };
  DiffTimer.startTimer();
  std::vector<DominatorTree::UpdateType> Updates;
  std::vector<BasicBlock*>DiffCFG;
  llvm::sort(PendPoints.begin(),PendPoints.end());
  PendPoints.erase(std::unique(PendPoints.begin(),PendPoints.end()),PendPoints.end());

  for(auto&Point:PendPoints) {
    auto& PrevCFG=SnapshotedCFG[Point];
    auto NewCFG=getNewCFG(Point);
    std::set_difference(PrevCFG.begin(), PrevCFG.end(), NewCFG.begin(), NewCFG.end(),
                        std::inserter(DiffCFG, DiffCFG.begin()));
    // Deleted Edges
    for (auto &Edge:DiffCFG)
      if (Point != Edge)
          Updates.push_back({DominatorTree::Delete, Point, Edge});
    DiffCFG.clear();
    std::set_difference(NewCFG.begin(), NewCFG.end(), PrevCFG.begin(), PrevCFG.end(),
                        std::inserter(DiffCFG, DiffCFG.begin()));
    // Inserted Edges
    for (auto &Edge:DiffCFG)
      if (Point != Edge)
          Updates.push_back({DominatorTree::Insert, Point, Edge});
    SnapshotedCFG[Point]=NewCFG;
    DiffCFG.clear();
  }
  PendPoints.clear();
  DiffTimer.stopTimer();

  return Updates;
}

void DomTreeUpdater::snapshotCFG(CFG& Graph) {
  Graph.clear();
  if(!Func){
    if(DT)
      Func=&*DT->getRoot()->getParent();
    else if(PDT)
      Func=&*PDT->getRoot()->getParent();
  }
  SnapshotedBB=&Func->getEntryBlock();
  SnapshotTimer.startTimer();
  for(BasicBlock& BB:Func->getBasicBlockList()) {
      auto& I=Graph[&BB];
      I.reserve(succ_size(&BB));
      for (auto *Addr:successors(&BB))
          I.push_back(Addr);
  }
  for(auto& Point:Graph) {
    llvm::sort(Point.second.begin(), Point.second.end());
    Point.second.erase(std::unique(Point.second.begin(), Point.second.end()), Point.second.end());
  }
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
      ++NumduplictePruned;
      return false; // Discard duplicate updates.
    }
    if (Invert == *I) {
      // Update and Invert are both valid (equivalent to a no-op). Remove
      // Invert from PendUpdates and discard the Update.
      ++NumUpdatePruned;
      NumLazyUpdate -= 2;
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
  if(!isAuto()) {
    applyDomTreeUpdates();
    applyPostDomTreeUpdates();
  }
  else
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
    BB->removeFromParent();
    eraseDelBBNode(BB);
    delete BB;
  }
  DeletedBBs.clear();
  Callbacks.clear();
  return true;
}

bool DomTreeUpdater::recalculate(Function &F) {
  if (!DT && !PDT)
    return false;

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
    return true;
  }

  // Prevent forceFlushDeletedBB() from erasing DomTree or PostDomTree nodes.
  IsRecalculatingDomTree = IsRecalculatingPostDomTree = true;


  // Because all trees are going to be up-to-date after recalculation,
  // flush awaiting deleted BasicBlocks.
  if (forceFlushDeletedBB() || hasPendingUpdates()) {
    if(isAuto()){
      if(SnapshotedBB==&Func->getEntryBlock()){
        NeedCalculate=true;
        IsRecalculatingDomTree = IsRecalculatingPostDomTree = false;
        applyAutoUpdates();
        return true;
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
    PendDTUpdateIndex = PendPDTUpdateIndex = PendUpdates.size();
    dropOutOfDateUpdates();
    if(isAuto()) {
      snapshotCFG(SnapshotedCFG);
      PendPoints.clear();
      NeedCalculate=false;
    }
    return true;
  }

  // Resume forceFlushDeletedBB() to erase DomTree or PostDomTree nodes.
  IsRecalculatingDomTree = IsRecalculatingPostDomTree = false;
  return false;
}

bool DomTreeUpdater::hasPendingUpdates() const {
  return hasPendingDomTreeUpdates() || hasPendingPostDomTreeUpdates();
}

bool DomTreeUpdater::hasPendingDomTreeUpdates() const {
  if (!DT)
    return false;
  if(isAuto()&&NeedCalculate)
    return true;
  return PendUpdates.size() != PendDTUpdateIndex;
}

bool DomTreeUpdater::hasPendingPostDomTreeUpdates() const {
  if (!PDT)
    return false;
  if(isAuto()&&NeedCalculate)
    return true;
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

  if(isAuto())
      SnapshotedCFG.erase(DelBB);
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
  assert(succ_empty(DelBB));
}

void DomTreeUpdater::applyUpdates(ArrayRef<DominatorTree::UpdateType> Updates,
                                  bool ForceRemoveDuplicates) {
  if (!DT && !PDT)
    return;

  if(isAuto()) {
    NeedCalculate=true;
    for(auto& Update:Updates)
        PendPoints.push_back(Update.getFrom());
    return;
  }

  if (Strategy == UpdateStrategy::Lazy || ForceRemoveDuplicates) {
    if(isLazy())
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
    if(isLazy())
      DeduplicateTimer.stopTimer();  
    if (Strategy == UpdateStrategy::Lazy)
      return;

    DTUApplyUpdatesTimer.startTimer();
    if (DT) {
      DT->applyUpdates(Seen);
    }
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
  if(!isAuto())
    applyDomTreeUpdates();
  else
    applyAutoUpdates();
  dropOutOfDateUpdates();
  return *DT;
}

PostDominatorTree &DomTreeUpdater::getPostDomTree() {
  assert(PDT && "Invalid acquisition of a null PostDomTree");
  if(!isAuto())
    applyPostDomTreeUpdates();
  else
    applyAutoUpdates();
  dropOutOfDateUpdates();
  return *PDT;
}

void DomTreeUpdater::insertEdge(BasicBlock *From, BasicBlock *To) {

  if(isAuto()) {
    NeedCalculate=true;
    PendPoints.push_back(From);
    return;
  }

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


  applyLazyUpdate(DominatorTree::Insert, From, To);
}

void DomTreeUpdater::insertEdgeRelaxed(BasicBlock *From, BasicBlock *To) {
  if (From == To)
    return;

  if (!DT && !PDT)
    return;

  if(isAuto()) {
    NeedCalculate=true;
    PendPoints.push_back(From);
    return;
  }

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
  DeduplicateTimer.startTimer();
  applyLazyUpdate(DominatorTree::Insert, From, To);
  DeduplicateTimer.stopTimer();
}

void DomTreeUpdater::deleteEdge(BasicBlock *From, BasicBlock *To) {

  if(isAuto()) {
    NeedCalculate=true;
    PendPoints.push_back(From);
    return;
  }
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
  applyLazyUpdate(DominatorTree::Delete, From, To);
}

void DomTreeUpdater::deleteEdgeRelaxed(BasicBlock *From, BasicBlock *To) {
  if (From == To)
    return;

  if (!DT && !PDT)
    return;

  if(isAuto()) {
    NeedCalculate=true;
    PendPoints.push_back(From);
    return;
  }

  if (!isUpdateValid({DominatorTree::Delete, From, To}))
    return;

  if (Strategy == UpdateStrategy::Eager) {
    DTUDeleteEdgeTimer.startTimer();
    if (DT)
      DT->deleteEdge(From, To);
    DTUDeleteEdgeTimer.stopTimer();
    PDTDeleteEdgeTimer.startTimer();
    if (PDT)
      PDT->deleteEdge(From, To);
    PDTDeleteEdgeTimer.stopTimer();
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


  if(isAuto())
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
  if(!NeedCalculate)
    return;
  if(SnapshotedBB!=&Func->getEntryBlock()) {
    recalculate(*Func);
    return;
  }
  NeedCalculate=false;
  auto Updates = diffCFG();
  DTUApplyUpdatesTimer.startTimer();    
  if(DT)
    DT->applyUpdates(Updates);
  DTUApplyUpdatesTimer.stopTimer();
  PDTUApplyUpdatesTimer.startTimer();
  if(PDT)
    PDT->applyUpdates(Updates);
  PDTUApplyUpdatesTimer.stopTimer();
}
} // namespace llvm
