//===== BoundsWideningAnalysis.h - Dataflow analysis for bounds widening ====//
//
//                     The LLVM Compiler Infrastructure
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===---------------------------------------------------------------------===//
// This file implements a dataflow analysis that determines that extent
// of flow-sensitive bounds declarations (bounds declarations in _Where clauses).
// This is a simple forward analysis of reaching definitions.  If there are
// conflicting definitions, lower the declared bounds to bottom (unknown bounds).
//===---------------------------------------------------------------------===//

#include "clang/Sema/BoundsDeclExtent.h"

namespace clang {

//===---------------------------------------------------------------------===//
// Implementation of the methods in the BoundsDeclExtent class.
//===---------------------------------------------------------------------===//

void BoundsDeclExtent::compute(FunctionDecl *FD) {
  assert(Cfg && "expected CFG to exist");

  // Compute the set of variables that have bounds declarations in _Where
  // clauses.
  computeFlowSensitiveVars(FD);
  // The common case - exit early
  if (!hasAnyWhereBoundsDecls())
    return;

  for (CFG::iterator I = Cfg->begin(), E = Cfg->end(); I != E; ++I) {
    const CFGBlock *B = *I;
    if (!B)
      continue;

    // Compute Gen and Kill sets for the block.
    computeGenKillSets(B);

    // Initialize the In sets for the entry block.
    initEntryInSet(FD);
  }

  // WorkList stores the blocks that remain to be processed for the fixed point
  // computation. WorkList is a queue and maintains a reverse post order
  // traversal when we iterate WorkList.
  WorkListTy WorkList;

  // Initialize it to the entry block. Then add the remaining blocks to ensure
  // that even unreachable blocks are traversed once.
  WorkList.append(&Cfg->getEntry());

  for (CFG::iterator I = Cfg->begin(), E = Cfg->end(); I != E; ++I)
    if (*I && *I != &Cfg->getEntry())
      WorkList.append(*I);

  // Iteratively compute in/out sets for blocks until a fixed point is reached.
  while (!WorkList.empty()) {
    const CFGBlock *B = WorkList.next();
    WorkList.remove(B);

    bool Changed = false;
    Changed |= computeInSet(B);
    Changed |= computeOutSet(B);

    if (Changed)
      addSuccsToWorkList(B, WorkList);
  }
}

void BoundsDeclExtent::computeGenKillSets(const CFGBlock *B) {
  BlockInfo &Info = BlockState[B->getBlockID()];
  // Traverse statements in the block and compute Gen and Kill sets for each
  // statement.
  for (CFGBlock::const_iterator I = B->begin(), E = B->end(); I != E;
       ++I) {
    CFGElement Elem = *I;
    if (Elem.getKind() == CFGElement::LifetimeEnds) {
      // Every variable going out of scope is indicated by a LifetimeEnds
      // CFGElement.
      CFGLifetimeEnds LE = Elem.castAs<CFGLifetimeEnds>();
      VarDecl *V = const_cast<VarDecl *>(LE.getVarDecl());
      if (V && InterestingVars.contains(V)) {
        Info.Kill.insert(V);
        Info.Gen.erase(V);
      }
    } else if (Elem.getKind() == CFGElement::Statement) {
      if (Stmt *CurrStmt = const_cast<Stmt *>(Elem.castAs<CFGStmt>().getStmt()))
          getEnvFromStmt(CurrStmt, Info.Gen, &InterestingVars);
    }
  }
}

bool BoundsDeclExtent::computeInSet(const CFGBlock *B) {
  if (!B)
    return false;
 
  BlockInfo &Info = BlockState[B->getBlockID()];
  auto OrigIn = Info.In;

  bool first = true;
  // Intersect the out sets of the predecessors blocks of B.
  // Note: if there are no valid predecessors, EB->In is the empty
  // environment and always stays that way.
  for (const CFGBlock *PredBlock : B->preds()) {
    if (!PredBlock) {
      BlockInfo &PredInfo = BlockState[PredBlock->getBlockID()];
      if (first) {
        Info.In = PredInfo.Out;
        first = false;
      } else
        Info.In = BDUtil.Intersect(Info.In, PredInfo.Out);
    }
  }

  // Return true if the In set has changed, false otherwise.
  return !BDUtil.IsEqual(OrigIn, Info.In);
}

bool BoundsDeclExtent::computeOutSet(const CFGBlock *B) {
  if (!B)
    return false;

  BlockInfo &Info = BlockState[B->getBlockID()];
  auto OrigOut = Info.In;
  Info.Out = BDUtil.Difference(Info.In,Info.Kill);
  Info.Out = BDUtil.Union(Info.Out, Info.Gen);

  // Return true if the Out set has changed, false otherwise.
  return !BDUtil.IsEqual(OrigOut, Info.Out);
}

void BoundsDeclExtent::initEntryInSet(FunctionDecl *FD) {
  // Initialize the In set for the entry block.
  CFGBlock &Entry = Cfg->getEntry();
  BlockInfo &Info = BlockState[Entry.getBlockID()];
  for (ParmVarDecl *PD : FD->parameters())
    getEnvFromDecl(PD, Info.In, nullptr);
}

void BoundsDeclExtent::addSuccsToWorkList(const CFGBlock *CurrBlock,
                                          WorkListTy &WorkList) {
  if (!CurrBlock)
    return; 

  for (const CFGBlock *SuccBlock : CurrBlock->succs()) {
    if (SuccBlock)
      WorkList.append(SuccBlock);
  }
}

void BoundsDeclExtent::computeFlowSensitiveVars(FunctionDecl *FD) {
  BoundsDeclEnv Env;
  for (ParmVarDecl *PD : FD->parameters())
    getEnvFromDecl(PD, Env, nullptr);

  for (CFG::const_iterator I = Cfg->begin(), E = Cfg->end(); I != E; ++I) {
    CFGBlock *B = *I;
    for (CFGBlock::const_iterator SI = B->begin(),
                                  SE = B->end();
       SI != SE; ++SI) {
      CFGElement Elem = *SI;
      if (Elem.getKind() == CFGElement::Statement) {
        Stmt *CurrStmt = const_cast<Stmt *>(Elem.castAs<CFGStmt>().getStmt());
        if (CurrStmt)
          getEnvFromStmt(CurrStmt, Env, nullptr);
      }
    }
  }

  // Convert domain(Env) to a set.
  InterestingVars.clear();
  for (auto VarBoundsPair : Env)
    InterestingVars.insert(VarBoundsPair.first);
}

// If FlowSensitiveVars is non-null, add bounds declared at declarations of variables
// that are in FlowSensitiveVars to Env.
void BoundsDeclExtent::getEnvFromStmt(Stmt *S, BoundsDeclEnv &Env, 
                                      VarSetTy *FlowSensitiveVars) {
  if (auto *DS = dyn_cast<DeclStmt>(S)) {
    for (Decl *D : DS->decls())
      if (auto *V = dyn_cast<VarDecl>(D))
        getEnvFromDecl(V, Env, FlowSensitiveVars);
  } else if (auto *VS = dyn_cast<ValueStmt>(S))
    getEnvFromWhereClause(VS->getWhereClause(), Env);
  else if (auto *NS = dyn_cast<NullStmt>(S))
    // TODO: Currently, a null statement does not occur in the list of
    // statements of a block.
    getEnvFromWhereClause(NS->getWhereClause(), Env);
}


void BoundsDeclExtent::getEnvFromDecl(VarDecl *V, BoundsDeclEnv &Env, 
                                      VarSetTy *FlowSensitiveVars) {
  if (FlowSensitiveVars && FlowSensitiveVars->contains(V) && V->hasBoundsExpr())
    Env[V] = V->getBoundsExpr();
  getEnvFromWhereClause(V->getWhereClause(), Env);
}

void BoundsDeclExtent::getEnvFromWhereClause(WhereClause *WC, BoundsDeclEnv &Env) {
  if (!WC)
    return;

  for (auto *Fact : WC->getFacts()) {
    if (auto *F = dyn_cast<BoundsDeclFact>(Fact)) {
      VarDecl *V = F->getVarDecl();
      Env[V] = F->getBoundsExpr();
    }
  }
}

bool BoundsDeclExtent::hasAnyWhereBoundsDecls() {
  return InterestingVars.size() > 0;
}

bool BoundsDeclExtent::hasWhereBoundsDecl(const VarDecl *V) {
  return InterestingVars.contains(V);
}

void BoundsDeclExtent::BlockIterator::setBlock(const CFGBlock *B) {
  if (!B)
    return;

  Block = B;
  CurrentElem = 0;
  CurrentStmtIn = ExtentAnalysis->BlockState[B->getBlockID()].In;
  CurrentStmtOut = CurrentStmtIn;
  if (B->size() >= 1)
    processGenKill((*B)[0], CurrentStmtOut);
}

void BoundsDeclExtent::BlockIterator::processGenKill(CFGElement Elem, BoundsDeclEnv &Env) {
  if (Elem.getKind() == CFGElement::LifetimeEnds) {
    // Kill
    CFGLifetimeEnds LE = Elem.castAs<CFGLifetimeEnds>();
    VarDecl *V = const_cast<VarDecl *>(LE.getVarDecl());
    if (V && ExtentAnalysis->InterestingVars.contains(V))
      Env.erase(V);
    else if (Elem.getKind() == CFGElement::Statement) {
     // Gen
     if (Stmt *CurrStmt = const_cast<Stmt *>(Elem.castAs<CFGStmt>().getStmt()))
       ExtentAnalysis->getEnvFromStmt(CurrStmt, Env, &ExtentAnalysis->InterestingVars);
    }
  }
}

void BoundsDeclExtent::BlockIterator::advance(const Stmt *NextStmt) {
  while (CurrentElem < Block->size()) {
    CFGElement Elem = (*Block)[CurrentElem];
    if (Elem.getKind() == CFGElement::Statement) {
      if (const Stmt *CurrStmt = Elem.castAs<CFGStmt>().getStmt())
        if (CurrStmt == NextStmt)
          return;
    }
    CurrentElem++;
    CurrentStmtIn = CurrentStmtOut;
    processGenKill(Elem, CurrentStmtOut);
  }
  llvm_unreachable("Statement not found");
}

void BoundsDeclExtent::printVarSet(VarSetTy VarSet,
                                   int PrintOption) const {
  if (VarSet.size() == 0) {
    if (PrintOption == 0)
      OS << "<no flow-sensitive bounds>\n";
    else
      OS << "    {}\n";
    return;
  }

  // A VarSetTy has const iterator. So we cannot simply sort a VarSetTy and
  // need to copy the elements to a vector to sort.
  std::vector<const VarDecl *> Vars(VarSet.begin(), VarSet.end());

  llvm::sort(Vars.begin(), Vars.end(),
    [](const VarDecl *A, const VarDecl *B) {
       return A->getQualifiedNameAsString().compare(
              B->getQualifiedNameAsString()) < 0;
    });

  for (const VarDecl *V : Vars)
    OS << "    " << V->getQualifiedNameAsString() << "\n";
}

void BoundsDeclExtent::printBoundsEnv(BoundsDeclEnv BoundsMap,
                                      int PrintOption) const {
  if (BoundsMap.size() == 0) {
    if (PrintOption == 0)
      OS << "<no flow-sensitive bounds>\n";
    else
      OS << "    {}\n";
    return;
  }

  std::vector<const VarDecl *> Vars;
  for (auto VarBoundsPair : BoundsMap)
    Vars.push_back(VarBoundsPair.first);

  llvm::sort(Vars.begin(), Vars.end(),
    [](const VarDecl *A, const VarDecl *B) {
       return A->getQualifiedNameAsString().compare(
              B->getQualifiedNameAsString()) < 0;
    });

  for (const VarDecl *V : Vars) {
    OS << "    " << V->getQualifiedNameAsString() << ": ";

    const BoundsExpr *Bounds = BoundsMap[V];
    if (!Bounds)
      OS << "bottom";
    else
      Bounds->printPretty(OS, nullptr, Ctx.getPrintingPolicy());
  }
}

void BoundsDeclExtent::printStmt(const Stmt *CurrStmt) const {
  if (!CurrStmt) {
    OS << "\n";
    return;
  }

  std::string Str;
  llvm::raw_string_ostream SS(Str);
  CurrStmt->printPretty(SS, nullptr, Ctx.getPrintingPolicy());

  OS << SS.str();
  if (SS.str().back() != '\n')
    OS << "\n";
}

void BoundsDeclExtent::dumpFlowSensitiveBoundsDecls(FunctionDecl *FD,
                                                    int PrintOption) {
  BlockIterator Iterator(this);

  OS << "\n--------------------------------------";
  // Print the function name.
  OS << "\nFunction: " << FD->getName();

  for (const CFGBlock *CurrBlock : getOrderedBlocks()) {
    unsigned BlockID = CurrBlock->getBlockID();

    // Print the current block number.
    OS << "\nBlock: B" << BlockID;
    if (CurrBlock == &Cfg->getEntry())
      OS << " (Entry)";

    // Print the predecessor blocks of the current block.
    OS << ", Pred: ";
    for (const CFGBlock *PredBlock : CurrBlock->preds()) {
      if (PredBlock)
        OS << "B" << PredBlock->getBlockID() << ", ";
    }

    // Print the successor blocks of the current block.
    OS << "Succ: ";
    for (const CFGBlock *SuccBlock : CurrBlock->succs()) {
      if (SuccBlock) {
        OS << "B" << SuccBlock->getBlockID();

        if (SuccBlock != *(CurrBlock->succs().end() - 1))
          OS << ", ";
        }
    }

    BlockInfo &Info = BlockState[BlockID];

    if (PrintOption == 1) {
      // Print the In set for the block.
      OS << "\n  In:\n";
      printBoundsEnv(Info.In, PrintOption);

      // Print the Out set for the block.
      OS << "  Out:\n";
      printBoundsEnv(Info.Out, PrintOption);
    }

    if (CurrBlock->empty()) {
      OS << "\n";
      continue;
    }

    Iterator.setBlock(CurrBlock);
    for (CFGElement Elem : *CurrBlock) {
      if (Elem.getKind() != CFGElement::Statement)
        continue;
      const Stmt *CurrStmt = Elem.castAs<CFGStmt>().getStmt();
      if (!CurrStmt)
        continue;
      Iterator.advance(CurrStmt);
      
      if (PrintOption == 0) {
        OS << "\n  Flow-sensitive bounds before stmt: ";
      } else if (PrintOption == 1) {
        OS << "\n  Stmt: ";
      }

      // Print the current statement.
      printStmt(CurrStmt);

      if (PrintOption == 0) {
        // Print widened bounds before the statement.
        printBoundsEnv(Iterator.getStmtIn(), PrintOption);

      } else if (PrintOption == 1) {
        // Print the In set for the statement.
        OS << "  In:\n";
        printBoundsEnv(Iterator.getStmtIn(), PrintOption);

        // Print the Out set for the statement.
        OS << "  Out:\n";
        printBoundsEnv(Iterator.getStmtOut(), PrintOption);
      }
    }
  }
}

std::vector<const CFGBlock *> BoundsDeclExtent::getOrderedBlocks() const {
  size_t NumBlockIds = Cfg->getNumBlockIDs();
  std::vector<const CFGBlock *> Result(Cfg->getNumBlockIDs());
  // We order the CFG blocks based on block ID. Block IDs decrease from entry
  // to exit. So we sort in the reverse order.
  for (CFG::const_iterator I = Cfg->begin(), E = Cfg->end(); I != E; ++I) {
    const CFGBlock *Block = *I;
    Result[NumBlockIds - Block->getBlockID()] = Block;
  }
  return Result;
}

// end of methods for the BoundsDeclExtent class.

//===---------------------------------------------------------------------===//
// Implementation of the methods in the BoundsDeclUtil class. This class
// contains helper methods that are used by the BoundsDeclExtent class to
// perform the dataflow analysis.
//===---------------------------------------------------------------------===//

// Common templated set operation functions.
template<class T, class U>
T BoundsDeclUtil::Difference(T &A, U &B) const {
  if (!A.size() || !B.size())
    return A;

  auto CopyA = A;
  for (auto Item : A) {
    if (B.count(Item))
      CopyA.erase(Item);
  }
  return CopyA;
}

template<class T>
T BoundsDeclUtil::Union(T &A, T &B) const {
  auto CopyA = A;
  for (auto Item : B)
    CopyA.insert(Item);

  return CopyA;
}

template<class T>
T BoundsDeclUtil::Intersect(T &A, T &B) const {
  if (!A.size() || !B.size())
    return T();

  auto CopyA = A;
  for (auto Item : A) {
    if (!B.count(Item))
      CopyA.erase(Item);
  }
  return CopyA;
}

template<class T>
bool BoundsDeclUtil::IsEqual(T &A, T &B) const {
  return A.size() == B.size() &&
         A.size() == Intersect(A, B).size();
}

// Template specializations of common set operation functions.
template<>
BoundsDeclEnv BoundsDeclUtil::Difference<BoundsDeclEnv, VarSetTy>(
  BoundsDeclEnv &A, VarSetTy &B) const {

  if (!A.size() || !B.size())
    return A;

  auto CopyA = A;
  for (auto VarBoundsPair : A) {
    if (B.count(VarBoundsPair.first))
      CopyA.erase(VarBoundsPair.first);
  }
  return CopyA;
}

template<>
BoundsDeclEnv BoundsDeclUtil::Intersect<BoundsDeclEnv>(
  BoundsDeclEnv &A, BoundsDeclEnv &B) const {

  if (!A.size() || !B.size()) 
    return BoundsDeclEnv();

  auto CopyA = A;
  for (auto VarBoundsPair : B) {
    const VarDecl *V = VarBoundsPair.first;
    auto VarBoundsIt = CopyA.find(V);
    if (VarBoundsIt == CopyA.end()) {
      CopyA.erase(V);
      continue;
    }

    BoundsExpr *BoundsA = VarBoundsIt->second;
    BoundsExpr *BoundsB = VarBoundsPair.second;

    if (Lex.CompareExprSemantically(BoundsA, BoundsB))
      CopyA[V] = BoundsA;
    else
      CopyA[V] = Ctx.getPrebuiltBoundsUnknown();
  }
  return CopyA;
}

template<>
BoundsDeclEnv BoundsDeclUtil::Union<BoundsDeclEnv>(
  BoundsDeclEnv &A, BoundsDeclEnv &B) const {

  auto CopyA = A;
  for (auto VarBoundsPair : B)
    CopyA[VarBoundsPair.first] = VarBoundsPair.second;

  return CopyA;
}

template<>
bool BoundsDeclUtil::IsEqual<BoundsDeclEnv>(
  BoundsDeclEnv &A, BoundsDeclEnv &B) const {

  if (A.size() != B.size())
    return false;

  auto CopyA = A;
  for (auto VarBoundsPair : B) {
    const VarDecl *V = VarBoundsPair.first;

    auto VarBoundsIt = CopyA.find(V);
    if (VarBoundsIt == CopyA.end())
      return false;

    const BoundsExpr *BoundsA = VarBoundsIt->second;
    const BoundsExpr *BoundsB = VarBoundsPair.second;

    if (!Lex.CompareExprSemantically(BoundsA, BoundsB))
      return false;
  }
  return true;
}
// end of methods for the BoundsDeclUtil class.

} // end namespace clang
