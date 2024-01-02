//===== BoundsDeclarationAnalysis.h - Compute flow-senstive bounds decls ====//
//
//                     The LLVM Compiler Infrastructure
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===---------------------------------------------------------------------===//
//  This file defines the interface for a dataflow analysis for determiing the
//  flow-sensitive bounds declarations that apply to a statement.
//===---------------------------------------------------------------------===//

#ifndef LLVM_CLANG_BOUNDS_DECL_EXTENT_H
#define LLVM_CLANG_BOUNDS_DECL_EXTENT_H

#include "clang/AST/CanonBounds.h"
#include "clang/AST/ExprUtils.h"
#include "clang/AST/PrettyPrinter.h"
#include "clang/Analysis/CFG.h"
#include "clang/Sema/BoundsUtils.h"
#include "clang/Sema/CheckedCAnalysesPrepass.h"
#include "clang/Sema/Sema.h"

namespace clang {

  // BoundsDeclEnv is an environment: it maps variables to flow-sensitive bounds 
  // declarations.
  using BoundsDeclEnv = llvm::DenseMap<const VarDecl *, BoundsExpr *>;

  //===-------------------------------------------------------------------===//
  // Class definition of the BoundsDeclUtil class. This class contains
  // helper methods that are used by the BounsdDeclExtent class.
  //===-------------------------------------------------------------------===//

  class BoundsDeclUtil {
  private:
    Sema &SemaRef;
    CFG *Cfg;
    ASTContext &Ctx;
    Lexicographic Lex;

  public:
    BoundsDeclUtil(Sema &SemaRef, CFG *Cfg,
                       ASTContext &Ctx, Lexicographic Lex) :
      SemaRef(SemaRef), Cfg(Cfg), Ctx(Ctx), Lex(Lex) {}

    // Compute the set difference of sets A and B.
    // @param[in] A is a set.
    // @param[in] B is a set.
    // @return The set difference of sets A and B.
    template<class T, class U>
    T Difference(T &A, U &B) const;

    // Compute the intersection of sets A and B.
    // @param[in] A is a set.
    // @param[in] B is a set.
    // @return The intersection of sets A and B.
    template<class T>
    T Intersect(T &A, T &B) const;

    // Compute the union of sets A and B.
    // @param[in] A is a set.
    // @param[in] B is a set.
    // @return The union of sets A and B.
    template<class T>
    T Union(T &A, T &B) const;

    // Determine whether sets A and B are equal. Equality is determined by
    // comparing each element in the two input sets.
    // @param[in] A is a set.
    // @param[in] B is a set.
    // @return Whether sets A and B are equal.
    template<class T>
    bool IsEqual(T &A, T &B) const;

  }; // end of BoundsDeclUtil class.

  // Note: Template specializations of a class member must be present at the
  // same namespace level as the class. So we need to declare template
  // specializations outside the class declaration.

  // Template specialization for computing the difference between BoundsDeclEnv
  // and VarSetTy.
  template<>
  BoundsDeclEnv BoundsDeclUtil::Difference<BoundsDeclEnv, VarSetTy>(
    BoundsDeclEnv &A, VarSetTy &B) const;

  // Template specialization for computing the union of BoundsDeclEnv.
  template<>
  BoundsDeclEnv BoundsDeclUtil::Union<BoundsDeclEnv>(
    BoundsDeclEnv &A, BoundsDeclEnv &B) const;

  // Template specialization for computing the intersection of BoundsDeclEnv.
  template<>
  BoundsDeclEnv BoundsDeclUtil::Intersect<BoundsDeclEnv>(
    BoundsDeclEnv &A, BoundsDeclEnv &B) const;

  // Template specialization for determining the equality of BoundsDeclEnv.
  template<>
  bool BoundsDeclUtil::IsEqual<BoundsDeclEnv>(
    BoundsDeclEnv &A, BoundsDeclEnv &B) const;

} // end namespace clang

namespace clang {
  //===-------------------------------------------------------------------===//
  // Compute the extents of bounds declarations for a functions, for functions
  // that have bounds declarations in _Where clausess, following
  // the Checked C specification.
  //===-------------------------------------------------------------------===//

  class BoundsDeclExtent {
  private:
    Sema &SemaRef;
    CFG *Cfg;
    ASTContext &Ctx;
    Lexicographic Lex;
    llvm::raw_ostream &OS;
    BoundsDeclUtil BDUtil;

    // Per-block information
    class BlockInfo {
    public:
      // The In and Out sets for the block.
      BoundsDeclEnv In, Out;

      // The Gen set for the block.
      BoundsDeclEnv Gen;

      // The Kill set for the block.
      VarSetTy Kill;
    }; // end of BlockInfo class.

    // Per-block info
    std::vector<BlockInfo> BlockState;

    // A queue of unique ElevatedCFGBlocks involved in the fixpoint of the
    // dataflow analysis.
    using WorkListTy = QueueSet<const CFGBlock>;

    // All variables that have bounds declared for them in _Where clauses.
    VarSetTy InterestingVars;
  
  public:
    BoundsDeclExtent(Sema &SemaRef, CFG *Cfg) :
      SemaRef(SemaRef), Cfg(Cfg), Ctx(SemaRef.Context),
      Lex(Lexicographic(Ctx, nullptr)), OS(llvm::outs()),
      BDUtil(BoundsDeclUtil(SemaRef, Cfg, Ctx, Lex)),
      BlockState(Cfg ? Cfg->getNumBlockIDs() : 0) {}

    // Run the dataflow analysis. 
    // @param[in] FD is the current function.
    void compute(FunctionDecl *FD);

    // Does the VarDecl have a bounds declaration in a _Where clause?
    bool hasWhereBoundsDecl(const VarDecl *V);

    // Whether the function has any where bounds decls
    bool hasAnyWhereBoundsDecls();

    // Helper class for iterating through the statements of a block and getting
    // their in/out sets.
    class BlockIterator {
    private:
      BoundsDeclExtent *ExtentAnalysis; // pointer to the closing class;
      const CFGBlock *Block;

      // The CFG element that the forward iterator is at.
      size_t CurrentElem;

      // The in/out sets for the statement.
      // Invariant: CurrentStmtIn/Out are the in/out set for CFGElement at
      // CurrentElem.  The invariant is on CFGElements, not statements, to cover
      // the case where the iterator is initialized for a block, but the first CFGElement
      // is not a statement.
      BoundsDeclEnv CurrentStmtIn, CurrentStmtOut;

    public:
      BlockIterator(BoundsDeclExtent *BE) : ExtentAnalysis(BE) {}

      // Set the iterator to the first statement of this block, if there
      // is a statement.
      void setBlock(const CFGBlock *B);

      // Advance the iterator to Stmt.
      void advance(const Stmt *Stmt);

      // Get the Out set for the current statement that the iterator is at.
      BoundsDeclEnv getStmtOut() const { return CurrentStmtOut; }

      // Get the In set for the current statement that the iterator is at.
      BoundsDeclEnv getStmtIn() const { return CurrentStmtIn; }

    private:
      void processGenKill(const CFGElement Elem, BoundsDeclEnv &Env);
    };

    // Pretty print the flow-sensitive bounds for all statements
    // in the current function.
    // @param[in] FD is the current function.
    // @param[in] PrintOption == 0: Dump bounds declarations
    //            PrintOption == 1: Dump dataflow sets.
    void dumpFlowSensitiveBoundsDecls(FunctionDecl *FD, int PrintOption);

    // Pretty print a BoundsDeclEnv.
    // @param[in] Env maps variables to their bounds declarations.
    // @param[in] EmptyMessage is the message displayed if the container is
    // empty.
    // @param[in] PrintOption == 0: Dump widened bounds
    //            PrintOption == 1: Dump dataflow sets for bounds widening
    void printBoundsEnv(BoundsDeclEnv BoundEnv, int PrintOption) const;

    // Pretty print a set of variables.
    // @param[in] VarSet is a set of variables.
    // @param[in] EmptyMessage is the message displayed if the container is
    // empty.
    // @param[in] PrintOption == 0: Dump widened bounds
    //            PrintOption == 1: Dump dataflow sets for bounds widening
    void printVarSet(VarSetTy VarSet, int PrintOption) const;

    // Pretty print a statement.
    // @param[in] CurrStmt is the statement to be printed.
    void printStmt(const Stmt *CurrStmt) const;

  private:
    // Compute Gen and Kill sets for the block.
    // @param[in] B is the current CFGBlock.
    void computeGenKillSets(const CFGBlock *B);

    // Compute the In set for the block.
    // @param[in] B is the current CFGBlock.
    // @return Return true if the In set of the block has changed, false
    // otherwise.
    bool computeInSet(const CFGBlock *B);

    // Compute the Out set for the block.
    // @param[in] B is the current CFGBlock.
    // @return Return true if the Out set of the block has changed, false
    // otherwise.
    bool computeOutSet(const CFGBlock *B);

    // Initialize the In set for the entry block.
    // @param[in] FD is the current function.
    void initEntryInSet(FunctionDecl *FD);

    // Add the successors of the current block to WorkList.
    // @param[in] CurrBlock is the current block.
    // @param[in] WorkList stores the blocks remaining to be processed for the
    // fixpoint computation.
    void addSuccsToWorkList(const CFGBlock *CurrBlock, WorkListTy &WorkList);

    // Compute the set of variables that have bounds declarations in _Where
    // clauses.
   void computeFlowSensitiveVars(FunctionDecl *FD);

   void getEnvFromStmt(Stmt *S, BoundsDeclEnv &Env, VarSetTy *IncludeDecls);

    // Construct an environment for the bounds declared in a declaration. The
    // environment is restricted to variables with flow-sensitive bounds
    // declarations.
    // @param[in] V is a variable declaration
    // @param[out] Env is a map of variables to their bounds
    // expressions. This field is updated by this function.
    void getEnvFromDecl(VarDecl *V, BoundsDeclEnv &Env,
                        VarSetTy *FlowSensitiveVars);

    // Cosntruct an environemtn for the bounds declared in a where clause.
    // @param[in] WC is the where clause.
    // @param[out] Env is a map of variables to their bounds declarations.
    // expressions. This field is updated by this function.
    void getEnvFromWhereClause(WhereClause *WC, BoundsDeclEnv &Env);

    // Order the blocks by block number to get a deterministic iteration order
    // for the blocks.
    // @return Blocks ordered by block number from higher to lower since block
    // numbers decrease from entry to exit.
    std::vector<const CFGBlock *> getOrderedBlocks() const;

  }; // end of BoundsDeclExtent class.

} // end namespace clang
#endif
