//=--CheckedRegions.h---------------------------------------------*- C++-*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
// This class contains functions and classes that deal with
// adding the _Checked and _Unchecked annotations to code
// when enabled with the -addcr flag
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_3C_CHECKEDREGIONS_H
#define LLVM_CLANG_3C_CHECKEDREGIONS_H

#include "clang/3C/ProgramInfo.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/ASTTypeTraits.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include <utility>

typedef enum {
  IS_UNCHECKED,
  IS_CHECKED,
  IS_CONTAINED,
} AnnotationNeeded;

class CheckedRegionAdder
    : public clang::RecursiveASTVisitor<CheckedRegionAdder> {
public:
  explicit CheckedRegionAdder(
      clang::ASTContext *C, clang::Rewriter &R,
      std::map<llvm::FoldingSetNodeID, AnnotationNeeded> &M, ProgramInfo &I)
      : Context(C), Writer(R), Map(M), Info(I) {}

  bool VisitCompoundStmt(clang::CompoundStmt *S);
  bool VisitCallExpr(clang::CallExpr *C);

private:
  std::pair<const clang::CompoundStmt *, int>
  findParentCompound(const clang::DynTypedNode &N, int);
  bool isParentChecked(const clang::DynTypedNode &N);
  bool isWrittenChecked(const clang::CompoundStmt *);
  clang::ASTContext *Context;
  clang::Rewriter &Writer;
  std::map<llvm::FoldingSetNodeID, AnnotationNeeded> &Map;
  ProgramInfo &Info;
};

class CheckedRegionFinder
    : public clang::RecursiveASTVisitor<CheckedRegionFinder> {
public:
  explicit CheckedRegionFinder(
      clang::ASTContext *C, clang::Rewriter &R, ProgramInfo &I,
      std::set<llvm::FoldingSetNodeID> &S,
      std::map<llvm::FoldingSetNodeID, AnnotationNeeded> &M, bool EmitWarnings)
      : Context(C), Writer(R), Info(I), Seen(S), Map(M),
        EmitWarnings(EmitWarnings) {}
  bool Wild = false;

  bool VisitForStmt(clang::ForStmt *S);
  bool VisitSwitchStmt(clang::SwitchStmt *S);
  bool VisitIfStmt(clang::IfStmt *S);
  bool VisitWhileStmt(clang::WhileStmt *S);
  bool VisitDoStmt(clang::DoStmt *S);
  bool VisitCompoundStmt(clang::CompoundStmt *S);
  bool VisitStmtExpr(clang::StmtExpr *SE);
  bool VisitCStyleCastExpr(clang::CStyleCastExpr *E);
  bool VisitCallExpr(clang::CallExpr *C);
  bool VisitVarDecl(clang::VarDecl *VD);
  bool VisitParmVarDecl(clang::ParmVarDecl *PVD);
  bool VisitMemberExpr(clang::MemberExpr *E);
  bool VisitDeclRefExpr(clang::DeclRefExpr *);

private:
  void handleChildren(const clang::Stmt::child_range &Stmts);
  void markChecked(clang::CompoundStmt *S, int LocalWild);
  bool isInStatementPosition(clang::CallExpr *C);
  bool hasUncheckedParameters(clang::CompoundStmt *S);
  bool containsUncheckedPtr(clang::QualType Qt);
  bool containsUncheckedPtrAcc(clang::QualType Qt, std::set<std::string> &Seen);
  bool isUncheckedStruct(clang::QualType Qt, std::set<std::string> &Seen);
  void emitCauseDiagnostic(PersistentSourceLoc);
  bool isWild(CVarOption CVar);

  clang::ASTContext *Context;
  clang::Rewriter &Writer;
  ProgramInfo &Info;
  std::set<llvm::FoldingSetNodeID> &Seen;
  std::map<llvm::FoldingSetNodeID, AnnotationNeeded> &Map;
  std::set<PersistentSourceLoc> Emitted;
  bool EmitWarnings;
};

#endif // LLVM_CLANG_3C_CHECKEDREGIONS_H
