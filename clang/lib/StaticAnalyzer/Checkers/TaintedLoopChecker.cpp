//=== TaintedLoopChecker.cpp -----------------------------------*- C++ -*--===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file defines TaintedLoopChecker, which checks for tainted
// loop bound.
//===----------------------------------------------------------------------===//

#include "clang/AST/StmtObjC.h"
#include "clang/AST/Type.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/ParentMapContext.h"
#include "clang/StaticAnalyzer/Checkers/BuiltinCheckerRegistration.h"
#include "clang/StaticAnalyzer/Checkers/Taint.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include <optional>
#include <utility>

using namespace clang;
using namespace ento;

namespace {

class TaintedLoopChecker : public Checker<check::BranchCondition> {
  const BugType BT{this, "Loop condition is a tainted, attacker controlled value"};

public:
  void checkBranchCondition(const Stmt *Condition, CheckerContext &Ctx) const;
};

} // namespace

bool isLoopCondition(const Stmt *S, ASTContext &Ctx) {
  for (const auto &Parent : Ctx.getParents(*S)) {
    if (const auto *For = Parent.get<ForStmt>())
      return For->getCond() == S;
    if (const auto *While = Parent.get<WhileStmt>())
      return While->getCond() == S;
    if (const auto *Do = Parent.get<DoStmt>())
      return Do->getCond() == S;
  }
  return false;
}

Stmt* getBoundStmt(const Stmt *S, ASTContext &Ctx){
    if (const auto *BO = dyn_cast<BinaryOperator>(S)) {
        if (BO->isRelationalOp()){ // covers <, >, <=, >=
            if (BO->getOpcode() == BO_LT || BO->getOpcode() == BO_LE)
                return BO->getRHS();
            return BO->getLHS();
        }
    }
    return nullptr;
}

bool isSValBounded(CheckerContext &Ctx, const SVal Val){
  const ProgramStateRef St = Ctx.getState();
  SValBuilder &SVB = Ctx.getSValBuilder();
  QualType BoundType = Val.getType(Ctx.getASTContext());
  if (BoundType->isCharType())//Let's not report to such small indexes
    return true;
  QualType CmpTy = SVB.getConditionType();
  // In case the symbol is tainted, we give a warning if the
  // size is larger than TYPE_MAX/4
  BasicValueFactory &BVF = SVB.getBasicValueFactory();
  const llvm::APSInt MaxValInt = BVF.getMaxValue(BoundType);
  NonLoc MaxValue =
      SVB.makeIntVal(MaxValInt / APSIntType(MaxValInt).getValue(4));
  std::optional<NonLoc> BoundNL = Val.getAs<NonLoc>();
  auto Cmp = SVB.evalBinOpNN(St, BO_GE, *BoundNL, MaxValue, CmpTy)
                 .getAs<DefinedOrUnknownSVal>();
  if (!Cmp){
    llvm::errs()<<"TaintedLoopChecker: evalBinOpNN failed\n";
    return true;
  }
  auto [StateTooLarge, StateNotTooLarge] = St->assume(*Cmp);
  if (!StateTooLarge && StateNotTooLarge) {
    // We can prove that size is not too large so there is no issue.
    llvm::errs()<<"TaintedLoopChecker: loopbound not too large\n";
    return true;
  }
  return false;
}

void TaintedLoopChecker::checkBranchCondition(const Stmt *Condition,
                                              CheckerContext &Ctx) const {
  // ObjCForCollection is a loop, but has no actual condition.
  if (isa<ObjCForCollectionStmt>(Condition))
    return;

  if (!isLoopCondition(Condition, Ctx.getASTContext()))
   return;
  Stmt* LoopBound = getBoundStmt(Condition, Ctx.getASTContext());
  if (!LoopBound){
    llvm::errs()<<"TaintedLoopChecker: Loop bound not found\n";
    Condition->dump();
    return;
  }
  //llvm::errs() << "TaintedLoopChecker: Loop bound:\n";
  //LoopBound->dump();

  const ProgramStateRef St = Ctx.getState();
  const Expr *LoopBoundExpr = cast<Expr>(LoopBound);
  const LocationContext *LCtx = Ctx.getLocationContext();
  const SVal BoundSVal = St->getSVal(LoopBoundExpr, LCtx);

  if (!taint::isTainted(St, BoundSVal))
    return;
  // Don't report if the loop bound is reasonably bounded
  if (isSValBounded(Ctx, BoundSVal))
    return;

  // If the loop bound is tainted and unbounded, report it.
  ExplodedNode *N = Ctx.generateErrorNode();
  if (!N)
    return;

  assert(!N->pred_empty());

  // Emit the bug report.
  auto R = std::make_unique<PathSensitiveBugReport>(BT, BT.getDescription(), N);
  bugreporter::trackExpressionValue(N, LoopBoundExpr, *R);
  R->addRange(LoopBoundExpr->getSourceRange());
  std::vector<SymbolRef> TaintedSyms = taint::getTaintedSymbols(Ctx.getState(), BoundSVal);
  for (auto Sym : TaintedSyms)
      R->markInteresting(Sym);
  Ctx.emitReport(std::move(R));
}

void ento::registerTaintedLoopChecker(CheckerManager &mgr) {
  mgr.registerChecker<TaintedLoopChecker>();
}

bool ento::shouldRegisterTaintedLoopChecker(const CheckerManager &mgr) {
  return true;
}
