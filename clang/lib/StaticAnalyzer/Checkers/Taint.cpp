//=== Taint.cpp - Taint tracking and basic propagation rules. ------*- C++ -*-//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Defines basic, non-domain-specific mechanisms for tracking tainted values.
//
//===----------------------------------------------------------------------===//

#include "clang/StaticAnalyzer/Checkers/Taint.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugReporter.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramStateTrait.h"

using namespace clang;
using namespace ento;
using namespace taint;

// Fully tainted symbols.
REGISTER_MAP_WITH_PROGRAMSTATE(TaintMap, SymbolRef, TaintData)

// Partially tainted symbols.
REGISTER_MAP_FACTORY_WITH_PROGRAMSTATE(TaintedSubRegions, const SubRegion *,
                                       TaintData)
REGISTER_MAP_WITH_PROGRAMSTATE(DerivedSymTaint, SymbolRef, TaintedSubRegions)

void taint::printTaint(ProgramStateRef State, raw_ostream &Out, const char *NL,
                       const char *Sep) {
  TaintMapTy TM = State->get<TaintMap>();

  if (!TM.isEmpty())
    Out << "Tainted symbols:" << NL;

  for (const auto &I : TM)
    Out << I.first << " : " << I.second << NL;
}

void taint::dumpTaint(ProgramStateRef State) {
  printTaint(State, llvm::errs());
}

ProgramStateRef taint::addTaint(ProgramStateRef State, const Stmt *S,
                                const LocationContext *LCtx, TaintData Data) {
  return addTaint(State, State->getSVal(S, LCtx), Data);
}

ProgramStateRef taint::addTaint(ProgramStateRef State, SVal V, TaintData Data) {
  SymbolRef Sym = V.getAsSymbol();
  if (Sym)
    return addTaint(State, Sym, Data);

  // If the SVal represents a structure, try to mass-taint all values within the
  // structure. For now it only works efficiently on lazy compound values that
  // were conjured during a conservative evaluation of a function - either as
  // return values of functions that return structures or arrays by value, or as
  // values of structures or arrays passed into the function by reference,
  // directly or through pointer aliasing. Such lazy compound values are
  // characterized by having exactly one binding in their captured store within
  // their parent region, which is a conjured symbol default-bound to the base
  // region of the parent region.
  if (auto LCV = V.getAs<nonloc::LazyCompoundVal>()) {
    if (std::optional<SVal> binding =
            State->getStateManager().getStoreManager().getDefaultBinding(
                *LCV)) {
      if (SymbolRef Sym = binding->getAsSymbol())
        return addPartialTaint(State, Sym, LCV->getRegion(), Data);
    }
  }

  const MemRegion *R = V.getAsRegion();
  return addTaint(State, R, Data);
}

ProgramStateRef taint::addTaint(ProgramStateRef State, const MemRegion *R,
                                TaintData Data) {
  if (const SymbolicRegion *SR = dyn_cast_or_null<SymbolicRegion>(R))
    return addTaint(State, SR->getSymbol(), Data);
  return State;
}

ProgramStateRef taint::addTaint(ProgramStateRef State, SymbolRef Sym,
                                TaintData Data) {
  // If this is a symbol cast, remove the cast before adding the taint. Taint
  // is cast agnostic.
  while (const SymbolCast *SC = dyn_cast<SymbolCast>(Sym))
    Sym = SC->getOperand();

  ProgramStateRef NewState = State->set<TaintMap>(Sym, Data);
  assert(NewState);
  return NewState;
}

ProgramStateRef taint::removeTaint(ProgramStateRef State, SVal V) {
  SymbolRef Sym = V.getAsSymbol();
  if (Sym)
    return removeTaint(State, Sym);

  const MemRegion *R = V.getAsRegion();
  return removeTaint(State, R);
}

ProgramStateRef taint::removeTaint(ProgramStateRef State, const MemRegion *R) {
  if (const SymbolicRegion *SR = dyn_cast_or_null<SymbolicRegion>(R))
    return removeTaint(State, SR->getSymbol());
  return State;
}

ProgramStateRef taint::removeTaint(ProgramStateRef State, SymbolRef Sym) {
  // If this is a symbol cast, remove the cast before adding the taint. Taint
  // is cast agnostic.
  while (const SymbolCast *SC = dyn_cast<SymbolCast>(Sym))
    Sym = SC->getOperand();

  ProgramStateRef NewState = State->remove<TaintMap>(Sym);
  assert(NewState);
  return NewState;
}

ProgramStateRef taint::addPartialTaint(ProgramStateRef State,
                                       SymbolRef ParentSym,
                                       const SubRegion *SubRegion,
                                       TaintData Data) {
  // Ignore partial taint if the entire parent symbol is already tainted.
  if (const TaintData *T = State->get<TaintMap>(ParentSym))
    if (T->Type == Data.Type)
      return State;

  // Partial taint applies if only a portion of the symbol is tainted.
  if (SubRegion == SubRegion->getBaseRegion())
    return addTaint(State, ParentSym, Data);

  const TaintedSubRegions *SavedRegs = State->get<DerivedSymTaint>(ParentSym);
  TaintedSubRegions::Factory &F = State->get_context<TaintedSubRegions>();
  TaintedSubRegions Regs = SavedRegs ? *SavedRegs : F.getEmptyMap();

  Regs = F.add(Regs, SubRegion, Data);
  ProgramStateRef NewState = State->set<DerivedSymTaint>(ParentSym, Regs);
  assert(NewState);
  return NewState;
}

std::optional<TaintData> taint::getTaintData(ProgramStateRef State, const Stmt *S,
                                        const LocationContext *LCtx) {
  SVal val = State->getSVal(S, LCtx);
  return getTaintData(State, val);
}

std::optional<TaintData> taint::getTaintData(ProgramStateRef State, SVal V) {
  if (SymbolRef Sym = V.getAsSymbol())
    return getTaintData(State, Sym);
  if (const MemRegion *Reg = V.getAsRegion())
    return getTaintData(State, Reg);
  return std::nullopt;
}

std::optional<TaintData> taint::getTaintData(ProgramStateRef State, SymbolRef Sym) {
  if (!Sym)
    return std::nullopt;

  // Traverse all the symbols this symbol depends on to see if any are tainted.
  for (SymExpr::symbol_iterator SI = Sym->symbol_begin(),
                                SE = Sym->symbol_end();
       SI != SE; ++SI) {
    if (!isa<SymbolData>(*SI))
      continue;

    if (const TaintData *Data = State->get<TaintMap>(*SI)) {
      return *Data;
    }

    if (const auto *SD = dyn_cast<SymbolDerived>(*SI)) {
      // If this is a SymbolDerived with a tainted parent, it's also tainted.
      if (getTaintData(State, SD->getParentSymbol()))
        return getTaintData(State, SD->getParentSymbol());

      // If this is a SymbolDerived with the same parent symbol as another
      // tainted SymbolDerived and a region that's a sub-region of that tainted
      // symbol, it's also tainted.
      if (const TaintedSubRegions *Regs =
              State->get<DerivedSymTaint>(SD->getParentSymbol())) {
        const TypedValueRegion *R = SD->getRegion();
        for (auto I : *Regs) {
          // FIXME: The logic to identify tainted regions could be more
          // complete. For example, this would not currently identify
          // overlapping fields in a union as tainted. To identify this we can
          // check for overlapping/nested byte offsets.
          if (R->isSubRegionOf(I.first))
            return I.second;
        }
      }
    }

    // If memory region is tainted, data is also tainted.
    if (const auto *SRV = dyn_cast<SymbolRegionValue>(*SI)) {
      if (getTaintData(State, SRV->getRegion()))
        return getTaintData(State, SRV->getRegion());
    }

    // If this is a SymbolCast from a tainted value, it's also tainted.
    if (const auto *SC = dyn_cast<SymbolCast>(*SI)) {
      if (getTaintData(State, SC->getOperand()))
        return getTaintData(State, SC->getOperand());
    }
  }
  return std::nullopt;
}

std::optional<TaintData> taint::getTaintData(ProgramStateRef State,
                                        const MemRegion *Reg) {
  if (!Reg)
    return std::nullopt;

  // Element region (array element) is tainted if either the base or the offset
  // are tainted.
  if (const ElementRegion *ER = dyn_cast<ElementRegion>(Reg)) {
    if (getTaintData(State, ER->getSuperRegion()))
      return getTaintData(State, ER->getSuperRegion());
    else
      return getTaintData(State, ER->getIndex());
  }

  if (const SymbolicRegion *SR = dyn_cast<SymbolicRegion>(Reg))
    return getTaintData(State, SR->getSymbol());

  if (const SubRegion *ER = dyn_cast<SubRegion>(Reg))
    return getTaintData(State, ER->getSuperRegion());

  return std::nullopt;
}

bool taint::isStdin(SVal Val, const ASTContext &ACtx) {
  // FIXME: What if Val is NonParamVarRegion?

  // The region should be symbolic, we do not know it's value.
  const auto *SymReg = dyn_cast_or_null<SymbolicRegion>(Val.getAsRegion());
  if (!SymReg)
    return false;

  // Get it's symbol and find the declaration region it's pointing to.
  const auto *DeclReg =
      dyn_cast_or_null<DeclRegion>(SymReg->getSymbol()->getOriginRegion());
  if (!DeclReg)
    return false;

  // This region corresponds to a declaration, find out if it's a global/extern
  // variable named stdin with the proper type.
  if (const auto *D = dyn_cast_or_null<VarDecl>(DeclReg->getDecl())) {
    D = D->getCanonicalDecl();
    // FIXME: This should look for an exact match.
    if (D->getName().contains("stdin") && D->isExternC()) {
      const QualType FILETy = ACtx.getFILEType().getCanonicalType();
      const QualType Ty = D->getType().getCanonicalType();

      if (Ty->isPointerType())
        return Ty->getPointeeType() == FILETy;
    }
  }
  return false;
}

std::optional<TaintData> taint::getTaintDataPointeeOrPointer(const CheckerContext &C,
                                                        SVal Arg) {
  const ProgramStateRef State = C.getState();

  if (auto Pointee = getPointeeOf(C, Arg))
    if (isTainted(State, *Pointee))
      return getTaintData(State, *Pointee);

  if (isTainted(State, Arg))
    return getTaintData(State, Arg);

  return std::nullopt;
}

std::optional<TaintData>
taint::getTaintDataPointeeOrPointer(const Expr *E, const ProgramStateRef &State,
                                    CheckerContext &C) {
  return getTaintDataPointeeOrPointer(C, C.getSVal(E));
}

SVal taint::getPointeeOf(const CheckerContext &C, Loc LValue) {
  const QualType ArgTy = LValue.getType(C.getASTContext());
  if (!ArgTy->isPointerType() || !ArgTy->getPointeeType()->isVoidType())
    return C.getState()->getSVal(LValue);

  // Do not dereference void pointers. Treat them as byte pointers instead.
  // FIXME: we might want to consider more than just the first byte.
  return C.getState()->getSVal(LValue, C.getASTContext().CharTy);
}

/// Given a pointer/reference argument, return the value it refers to.
std::optional<SVal> taint::getPointeeOf(const CheckerContext &C, SVal Arg) {
  if (auto LValue = Arg.getAs<Loc>())
    return getPointeeOf(C, *LValue);
  return std::nullopt;
}

bool taint::isTainted(ProgramStateRef State, const Stmt *S,
                      const LocationContext *LCtx, TaintTagType Kind) {
  SVal val = State->getSVal(S, LCtx);
  return isTainted(State, val, Kind);
}

bool taint::isTainted(ProgramStateRef State, SVal V, TaintTagType Kind) {
  if (SymbolRef Sym = V.getAsSymbol())
    return isTainted(State, Sym, Kind);
  if (const MemRegion *Reg = V.getAsRegion())
    return isTainted(State, Reg, Kind);
  return false;
}

bool taint::isTainted(ProgramStateRef State, const MemRegion *Reg,
                      TaintTagType Kind) {
  if (!Reg)
    return false;
  std::optional<TaintData> TD = getTaintData(State, Reg);
  return TD ? (TD->Type == Kind) : false;
}

bool taint::isTainted(ProgramStateRef State, SymbolRef Sym, TaintTagType Kind) {
  if (!Sym)
    return false;
  std::optional<TaintData> TD = getTaintData(State, Sym);
  return TD ? (TD->Type == Kind) : false;
}