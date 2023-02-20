//=== Taint.h - Taint tracking and basic propagation rules. --------*- C++ -*-//
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

#ifndef LLVM_CLANG_LIB_STATICANALYZER_CHECKERS_TAINT_H
#define LLVM_CLANG_LIB_STATICANALYZER_CHECKERS_TAINT_H

#include "clang/StaticAnalyzer/Core/BugReporter/BugReporter.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugReporterVisitors.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramState.h"

namespace clang {
namespace ento {
namespace taint {

/// The type of taint, which helps to differentiate between different types of
/// taint.
using TaintTagType = unsigned;
using TaintFlowType = int;

static constexpr TaintTagType TaintTagGeneric = 0;
static constexpr TaintFlowType UninitializedFlow = -1;

/// Used to store the taint flow related information
/// in the program state.
struct TaintData {
  TaintTagType Type; // Type of the taintedness (e.g. sql escape checked)
  TaintFlowType Flow; // Unique identifier of the taint flow
  TaintData() : Type(TaintTagGeneric), Flow(UninitializedFlow){};
  TaintData(TaintFlowType f) : Type(TaintTagGeneric), Flow(f){};
  TaintData(TaintTagType t, TaintFlowType f) : Type(t), Flow(f){};
  bool operator==(const TaintData &X) const { return Flow == X.Flow; }
  int operator<(const TaintData &X) const { return Flow < X.Flow; }
  void Profile(llvm::FoldingSetNodeID &ID) const { ID.AddInteger(Flow); }
};

static inline raw_ostream &operator<<(llvm::raw_ostream &Out,
                                      const clang::ento::taint::TaintData t) {
  Out << "Type:" << t.Type << " Flow:" << t.Flow << "\n";
  return Out;
}

/// Create a new state in which the value of the statement is marked as tainted.
[[nodiscard]] ProgramStateRef addTaint(ProgramStateRef State, const Stmt *S,
                                       const LocationContext *LCtx,
                                       TaintData Data = TaintData());

/// Create a new state in which the value is marked as tainted.
[[nodiscard]] ProgramStateRef addTaint(ProgramStateRef State, SVal V,
                                       TaintData Data = TaintData());

/// Create a new state in which the symbol is marked as tainted.
[[nodiscard]] ProgramStateRef addTaint(ProgramStateRef State, SymbolRef Sym,
                                       TaintData Data = TaintData());

/// Create a new state in which the pointer represented by the region
/// is marked as tainted.
[[nodiscard]] ProgramStateRef addTaint(ProgramStateRef State,
                                       const MemRegion *R,
                                       TaintData Data = TaintData());

[[nodiscard]] ProgramStateRef removeTaint(ProgramStateRef State, SVal V);

[[nodiscard]] ProgramStateRef removeTaint(ProgramStateRef State,
                                          const MemRegion *R);

[[nodiscard]] ProgramStateRef removeTaint(ProgramStateRef State, SymbolRef Sym);

/// Create a new state in a which a sub-region of a given symbol is tainted.
/// This might be necessary when referring to regions that can not have an
/// individual symbol, e.g. if they are represented by the default binding of
/// a LazyCompoundVal.
[[nodiscard]] ProgramStateRef addPartialTaint(ProgramStateRef State,
                                              SymbolRef ParentSym,
                                              const SubRegion *SubRegion,
                                              TaintData = TaintData());

std::optional<TaintData> getTaintData(ProgramStateRef State, const Stmt *S,
                                 const LocationContext *LCtx);

/// Get the taint data for a value if tainted in the given state.
std::optional<TaintData> getTaintData(ProgramStateRef State, SVal V);

/// Get the taint data for symbol if tainted in the given state.
std::optional<TaintData> getTaintData(ProgramStateRef State, SymbolRef Sym);

/// Get the Taint data for a pointer represented by the region
// if tainted in the given state.
std::optional<TaintData> getTaintData(ProgramStateRef State, const MemRegion *Reg);

/// Check if the region the expression evaluates to is the standard input,
/// and thus, is tainted.
bool isStdin(SVal Val, const ASTContext &ACtx);

/// Returns the TaintData for a pointed value (if tainted), otherwise
/// the TaintData of the pointer itself.
std::optional<TaintData> getTaintDataPointeeOrPointer(const CheckerContext &C,
                                                 SVal Arg);
std::optional<TaintData> getTaintDataPointeeOrPointer(const Expr *E,
                                                 const ProgramStateRef &State,
                                                 CheckerContext &C);

SVal getPointeeOf(const CheckerContext &C, Loc LValue);
std::optional<SVal> getPointeeOf(const CheckerContext &C, SVal Arg);

/// Check if the statement has a tainted value in the given state.
bool isTainted(ProgramStateRef State, const Stmt *S,
               const LocationContext *LCtx,
               TaintTagType Kind = TaintTagGeneric);

/// Check if the value is tainted in the given state.
bool isTainted(ProgramStateRef State, SVal V,
               TaintTagType Kind = TaintTagGeneric);

/// Check if the symbol is tainted in the given state.
bool isTainted(ProgramStateRef State, SymbolRef Sym,
               TaintTagType Kind = TaintTagGeneric);

/// Check if the pointer represented by the region is tainted in the given
/// state.
bool isTainted(ProgramStateRef State, const MemRegion *Reg,
               TaintTagType Kind = TaintTagGeneric);

void printTaint(ProgramStateRef State, raw_ostream &Out, const char *nl = "\n",
                const char *sep = "");

LLVM_DUMP_METHOD void dumpTaint(ProgramStateRef State);

/// Always use TaintBugReport to give taint related warnings in any checker.
/// The TaintData member carries the flow associated data of the tainted SVal
class TaintBugReport : public clang::ento::PathSensitiveBugReport {
public:
  TaintBugReport(const BugType &bt, StringRef desc,
                 const ExplodedNode *errorNode, TaintData T)
      : clang::ento::PathSensitiveBugReport(bt, desc, errorNode,
                                            Kind::TaintPathSensitive),
        taint_data(T){};
  static bool classof(const BugReport *R) {
    return R->getKind() == Kind::TaintPathSensitive;
  }
  TaintData taint_data;
};

} // namespace taint
} // namespace ento
} // namespace clang

#endif
