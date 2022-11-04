//===- unittests/Analysis/FlowSensitive/SignAnalysisTest.cpp --===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
//  This file defines a simplistic version of Sign Analysis as an example
//  of a forward, monotonic dataflow analysis. The analysis tracks all
//  variables in the scope, but lacks escape analysis.
//
//===----------------------------------------------------------------------===//

#include "TestingSupport.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Analysis/FlowSensitive/DataflowAnalysis.h"
#include "clang/Analysis/FlowSensitive/DataflowEnvironment.h"
#include "clang/Analysis/FlowSensitive/DataflowLattice.h"
#include "clang/Analysis/FlowSensitive/MapLattice.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/ADT/None.h"
#include "llvm/ADT/Optional.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/Twine.h"
#include "llvm/Support/Error.h"
#include "llvm/Testing/Support/Annotations.h"
#include "llvm/Testing/Support/Error.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include <cstdint>
#include <memory>
#include <ostream>
#include <string>
#include <utility>

namespace clang {
namespace dataflow {
namespace {
using namespace ast_matchers;

// Models the signedness of a variable, for all paths through
// the program.
struct TaintLattice {
  enum class TaintState : int {
    Bottom,
    Untainted,
    Tainted,
    Top,
  };
  TaintState State;

  constexpr TaintLattice() : State(TaintState::Bottom) {}
  constexpr TaintLattice(TaintState S) : State(S) {}

  static constexpr TaintLattice bottom() {
    return TaintLattice(TaintState::Bottom);
  }
  static constexpr TaintLattice untainted() {
    return TaintLattice(TaintState::Untainted);
  }
  static constexpr TaintLattice tainted() {
    return TaintLattice(TaintState::Tainted);
  }
  static constexpr TaintLattice top() { return TaintLattice(TaintState::Top); }

  friend bool operator==(const TaintLattice &Lhs, const TaintLattice &Rhs) {
    return Lhs.State == Rhs.State;
  }
  friend bool operator!=(const TaintLattice &Lhs, const TaintLattice &Rhs) {
    return !(Lhs == Rhs);
  }

  void printLattice(const TaintLattice &l){
    if (l==bottom())
      llvm::errs()<<"bottom\n";
    if (l==top())
      llvm::errs()<<"top\n";
    if (l==untainted())
      llvm::errs()<<"untainted\n";
    if (l==tainted())
      llvm::errs()<<"tainted\n";
  }

  LatticeJoinEffect join(const TaintLattice &Other) {
    std::string txt="";
    llvm::errs()<<"JOIN this\n";
    printLattice(*this);
    llvm::errs()<<"other: \n";
    printLattice(Other);

    if (*this == Other || Other == bottom() || *this == top()){
      llvm::errs()<<"LATTICE unchanged\n";
      return LatticeJoinEffect::Unchanged;
    }

    if (*this == bottom()) {
      *this = Other;
      llvm::errs()<<"LATTICE changed to OTHER\n";
      return LatticeJoinEffect::Changed;
    }

    llvm::errs()<<"LATTICE changed to TOP.\n";
    *this = top();
    return LatticeJoinEffect::Changed;
  }
};

std::ostream &operator<<(std::ostream &OS, const TaintLattice &L) {
  switch (L.State) {
  case TaintLattice::TaintState::Bottom:
    return OS << "Bottom";
  case TaintLattice::TaintState::Untainted:
    return OS << "Untainted";
  case TaintLattice::TaintState::Tainted:
    return OS << "Tainted";
  case TaintLattice::TaintState::Top:
    return OS << "Top";
  }
  llvm_unreachable("unknown TaintState!");
}

using TaintPropagationLattice = VarMapLattice<TaintLattice>;

constexpr char kDecl[] = "decl";
constexpr char kVar[] = "var";
constexpr char kRHSVar[] = "rhsvar";
constexpr char kInit[] = "init";
constexpr char kJustAssignment[] = "just-assignment";
constexpr char kAssignment[] = "assignment";
constexpr char kComparison[] = "comparison";
constexpr char kRHS[] = "rhs";

auto refToVar(StringRef V) { return declRefExpr(to(varDecl().bind(V))); }

// N.B. This analysis is deliberately simplistic, leaving out many important
// details needed for a real analysis. Most notably, the transfer function does
// not account for the variable's address possibly escaping, which would
// invalidate the analysis. It also could be optimized to drop out-of-scope
// variables from the map.
class TaintPropagationAnalysis
    : public DataflowAnalysis<TaintPropagationAnalysis, TaintPropagationLattice> {
public:
  explicit TaintPropagationAnalysis(ASTContext &Context)
      : DataflowAnalysis<TaintPropagationAnalysis, TaintPropagationLattice>(
            Context) {}

  static TaintPropagationLattice initialElement() {
    return TaintPropagationLattice::bottom();
  }

  TaintLattice evaluateTaintExpr(const Stmt *S, TaintPropagationLattice &Vars) {
    ASTContext &Context = getASTContext();
    auto matcher =
        stmt(anyOf(callExpr(callee(functionDecl().bind("func"))),
                   declRefExpr(to(varDecl().bind("var"))),
                   hasDescendant(callExpr(callee(functionDecl().bind("func")))),
                   hasDescendant(declRefExpr(to(varDecl().bind("var"))))
                   )
            );
    auto Results = match(matcher, *S, Context);

    if (Results.empty()) {
      llvm::errs() << "function or variable reference not found\n";
      S->dump();
      return TaintLattice::untainted();
    }
    const BoundNodes &Nodes = Results[0];
    if (const auto *func =
                   Nodes.getNodeAs<clang::FunctionDecl>("func")) {
      llvm::errs() << "func found\n";
      S->dump();
      if (func->getName() == "getchar"){ // taintsource
        llvm::errs()<<"Returning tainted";
        return TaintLattice::tainted();
      }
      else if (func->getName() == "sanitize") // sanitize function
        return TaintLattice::untainted();
    } else if (const auto *rhsVar = Nodes.getNodeAs<clang::VarDecl>("var")) {
      assert(rhsVar);
      auto It = Vars.find(rhsVar);
      if (It != Vars.end())
        return It->second;
    } else
      return TaintLattice::untainted();
  }

  void transfer(const Stmt *S, TaintPropagationLattice &Vars, Environment &Env) {
    llvm::errs()<<"Transfer function called\n";
    S->dump();
    auto matcher = stmt(
        anyOf(declStmt(hasSingleDecl(
                  varDecl(decl().bind("lhsVar"),
                          optionally(hasInitializer(expr().bind("rhsExpr"))))
                      .bind(kDecl))),
              binaryOperator(isAssignmentOperator(), hasLHS(refToVar("lhsVar")),
                             hasRHS(expr().bind("rhsExpr")))
                  .bind("binop"),
              binaryOperator(hasOperatorName("="), hasLHS(refToVar("lhsVar")),
                             hasRHS(expr().bind("rhsExpr")))
                  .bind("binop")
              )
      );

    ASTContext &Context = getASTContext();
    auto Results = match(matcher, *S, Context);
    if (Results.empty())
      return;
    const BoundNodes &Nodes = Results[0];

    const auto *Var = Nodes.getNodeAs<clang::VarDecl>("lhsVar");
    assert(Var != nullptr);
    const auto *RHSExpr = Nodes.getNodeAs<clang::Expr>("rhsExpr");

    if(!RHSExpr){
      llvm::errs()<<"no rhs expression\n";
      Vars[Var] = TaintLattice::bottom();//uninitialized vars are bottom
    } else {
      llvm::errs()<<"RHSEXPR\n";
      RHSExpr->dump();
      Vars[Var] = evaluateTaintExpr(RHSExpr, Vars);
      llvm::errs()<<"taintedness assigned\n";
    }
  }
};

using ::testing::IsEmpty;
using ::testing::Pair;
using ::testing::UnorderedElementsAre;

MATCHER_P(Var, name,
          (llvm::Twine(negation ? "isn't" : "is") + " a variable named `" +
           name + "`")
              .str()) {
  assert(isa<VarDecl>(arg));
  return arg->getName() == name;
}

MATCHER(Bottom, "") { return arg == arg.bottom(); }
MATCHER(Untainted, "") { return arg == arg.untainted(); }
MATCHER(Tainted, "") { return arg == arg.tainted(); }
MATCHER(Top, "") { return arg == arg.top(); }

MATCHER_P(HoldsTaintLattice, m,
          ((negation ? "doesn't hold" : "holds") +
           llvm::StringRef(" a lattice element that ") +
           ::testing::DescribeMatcher<TaintPropagationLattice>(m, negation))
              .str()) {
  return ExplainMatchResult(m, arg.Lattice, result_listener);
}

template <typename Matcher>
void RunDataflow(llvm::StringRef Code, Matcher Expectations) {
  ASSERT_THAT_ERROR(
      test::checkDataflow<TaintPropagationAnalysis>(
          Code, "fun",
          [](ASTContext &C, Environment &) {
            return TaintPropagationAnalysis(C);
          },
          [&Expectations](
              llvm::ArrayRef<std::pair<
                  std::string,
                  DataflowAnalysisState<TaintPropagationAnalysis::Lattice>>>
                  Results,
              ASTContext &) { EXPECT_THAT(Results, Expectations); },
          {"-fsyntax-only", "-std=c++17"}),
      llvm::Succeeded());
}


TEST(TaintAnalysisTest, Init) {
  std::string Code = R"(
    typedef unsigned long size_t;
    int getchar();
    void *malloc(size_t size);

    void fun() {
      size_t ts;
      size_t uninit;
      size_t clean=5;
      ts=getchar();
      int *ptr = (int*) malloc(ts * sizeof(int));
      // [[p]]
    }
  )";
  RunDataflow(Code, UnorderedElementsAre(
                        Pair("p", HoldsTaintLattice(UnorderedElementsAre(
                                      Pair(Var("ts"), Tainted()),
                                      Pair(Var("uninit"), Bottom()),
                                      Pair(Var("clean"), Untainted()),
                                      Pair(Var("ptr"), Tainted())
                                      )))));
}


TEST(TaintAnalysisTest, merge) {
  std::string Code = R"(
    int getchar();

    void fun(bool b) {
      int a;
      int ts;
      a = 5;
      if (b){
        ts = getchar();
        //[[p0]]
        }
      else{
        ts= 5;
        //[[p1]]
      }
      (void)0;
      // [[p]]
    }
  )";
  RunDataflow(Code, UnorderedElementsAre(
                        Pair("p0", HoldsTaintLattice(UnorderedElementsAre(
                                      Pair(Var("a"), Untainted())
                                      ,Pair(Var("ts"), Tainted())
                                      ))),
                        Pair("p1", HoldsTaintLattice(UnorderedElementsAre(
                                      Pair(Var("a"), Untainted())
                                      ,Pair(Var("ts"), Untainted())
                                      ))),
                        Pair("p", HoldsTaintLattice(UnorderedElementsAre(
                                      Pair(Var("a"), Untainted())
                                      ,Pair(Var("ts"), Top())
                                      )))));
}

/*
TEST(SignAnalysisTest, Init) {
  std::string Code = R"(
    void fun() {
      int neg = -1;
      int zero = 0;
      int pos = 1;
      int uninited;
      // [[p]]
    }
  )";
  RunDataflow(Code, UnorderedElementsAre(
                        Pair("p", HoldsTaintLattice(UnorderedElementsAre(
                                      Pair(Var("neg"), Negative()),
                                      Pair(Var("zero"), Zero()),
                                      Pair(Var("pos"), Positive()),
                                      Pair(Var("uninited"), Top()))))));
}

TEST(SignAnalysisTest, Assignment) {
  std::string Code = R"(
    void fun() {
      int neg, zero, pos;
      neg = -1;
      zero = 0;
      pos = 1;
      // [[p]]
    }
  )";
  RunDataflow(Code, UnorderedElementsAre(
                        Pair("p", HoldsTaintLattice(UnorderedElementsAre(
                                      Pair(Var("neg"), Negative()),
                                      Pair(Var("zero"), Zero()),
                                      Pair(Var("pos"), Positive()))))));
}

TEST(SignAnalysisTest, InitToBottom) {
  std::string Code = R"(
    int foo();
    void fun() {
      int a = foo();
      // [[p]]
    }
  )";
  RunDataflow(Code, UnorderedElementsAre(
                        Pair("p", HoldsTaintLattice(UnorderedElementsAre(
                                      Pair(Var("a"), Bottom()))))));
}

TEST(SignAnalysisTest, AssignmentAfterBottom) {
  std::string Code = R"(
    int foo();
    void fun(bool b) {
      int a = foo();
      a = -1;
      // [[p]]
    }
  )";
  RunDataflow(Code, UnorderedElementsAre(
                        Pair("p", HoldsTaintLattice(UnorderedElementsAre(
                                      Pair(Var("a"), Negative()))))));
}

TEST(SignAnalysisTest, GreaterThan) {
  std::string Code = R"(
    int foo();
    void fun() {
      int a = foo();
      if (a > 0) {
        (void)0;
        // [[p]]
      }
      if (a > -1) {
        (void)0;
        // [[q]]
      }
    }
  )";
  RunDataflow(Code, UnorderedElementsAre(
                        Pair("p", HoldsTaintLattice(UnorderedElementsAre(
                                      Pair(Var("a"), Positive())))),
                        Pair("q", HoldsTaintLattice(UnorderedElementsAre(
                                      Pair(Var("a"), Top()))))));
}

TEST(SignAnalysisTest, GreaterThanIfElse) {
  std::string Code = R"(
    void fun(int a) {
      if (a > 0) {
        (void)1;
        // [[p]]
      } else {
        (void)0;
        // [[q]]
      }
    }
  )";
  RunDataflow(Code, UnorderedElementsAre(
                        Pair("p", HoldsTaintLattice(UnorderedElementsAre(
                                      Pair(Var("a"), Positive())))),
                        Pair("q", HoldsTaintLattice(UnorderedElementsAre(
                                      Pair(Var("a"), Top()))))));
}

TEST(SignAnalysisTest, LessThan) {
  std::string Code = R"(
    int foo();
    void fun() {
      int a = foo();
      if (a < 0) {
        (void)0;
        // [[p]]
      }
      if (a < 1) {
        (void)0;
        // [[q]]
      }
    }
  )";
  RunDataflow(Code, UnorderedElementsAre(
                        Pair("p", HoldsTaintLattice(UnorderedElementsAre(
                                      Pair(Var("a"), Negative())))),
                        Pair("q", HoldsTaintLattice(UnorderedElementsAre(
                                      Pair(Var("a"), Top()))))));
}

TEST(SignAnalysisTest, LessThanIfElse) {
  std::string Code = R"(
    void fun(int a) {
      if (a < 0) {
        (void)1;
        // [[p]]
      } else {
        (void)0;
        // [[q]]
      }
    }
  )";
  RunDataflow(Code, UnorderedElementsAre(
                        Pair("p", HoldsTaintLattice(UnorderedElementsAre(
                                      Pair(Var("a"), Negative())))),
                        Pair("q", HoldsTaintLattice(UnorderedElementsAre(
                                      Pair(Var("a"), Top()))))));
}

TEST(SignAnalysisTest, Equality) {
  std::string Code = R"(
    int foo();
    void fun() {
      int a = foo();
      if (a == -1) {
        (void)0;
        // [[n]]
      }
      if (a == 0) {
        (void)0;
        // [[z]]
      }
      if (a == 1) {
        (void)0;
        // [[p]]
      }
    }
  )";
  RunDataflow(Code, UnorderedElementsAre(
                        Pair("n", HoldsTaintLattice(UnorderedElementsAre(
                                      Pair(Var("a"), Negative())))),
                        Pair("z", HoldsTaintLattice(UnorderedElementsAre(
                                      Pair(Var("a"), Zero())))),
                        Pair("p", HoldsTaintLattice(UnorderedElementsAre(
                                      Pair(Var("a"), Positive()))))));
}

TEST(SignAnalysisTest, SymbolicAssignment) {
  std::string Code = R"(
    int foo();
    void fun() {
      int a = foo();
      int b = foo();
      if (a < 0) {
        b = a;
        (void)0;
        // [[p]]
      }
    }
  )";
  RunDataflow(Code, UnorderedElementsAre(
                        Pair("p", HoldsTaintLattice(UnorderedElementsAre(
                                      Pair(Var("a"), Negative()),
                                      Pair(Var("b"), Negative()))))));
}

TEST(SignAnalysisTest, JoinToTop) {
  std::string Code = R"(
    int foo();
    void fun(bool b) {
      int a = foo();
      if (b) {
        a = -1;
        (void)0;
        // [[p]]
      } else {
        a = 1;
        (void)0;
        // [[q]]
      }
      (void)0;
      // [[r]]
    }
  )";
  RunDataflow(Code, UnorderedElementsAre(
                        Pair("p", HoldsTaintLattice(UnorderedElementsAre(
                                      Pair(Var("a"), Negative())))),
                        Pair("q", HoldsTaintLattice(UnorderedElementsAre(
                                      Pair(Var("a"), Positive())))),
                        Pair("r", HoldsTaintLattice(UnorderedElementsAre(
                                      Pair(Var("a"), Top()))))));
}

TEST(SignAnalysisTest, JoinToNeg) {
  std::string Code = R"(
    int foo();
    void fun() {
      int a = foo();
      if (a < 1) {
        a = -1;
        (void)0;
        // [[p]]
      } else {
        a = -1;
        (void)0;
        // [[q]]
      }
      (void)0;
      // [[r]]
    }
  )";
  RunDataflow(Code, UnorderedElementsAre(
                        Pair("p", HoldsTaintLattice(UnorderedElementsAre(
                                      Pair(Var("a"), Negative())))),
                        Pair("q", HoldsTaintLattice(UnorderedElementsAre(
                                      Pair(Var("a"), Negative())))),
                        Pair("r", HoldsTaintLattice(UnorderedElementsAre(
                                      Pair(Var("a"), Negative()))))));
}

TEST(SignAnalysisTest, NestedIfs) {
  std::string Code = R"(
    int foo();
    void fun() {
      int a = foo();
      if (a >= 0) {
        (void)0;
        // [[p]]
        if (a == 0) {
          (void)0;
          // [[q]]
        }
      }
      (void)0;
      // [[r]]
    }
  )";
  RunDataflow(
      Code,
      UnorderedElementsAre(
          Pair("p",
               HoldsTaintLattice(UnorderedElementsAre(Pair(Var("a"), Top())))),
          Pair("q",
               HoldsTaintLattice(UnorderedElementsAre(Pair(Var("a"), Zero())))),
          Pair("r",
               HoldsTaintLattice(UnorderedElementsAre(Pair(Var("a"), Top()))))));
}
*/
} // namespace
} // namespace dataflow
} // namespace clang