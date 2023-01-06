//== GenericTaintChecker.cpp ----------------------------------- -*- C++ -*--=//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This checker defines the attack surface for generic taint propagation.
//
// The taint information produced by it might be useful to other checkers. For
// example, checkers should report errors which involve tainted data more
// aggressively, even if the involved symbols are under constrained.
//
//===----------------------------------------------------------------------===//

#include "Yaml.h"
#include "clang/AST/Attr.h"
#include "clang/Basic/Builtins.h"
#include "clang/StaticAnalyzer/Checkers/BuiltinCheckerRegistration.h"
#include "clang/StaticAnalyzer/Checkers/Taint.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallDescription.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ExplodedGraph.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramStateTrait.h"

#include "llvm/Support/YAMLTraits.h"

#include <limits>
#include <memory>
#include <optional>
#include <utility>

#define DEBUG_TYPE "taint-checker"

using namespace clang;
using namespace ento;
using namespace taint;

using llvm::ImmutableSet;

namespace {

class GenericTaintChecker;

/// Check for CWE-134: Uncontrolled Format String.
constexpr llvm::StringLiteral MsgUncontrolledFormatString =
    "Untrusted data is used as a format string "
    "(CWE-134: Uncontrolled Format String)";

/// Check for:
/// CERT/STR02-C. "Sanitize data passed to complex subsystems"
/// CWE-78, "Failure to Sanitize Data into an OS Command"
constexpr llvm::StringLiteral MsgSanitizeSystemArgs =
    "Untrusted data is passed to a system call "
    "(CERT/STR02-C. Sanitize data passed to complex subsystems)";

/// Check if tainted data is used as a buffer size in strn.. functions,
/// and allocators.
constexpr llvm::StringLiteral MsgTaintedBufferSize =
    "Untrusted data is used to specify the buffer size "
    "(CERT/STR31-C. Guarantee that storage for strings has sufficient space "
    "for character data and the null terminator)";

/// Check if tainted data is used as a custom sink's parameter.
constexpr llvm::StringLiteral MsgCustomSink =
    "Untrusted data is passed to a user-defined sink";

using ArgIdxTy = int;
using ArgVecTy = llvm::SmallVector<ArgIdxTy, 2>;

/// In this structure we follow the spread of the taint flows through
/// the function arguments.
struct ArgIdxFlowTy {
  ArgIdxTy ArgIdx;
  int FlowId;
  ArgIdxFlowTy(ArgIdxTy i) : ArgIdx(i), FlowId(UninitializedFlow){};
  ArgIdxFlowTy(ArgIdxTy i, int f) : ArgIdx(i), FlowId(f){};
  bool operator==(const ArgIdxFlowTy &X) const {
    return FlowId == X.FlowId && ArgIdx == X.ArgIdx;
  }
  int operator<(const ArgIdxFlowTy &X) const {
    return FlowId < X.FlowId && ArgIdx < X.ArgIdx;
  }
  void Profile(llvm::FoldingSetNodeID &ID) const {
    ID.AddInteger(FlowId);
    ID.AddInteger(ArgIdx);
  }
};

/// Denotes the return value.
constexpr ArgIdxTy ReturnValueIndex{-1};

static ArgIdxTy fromArgumentCount(unsigned Count) {
  assert(Count <=
             static_cast<std::size_t>(std::numeric_limits<ArgIdxTy>::max()) &&
         "ArgIdxTy is not large enough to represent the number of arguments.");
  return Count;
}

/// Given a pointer, return the SVal of its pointee or if it is tainted,
/// otherwise return the pointer's SVal if tainted.
/// Also considers stdin as a taint source.
std::optional<SVal> getTaintedPointeeOrPointer(const CheckerContext &C,
                                               SVal Arg) {
  const ProgramStateRef State = C.getState();

  if (auto Pointee = getPointeeOf(C, Arg))
    if (isTainted(State, *Pointee)) // FIXME: isTainted(...) ? Pointee : None;
      return Pointee;

  if (isTainted(State, Arg))
    return Arg;

  // FIXME: This should be done by the isTainted() API.
  if (isStdin(Arg, C.getASTContext()))
    return Arg;

  return std::nullopt;
}

bool isTaintedOrPointsToTainted(const Expr *E, const ProgramStateRef &State,
                                CheckerContext &C) {
  return getTaintedPointeeOrPointer(C, C.getSVal(E)).has_value();
}

/// ArgSet is used to describe arguments relevant for taint detection or
/// taint application. A discrete set of argument indexes and a variadic
/// argument list signified by a starting index are supported.
class ArgSet {
public:
  ArgSet() = default;
  ArgSet(ArgVecTy &&DiscreteArgs,
         std::optional<ArgIdxTy> VariadicIndex = std::nullopt)
      : DiscreteArgs(std::move(DiscreteArgs)),
        VariadicIndex(std::move(VariadicIndex)) {}

  bool contains(ArgIdxTy ArgIdx) const {
    if (llvm::is_contained(DiscreteArgs, ArgIdx))
      return true;

    return VariadicIndex && ArgIdx >= *VariadicIndex;
  }

  bool isEmpty() const { return DiscreteArgs.empty() && !VariadicIndex; }

private:
  ArgVecTy DiscreteArgs;
  std::optional<ArgIdxTy> VariadicIndex;
};

const NoteTag *createTaintOriginTag(CheckerContext &C, int FlowId) {
  LLVM_DEBUG(llvm::dbgs() << "New taint flow. Flow id: " << FlowId << '\n';);
  const NoteTag *InjectionTag =
      C.getNoteTag([&C, FlowId](PathSensitiveBugReport &BR) -> std::string {
        SmallString<256> Msg;
        llvm::raw_svector_ostream Out(Msg);
        // Only make this note when the report is taint related and the flow
        // id of the origin matches with the flow id of the sink.
        // We are not using "interestingess" for this as it is not
        // propagating the same way as taintedness property.
        if (TaintBugReport *TBR = dyn_cast_or_null<TaintBugReport>(&BR))
          if (TBR->taint_data.Flow == FlowId) {
            LLVM_DEBUG(llvm::dbgs() << "Taint originated here. Flow id: "
                                    << std::to_string(FlowId) << "\n");
            Out << "Taint originated here";
          }
        return std::string(Out.str());
      });
  return InjectionTag;
}

/// A struct used to specify taint propagation rules for a function.
///
/// If any of the possible taint source arguments is tainted, all of the
/// destination arguments should also be tainted. If ReturnValueIndex is added
/// to the dst list, the return value will be tainted.
class GenericTaintRule {
  /// Arguments which are taints sinks and should be checked, and a report
  /// should be emitted if taint reaches these.
  ArgSet SinkArgs;
  /// Arguments which should be sanitized on function return.
  ArgSet FilterArgs;
  /// Arguments which can participate in taint propagation. If any of the
  /// arguments in PropSrcArgs is tainted, all arguments in  PropDstArgs should
  /// be tainted.
  ArgSet PropSrcArgs;
  ArgSet PropDstArgs;

  /// A message that explains why the call is sensitive to taint.
  std::optional<StringRef> SinkMsg;

  GenericTaintRule() = default;

  GenericTaintRule(ArgSet &&Sink, ArgSet &&Filter, ArgSet &&Src, ArgSet &&Dst,
                   std::optional<StringRef> SinkMsg = std::nullopt)
      : SinkArgs(std::move(Sink)), FilterArgs(std::move(Filter)),
        PropSrcArgs(std::move(Src)), PropDstArgs(std::move(Dst)),
        SinkMsg(SinkMsg) {}

public:
  /// Make a rule that reports a warning if taint reaches any of \p FilterArgs
  /// arguments.
  static GenericTaintRule Sink(ArgSet &&SinkArgs,
                               std::optional<StringRef> Msg = std::nullopt) {
    return {std::move(SinkArgs), {}, {}, {}, Msg};
  }

  /// Make a rule that sanitizes all FilterArgs arguments.
  static GenericTaintRule Filter(ArgSet &&FilterArgs) {
    return {{}, std::move(FilterArgs), {}, {}};
  }

  /// Make a rule that unconditionally taints all Args.
  /// If Func is provided, it must also return true for taint to propagate.
  static GenericTaintRule Source(ArgSet &&SourceArgs) {
    return {{}, {}, {}, std::move(SourceArgs)};
  }

  /// Make a rule that taints all PropDstArgs if any of PropSrcArgs is tainted.
  static GenericTaintRule Prop(ArgSet &&SrcArgs, ArgSet &&DstArgs) {
    return {{}, {}, std::move(SrcArgs), std::move(DstArgs)};
  }

  /// Make a rule that taints all PropDstArgs if any of PropSrcArgs is tainted.
  static GenericTaintRule
  SinkProp(ArgSet &&SinkArgs, ArgSet &&SrcArgs, ArgSet &&DstArgs,
           std::optional<StringRef> Msg = std::nullopt) {
    return {
        std::move(SinkArgs), {}, std::move(SrcArgs), std::move(DstArgs), Msg};
  }

  /// Process a function which could either be a taint source, a taint sink, a
  /// taint filter or a taint propagator.
  void process(const GenericTaintChecker &Checker, const CallEvent &Call,
               CheckerContext &C) const;

  /// Handles the resolution of indexes of type ArgIdxTy to Expr*-s.
  static const Expr *GetArgExpr(ArgIdxTy ArgIdx, const CallEvent &Call) {
    return ArgIdx == ReturnValueIndex ? Call.getOriginExpr()
                                      : Call.getArgExpr(ArgIdx);
  };

  /// Functions for custom taintedness propagation.
  static bool UntrustedEnv(CheckerContext &C);
};

using RuleLookupTy = CallDescriptionMap<GenericTaintRule>;

/// Used to parse the configuration file.
struct TaintConfiguration {
  using NameScopeArgs = std::tuple<std::string, std::string, ArgVecTy>;
  enum class VariadicType { None, Src, Dst };

  struct Common {
    std::string Name;
    std::string Scope;
  };

  struct Sink : Common {
    ArgVecTy SinkArgs;
  };

  struct Filter : Common {
    ArgVecTy FilterArgs;
  };

  struct Propagation : Common {
    ArgVecTy SrcArgs;
    ArgVecTy DstArgs;
    VariadicType VarType;
    ArgIdxTy VarIndex;
  };

  std::vector<Propagation> Propagations;
  std::vector<Filter> Filters;
  std::vector<Sink> Sinks;

  TaintConfiguration() = default;
  TaintConfiguration(const TaintConfiguration &) = default;
  TaintConfiguration(TaintConfiguration &&) = default;
  TaintConfiguration &operator=(const TaintConfiguration &) = default;
  TaintConfiguration &operator=(TaintConfiguration &&) = default;
};

struct GenericTaintRuleParser {
  GenericTaintRuleParser(CheckerManager &Mgr) : Mgr(Mgr) {}
  /// Container type used to gather call identification objects grouped into
  /// pairs with their corresponding taint rules. It is temporary as it is used
  /// to finally initialize RuleLookupTy, which is considered to be immutable.
  using RulesContTy = std::vector<std::pair<CallDescription, GenericTaintRule>>;
  RulesContTy parseConfiguration(const std::string &Option,
                                 TaintConfiguration &&Config) const;

private:
  using NamePartsTy = llvm::SmallVector<StringRef, 2>;

  /// Validate part of the configuration, which contains a list of argument
  /// indexes.
  void validateArgVector(const std::string &Option, const ArgVecTy &Args) const;

  template <typename Config> static NamePartsTy parseNameParts(const Config &C);

  // Takes the config and creates a CallDescription for it and associates a Rule
  // with that.
  template <typename Config>
  static void consumeRulesFromConfig(const Config &C, GenericTaintRule &&Rule,
                                     RulesContTy &Rules);

  void parseConfig(const std::string &Option, TaintConfiguration::Sink &&P,
                   RulesContTy &Rules) const;
  void parseConfig(const std::string &Option, TaintConfiguration::Filter &&P,
                   RulesContTy &Rules) const;
  void parseConfig(const std::string &Option,
                   TaintConfiguration::Propagation &&P,
                   RulesContTy &Rules) const;

  CheckerManager &Mgr;
};

class GenericTaintChecker : public Checker<check::PreCall, check::PostCall> {
public:
  void checkPreCall(const CallEvent &Call, CheckerContext &C) const;
  void checkPostCall(const CallEvent &Call, CheckerContext &C) const;
  void printState(raw_ostream &Out, ProgramStateRef State, const char *NL,
                  const char *Sep) const override;

  /// Generate a report if the expression is tainted or points to tainted data.
  bool generateReportIfTainted(const Expr *E, StringRef Msg,
                               CheckerContext &C) const;

  static TaintFlowType generateNewTaintFlow() { return FlowIdCount++; }

private:
  /// A unique counter for each taint flow.
  /// We must increase this whenever the analysis hits a new taint source.
  static TaintFlowType FlowIdCount;
  const BugType BT{this, "Use of Untrusted Data", categories::TaintedData};

  bool checkUncontrolledFormatString(const CallEvent &Call,
                                     CheckerContext &C) const;

  void taintUnsafeSocketProtocol(const CallEvent &Call,
                                 CheckerContext &C) const;

  /// Default taint rules are initilized with the help of a CheckerContext to
  /// access the names of built-in functions like memcpy.
  void initTaintRules(CheckerContext &C) const;

  /// CallDescription currently cannot restrict matches to the global namespace
  /// only, which is why multiple CallDescriptionMaps are used, as we want to
  /// disambiguate global C functions from functions inside user-defined
  /// namespaces.
  // TODO: Remove separation to simplify matching logic once CallDescriptions
  // are more expressive.

  mutable std::optional<RuleLookupTy> StaticTaintRules;
  mutable std::optional<RuleLookupTy> DynamicTaintRules;
};
TaintFlowType GenericTaintChecker::FlowIdCount = 0;

} // end of anonymous namespace

/// YAML serialization mapping.
LLVM_YAML_IS_SEQUENCE_VECTOR(TaintConfiguration::Sink)
LLVM_YAML_IS_SEQUENCE_VECTOR(TaintConfiguration::Filter)
LLVM_YAML_IS_SEQUENCE_VECTOR(TaintConfiguration::Propagation)

namespace llvm {
namespace yaml {
template <> struct MappingTraits<TaintConfiguration> {
  static void mapping(IO &IO, TaintConfiguration &Config) {
    IO.mapOptional("Propagations", Config.Propagations);
    IO.mapOptional("Filters", Config.Filters);
    IO.mapOptional("Sinks", Config.Sinks);
  }
};

template <> struct MappingTraits<TaintConfiguration::Sink> {
  static void mapping(IO &IO, TaintConfiguration::Sink &Sink) {
    IO.mapRequired("Name", Sink.Name);
    IO.mapOptional("Scope", Sink.Scope);
    IO.mapRequired("Args", Sink.SinkArgs);
  }
};

template <> struct MappingTraits<TaintConfiguration::Filter> {
  static void mapping(IO &IO, TaintConfiguration::Filter &Filter) {
    IO.mapRequired("Name", Filter.Name);
    IO.mapOptional("Scope", Filter.Scope);
    IO.mapRequired("Args", Filter.FilterArgs);
  }
};

template <> struct MappingTraits<TaintConfiguration::Propagation> {
  static void mapping(IO &IO, TaintConfiguration::Propagation &Propagation) {
    IO.mapRequired("Name", Propagation.Name);
    IO.mapOptional("Scope", Propagation.Scope);
    IO.mapOptional("SrcArgs", Propagation.SrcArgs);
    IO.mapOptional("DstArgs", Propagation.DstArgs);
    IO.mapOptional("VariadicType", Propagation.VarType);
    IO.mapOptional("VariadicIndex", Propagation.VarIndex);
  }
};

template <> struct ScalarEnumerationTraits<TaintConfiguration::VariadicType> {
  static void enumeration(IO &IO, TaintConfiguration::VariadicType &Value) {
    IO.enumCase(Value, "None", TaintConfiguration::VariadicType::None);
    IO.enumCase(Value, "Src", TaintConfiguration::VariadicType::Src);
    IO.enumCase(Value, "Dst", TaintConfiguration::VariadicType::Dst);
  }
};
} // namespace yaml
} // namespace llvm

/// A set which is used to pass information from call pre-visit instruction
/// to the call post-visit. The values are signed integers, which are either
/// ReturnValueIndex, or indexes of the pointer/reference argument, which
/// points to data, which should be tainted on return.
REGISTER_MAP_WITH_PROGRAMSTATE(TaintArgsOnPostVisit, const LocationContext *,
                               ImmutableSet<ArgIdxFlowTy>)
REGISTER_SET_FACTORY_WITH_PROGRAMSTATE(ArgIdxFactory, ArgIdxFlowTy)

void GenericTaintRuleParser::validateArgVector(const std::string &Option,
                                               const ArgVecTy &Args) const {
  for (ArgIdxTy Arg : Args) {
    if (Arg < ReturnValueIndex) {
      Mgr.reportInvalidCheckerOptionValue(
          Mgr.getChecker<GenericTaintChecker>(), Option,
          "an argument number for propagation rules greater or equal to -1");
    }
  }
}

template <typename Config>
GenericTaintRuleParser::NamePartsTy
GenericTaintRuleParser::parseNameParts(const Config &C) {
  NamePartsTy NameParts;
  if (!C.Scope.empty()) {
    // If the Scope argument contains multiple "::" parts, those are considered
    // namespace identifiers.
    StringRef{C.Scope}.split(NameParts, "::", /*MaxSplit*/ -1,
                             /*KeepEmpty*/ false);
  }
  NameParts.emplace_back(C.Name);
  return NameParts;
}

template <typename Config>
void GenericTaintRuleParser::consumeRulesFromConfig(const Config &C,
                                                    GenericTaintRule &&Rule,
                                                    RulesContTy &Rules) {
  NamePartsTy NameParts = parseNameParts(C);
  Rules.emplace_back(CallDescription(NameParts), std::move(Rule));
}

void GenericTaintRuleParser::parseConfig(const std::string &Option,
                                         TaintConfiguration::Sink &&S,
                                         RulesContTy &Rules) const {
  validateArgVector(Option, S.SinkArgs);
  consumeRulesFromConfig(S, GenericTaintRule::Sink(std::move(S.SinkArgs)),
                         Rules);
}

void GenericTaintRuleParser::parseConfig(const std::string &Option,
                                         TaintConfiguration::Filter &&S,
                                         RulesContTy &Rules) const {
  validateArgVector(Option, S.FilterArgs);
  consumeRulesFromConfig(S, GenericTaintRule::Filter(std::move(S.FilterArgs)),
                         Rules);
}

void GenericTaintRuleParser::parseConfig(const std::string &Option,
                                         TaintConfiguration::Propagation &&P,
                                         RulesContTy &Rules) const {
  validateArgVector(Option, P.SrcArgs);
  validateArgVector(Option, P.DstArgs);
  bool IsSrcVariadic = P.VarType == TaintConfiguration::VariadicType::Src;
  bool IsDstVariadic = P.VarType == TaintConfiguration::VariadicType::Dst;
  std::optional<ArgIdxTy> JustVarIndex = P.VarIndex;

  ArgSet SrcDesc(std::move(P.SrcArgs),
                 IsSrcVariadic ? JustVarIndex : std::nullopt);
  ArgSet DstDesc(std::move(P.DstArgs),
                 IsDstVariadic ? JustVarIndex : std::nullopt);

  consumeRulesFromConfig(
      P, GenericTaintRule::Prop(std::move(SrcDesc), std::move(DstDesc)), Rules);
}

GenericTaintRuleParser::RulesContTy
GenericTaintRuleParser::parseConfiguration(const std::string &Option,
                                           TaintConfiguration &&Config) const {

  RulesContTy Rules;

  for (auto &F : Config.Filters)
    parseConfig(Option, std::move(F), Rules);

  for (auto &S : Config.Sinks)
    parseConfig(Option, std::move(S), Rules);

  for (auto &P : Config.Propagations)
    parseConfig(Option, std::move(P), Rules);

  return Rules;
}

void GenericTaintChecker::initTaintRules(CheckerContext &C) const {
  // Check for exact name match for functions without builtin substitutes.
  // Use qualified name, because these are C functions without namespace.

  if (StaticTaintRules || DynamicTaintRules)
    return;

  using RulesConstructionTy =
      std::vector<std::pair<CallDescription, GenericTaintRule>>;
  using TR = GenericTaintRule;

  const Builtin::Context &BI = C.getASTContext().BuiltinInfo;

  RulesConstructionTy GlobalCRules{
      // Sources
      {{{"fdopen"}}, TR::Source({{ReturnValueIndex}})},
      {{{"fopen"}}, TR::Source({{ReturnValueIndex}})},
      {{{"freopen"}}, TR::Source({{ReturnValueIndex}})},
      {{{"getch"}}, TR::Source({{ReturnValueIndex}})},
      {{{"getchar"}}, TR::Source({{ReturnValueIndex}})},
      {{{"getchar_unlocked"}}, TR::Source({{ReturnValueIndex}})},
      {{{"gets"}}, TR::Source({{0}, ReturnValueIndex})},
      {{{"gets_s"}}, TR::Source({{0}, ReturnValueIndex})},
      {{{"scanf"}}, TR::Source({{}, 1})},
      {{{"scanf_s"}}, TR::Source({{}, {1}})},
      {{{"wgetch"}}, TR::Source({{}, ReturnValueIndex})},
      // Sometimes the line between taint sources and propagators is blurry.
      // _IO_getc is choosen to be a source, but could also be a propagator.
      // This way it is simpler, as modeling it as a propagator would require
      // to model the possible sources of _IO_FILE * values, which the _IO_getc
      // function takes as parameters.
      {{{"_IO_getc"}}, TR::Source({{ReturnValueIndex}})},
      {{{"getcwd"}}, TR::Source({{0, ReturnValueIndex}})},
      {{{"getwd"}}, TR::Source({{0, ReturnValueIndex}})},
      {{{"readlink"}}, TR::Source({{1, ReturnValueIndex}})},
      {{{"readlinkat"}}, TR::Source({{2, ReturnValueIndex}})},
      {{{"get_current_dir_name"}}, TR::Source({{ReturnValueIndex}})},
      {{{"gethostname"}}, TR::Source({{0}})},
      {{{"getnameinfo"}}, TR::Source({{2, 4}})},
      {{{"getseuserbyname"}}, TR::Source({{1, 2}})},
      {{{"getgroups"}}, TR::Source({{1, ReturnValueIndex}})},
      {{{"getlogin"}}, TR::Source({{ReturnValueIndex}})},
      {{{"getlogin_r"}}, TR::Source({{0}})},

      // Props
      {{{"atoi"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"atol"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"atoll"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"fgetc"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"fgetln"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"fgets"}}, TR::Prop({{2}}, {{0, ReturnValueIndex}})},
      {{{"fscanf"}}, TR::Prop({{0}}, {{}, 2})},
      {{{"fscanf_s"}}, TR::Prop({{0}}, {{}, {2}})},
      {{{"sscanf"}}, TR::Prop({{0}}, {{}, 2})},

      {{{"getc"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"getc_unlocked"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"getdelim"}}, TR::Prop({{3}}, {{0}})},
      {{{"getline"}}, TR::Prop({{2}}, {{0}})},
      {{{"getw"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"pread"}}, TR::Prop({{0, 1, 2, 3}}, {{1, ReturnValueIndex}})},
      {{{"read"}}, TR::Prop({{0, 2}}, {{1, ReturnValueIndex}})},
      {{{"strchr"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"strrchr"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"tolower"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"toupper"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"fread"}}, TR::Prop({{3}}, {{0, ReturnValueIndex}})},
      {{{"recv"}}, TR::Prop({{0}}, {{1, ReturnValueIndex}})},
      {{{"recvfrom"}}, TR::Prop({{0}}, {{1, ReturnValueIndex}})},

      {{{"ttyname"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"ttyname_r"}}, TR::Prop({{0}}, {{1, ReturnValueIndex}})},

      {{{"basename"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"dirname"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"fnmatch"}}, TR::Prop({{1}}, {{ReturnValueIndex}})},
      {{{"memchr"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"memrchr"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"rawmemchr"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},

      {{{"mbtowc"}}, TR::Prop({{1}}, {{0, ReturnValueIndex}})},
      {{{"wctomb"}}, TR::Prop({{1}}, {{0, ReturnValueIndex}})},
      {{{"wcwidth"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},

      {{{"memcmp"}}, TR::Prop({{0, 1}}, {{ReturnValueIndex}})},
      {{{"memcpy"}}, TR::Prop({{1}}, {{0, ReturnValueIndex}})},
      {{{"memmove"}}, TR::Prop({{1}}, {{0, ReturnValueIndex}})},
      // If memmem was called with a tainted needle and the search was
      // successful, that would mean that the value pointed by the return value
      // has the same content as the needle. If we choose to go by the policy of
      // content equivalence implies taintedness equivalence, that would mean
      // haystack should be considered a propagation source argument.
      {{{"memmem"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},

      // The comment for memmem above also applies to strstr.
      {{{"strstr"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"strcasestr"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},

      {{{"strchrnul"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},

      {{{"index"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"rindex"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},

      // FIXME: In case of arrays, only the first element of the array gets
      // tainted.
      {{{"qsort"}}, TR::Prop({{0}}, {{0}})},
      {{{"qsort_r"}}, TR::Prop({{0}}, {{0}})},

      {{{"strcmp"}}, TR::Prop({{0, 1}}, {{ReturnValueIndex}})},
      {{{"strcasecmp"}}, TR::Prop({{0, 1}}, {{ReturnValueIndex}})},
      {{{"strncmp"}}, TR::Prop({{0, 1, 2}}, {{ReturnValueIndex}})},
      {{{"strncasecmp"}}, TR::Prop({{0, 1, 2}}, {{ReturnValueIndex}})},
      {{{"strspn"}}, TR::Prop({{0, 1}}, {{ReturnValueIndex}})},
      {{{"strcspn"}}, TR::Prop({{0, 1}}, {{ReturnValueIndex}})},
      {{{"strpbrk"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"strndup"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"strndupa"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"strlen"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"strnlen"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"strtol"}}, TR::Prop({{0}}, {{1, ReturnValueIndex}})},
      {{{"strtoll"}}, TR::Prop({{0}}, {{1, ReturnValueIndex}})},
      {{{"strtoul"}}, TR::Prop({{0}}, {{1, ReturnValueIndex}})},
      {{{"strtoull"}}, TR::Prop({{0}}, {{1, ReturnValueIndex}})},

      {{{"isalnum"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"isalpha"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"isascii"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"isblank"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"iscntrl"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"isdigit"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"isgraph"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"islower"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"isprint"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"ispunct"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"isspace"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"isupper"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{{"isxdigit"}}, TR::Prop({{0}}, {{ReturnValueIndex}})},

      {{CDF_MaybeBuiltin, {BI.getName(Builtin::BIstrncat)}},
       TR::Prop({{1, 2}}, {{0, ReturnValueIndex}})},
      {{CDF_MaybeBuiltin, {BI.getName(Builtin::BIstrlcpy)}},
       TR::Prop({{1, 2}}, {{0}})},
      {{CDF_MaybeBuiltin, {BI.getName(Builtin::BIstrlcat)}},
       TR::Prop({{1, 2}}, {{0}})},
      {{CDF_MaybeBuiltin, {{"snprintf"}}},
       TR::Prop({{1}, 3}, {{0, ReturnValueIndex}})},
      {{CDF_MaybeBuiltin, {{"sprintf"}}},
       TR::Prop({{1}, 2}, {{0, ReturnValueIndex}})},
      {{CDF_MaybeBuiltin, {{"strcpy"}}},
       TR::Prop({{1}}, {{0, ReturnValueIndex}})},
      {{CDF_MaybeBuiltin, {{"stpcpy"}}},
       TR::Prop({{1}}, {{0, ReturnValueIndex}})},
      {{CDF_MaybeBuiltin, {{"strcat"}}},
       TR::Prop({{1}}, {{0, ReturnValueIndex}})},
      {{CDF_MaybeBuiltin, {{"strdup"}}}, TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{CDF_MaybeBuiltin, {{"strdupa"}}},
       TR::Prop({{0}}, {{ReturnValueIndex}})},
      {{CDF_MaybeBuiltin, {{"wcsdup"}}}, TR::Prop({{0}}, {{ReturnValueIndex}})},

      // Sinks
      {{{"system"}}, TR::Sink({{0}}, MsgSanitizeSystemArgs)},
      {{{"popen"}}, TR::Sink({{0}}, MsgSanitizeSystemArgs)},
      {{{"execl"}}, TR::Sink({{0}}, MsgSanitizeSystemArgs)},
      {{{"execle"}}, TR::Sink({{0}}, MsgSanitizeSystemArgs)},
      {{{"execlp"}}, TR::Sink({{0}}, MsgSanitizeSystemArgs)},
      {{{"execvp"}}, TR::Sink({{0}}, MsgSanitizeSystemArgs)},
      {{{"execvP"}}, TR::Sink({{0}}, MsgSanitizeSystemArgs)},
      {{{"execve"}}, TR::Sink({{0}}, MsgSanitizeSystemArgs)},
      {{{"dlopen"}}, TR::Sink({{0}}, MsgSanitizeSystemArgs)},
      {{CDF_MaybeBuiltin, {{"malloc"}}}, TR::Sink({{0}}, MsgTaintedBufferSize)},
      {{CDF_MaybeBuiltin, {{"calloc"}}}, TR::Sink({{0}}, MsgTaintedBufferSize)},
      {{CDF_MaybeBuiltin, {{"alloca"}}}, TR::Sink({{0}}, MsgTaintedBufferSize)},
      {{CDF_MaybeBuiltin, {{"memccpy"}}},
       TR::Sink({{3}}, MsgTaintedBufferSize)},
      {{CDF_MaybeBuiltin, {{"realloc"}}},
       TR::Sink({{1}}, MsgTaintedBufferSize)},
      {{{{"setproctitle"}}}, TR::Sink({{0}, 1}, MsgUncontrolledFormatString)},
      {{{{"setproctitle_fast"}}},
       TR::Sink({{0}, 1}, MsgUncontrolledFormatString)},

      // SinkProps
      {{CDF_MaybeBuiltin, BI.getName(Builtin::BImemcpy)},
       TR::SinkProp({{2}}, {{1, 2}}, {{0, ReturnValueIndex}},
                    MsgTaintedBufferSize)},
      {{CDF_MaybeBuiltin, {BI.getName(Builtin::BImemmove)}},
       TR::SinkProp({{2}}, {{1, 2}}, {{0, ReturnValueIndex}},
                    MsgTaintedBufferSize)},
      {{CDF_MaybeBuiltin, {BI.getName(Builtin::BIstrncpy)}},
       TR::SinkProp({{2}}, {{1, 2}}, {{0, ReturnValueIndex}},
                    MsgTaintedBufferSize)},
      {{CDF_MaybeBuiltin, {BI.getName(Builtin::BIstrndup)}},
       TR::SinkProp({{1}}, {{0, 1}}, {{ReturnValueIndex}},
                    MsgTaintedBufferSize)},
      {{CDF_MaybeBuiltin, {{"bcopy"}}},
       TR::SinkProp({{2}}, {{0, 2}}, {{1}}, MsgTaintedBufferSize)}};

  // `getenv` returns taint only in untrusted environments.
  if (TR::UntrustedEnv(C)) {
    // void setproctitle_init(int argc, char *argv[], char *envp[])
    GlobalCRules.push_back(
        {{{"setproctitle_init"}}, TR::Sink({{1, 2}}, MsgCustomSink)});
    GlobalCRules.push_back({{{"getenv"}}, TR::Source({{ReturnValueIndex}})});
  }

  StaticTaintRules.emplace(std::make_move_iterator(GlobalCRules.begin()),
                           std::make_move_iterator(GlobalCRules.end()));

  // User-provided taint configuration.
  CheckerManager *Mgr = C.getAnalysisManager().getCheckerManager();
  assert(Mgr);
  GenericTaintRuleParser ConfigParser{*Mgr};
  std::string Option{"Config"};
  StringRef ConfigFile =
      Mgr->getAnalyzerOptions().getCheckerStringOption(this, Option);
  std::optional<TaintConfiguration> Config =
      getConfiguration<TaintConfiguration>(*Mgr, this, Option, ConfigFile);
  if (!Config) {
    // We don't have external taint config, no parsing required.
    DynamicTaintRules = RuleLookupTy{};
    return;
  }

  GenericTaintRuleParser::RulesContTy Rules{
      ConfigParser.parseConfiguration(Option, std::move(*Config))};

  DynamicTaintRules.emplace(std::make_move_iterator(Rules.begin()),
                            std::make_move_iterator(Rules.end()));
}

void GenericTaintChecker::checkPreCall(const CallEvent &Call,
                                       CheckerContext &C) const {
  initTaintRules(C);

  // FIXME: this should be much simpler.
  if (const auto *Rule =
          Call.isGlobalCFunction() ? StaticTaintRules->lookup(Call) : nullptr)
    Rule->process(*this, Call, C);
  else if (const auto *Rule = DynamicTaintRules->lookup(Call))
    Rule->process(*this, Call, C);

  // FIXME: These edge cases are to be eliminated from here eventually.
  //
  // Additional check that is not supported by CallDescription.
  // TODO: Make CallDescription be able to match attributes such as printf-like
  // arguments.
  checkUncontrolledFormatString(Call, C);

  // TODO: Modeling sockets should be done in a specific checker.
  // Socket is a source, which taints the return value.
  taintUnsafeSocketProtocol(Call, C);
}

void GenericTaintChecker::checkPostCall(const CallEvent &Call,
                                        CheckerContext &C) const {
  // Set the marked values as tainted. The return value only accessible from
  // checkPostStmt.
  ProgramStateRef State = C.getState();
  const StackFrameContext *CurrentFrame = C.getStackFrame();

  // Depending on what was tainted at pre-visit, we determined a set of
  // arguments which should be tainted after the function returns. These are
  // stored in the state as TaintArgsOnPostVisit set.
  TaintArgsOnPostVisitTy TaintArgsMap = State->get<TaintArgsOnPostVisit>();

  const ImmutableSet<ArgIdxFlowTy> *TaintArgs =
      TaintArgsMap.lookup(CurrentFrame);
  if (!TaintArgs)
    return;
  assert(!TaintArgs->isEmpty());

  LLVM_DEBUG(for (ArgIdxFlowTy I
                  : *TaintArgs) {
    llvm::dbgs() << "PostCall<";
    Call.dump(llvm::dbgs());
    llvm::dbgs() << "> actually wants to taint arg index: " << I.ArgIdx
                 << " Flow Id: " << I.FlowId << "\n";
  });

  for (ArgIdxFlowTy ArgNum : *TaintArgs) {
    // Special handling for the tainted return value.
    if (ArgNum.ArgIdx == ReturnValueIndex) {
      State = addTaint(State, Call.getReturnValue(), ArgNum.FlowId);
      continue;
    }

    // The arguments are pointer arguments. The data they are pointing at is
    // tainted after the call.
    if (auto V = getPointeeOf(C, Call.getArgSVal(ArgNum.ArgIdx))) {
      State = addTaint(State, *V, ArgNum.FlowId);
    }
  }

  // Clear up the taint info from the state.
  State = State->remove<TaintArgsOnPostVisit>(CurrentFrame);
  C.addTransition(State);
}

void GenericTaintChecker::printState(raw_ostream &Out, ProgramStateRef State,
                                     const char *NL, const char *Sep) const {
  printTaint(State, Out, NL, Sep);
}

void GenericTaintRule::process(const GenericTaintChecker &Checker,
                               const CallEvent &Call, CheckerContext &C) const {
  ProgramStateRef State = C.getState();
  const ArgIdxTy CallNumArgs = fromArgumentCount(Call.getNumArgs());

  /// Iterate every call argument, and get their corresponding Expr and SVal.
  const auto ForEachCallArg = [&C, &Call, CallNumArgs](auto &&Fun) {
    for (ArgIdxTy I = ReturnValueIndex; I < CallNumArgs; ++I) {
      const Expr *E = GetArgExpr(I, Call);
      Fun(I, E, C.getSVal(E));
    }
  };

  /// Check for taint sinks.
  ForEachCallArg([this, &Checker, &C, &State](ArgIdxTy I, const Expr *E, SVal) {
    if (SinkArgs.contains(I) && isTaintedOrPointsToTainted(E, State, C)) {
      LLVM_DEBUG(llvm::dbgs()
                     << "Potential Injection vulnerability detected. Flow id: "
                     << getTaintDataPointeeOrPointer(C, C.getSVal(E))->Flow
                     << '\n';);
      Checker.generateReportIfTainted(E, SinkMsg.value_or(MsgCustomSink), C);
    }
  });

  /// Check for taint filters.
  ForEachCallArg([this, &C, &State](ArgIdxTy I, const Expr *E, SVal S) {
    if (FilterArgs.contains(I)) {
      State = removeTaint(State, S);
      if (auto P = getPointeeOf(C, S))
        State = removeTaint(State, *P);
    }
  });

  /// Check for taint propagation sources.
  /// A rule is relevant if PropSrcArgs is empty, or if any of its signified
  /// args are tainted in context of the current CallEvent.
  bool IsMatching = PropSrcArgs.isEmpty();
  TaintFlowType TaintFlowId = UninitializedFlow;

  const NoteTag *InjectionTag = nullptr;
  if (PropSrcArgs.isEmpty() && !PropDstArgs.isEmpty()) {
    // The attacker injects the taint value here
    // We place here a noteTag and assign a new Flow id.
    TaintFlowId = GenericTaintChecker::generateNewTaintFlow();
    InjectionTag = createTaintOriginTag(C, TaintFlowId);
  }

  ForEachCallArg([this, &C, &IsMatching, &State, &TaintFlowId,
                  &InjectionTag](ArgIdxTy I, const Expr *E, SVal) mutable {
    IsMatching = IsMatching || (PropSrcArgs.contains(I) &&
                                isTaintedOrPointsToTainted(E, State, C));
    if (TaintFlowId == UninitializedFlow) {
      if (isStdin(C.getSVal(E), C.getASTContext())) {
        // Reading from stdin. Creating a new flow
        TaintFlowId = GenericTaintChecker::generateNewTaintFlow();
        InjectionTag = createTaintOriginTag(C, TaintFlowId);
      } else if (getTaintDataPointeeOrPointer(C, C.getSVal(E)).has_value()) {
        // Propagating an existing Flow Id
        TaintFlowId = getTaintDataPointeeOrPointer(C, C.getSVal(E))->Flow;
      }
    }
  });

  if (!IsMatching)
    return;

  const auto WouldEscape = [](SVal V, QualType Ty) -> bool {
    if (!isa<Loc>(V))
      return false;

    const bool IsNonConstRef = Ty->isReferenceType() && !Ty.isConstQualified();
    const bool IsNonConstPtr =
        Ty->isPointerType() && !Ty->getPointeeType().isConstQualified();

    return IsNonConstRef || IsNonConstPtr;
  };

  /// Propagate taint where it is necessary.
  auto &F = State->getStateManager().get_context<ArgIdxFactory>();
  ImmutableSet<ArgIdxFlowTy> Result = F.getEmptySet();
  ForEachCallArg([&](ArgIdxTy I, const Expr *E, SVal V) {
    if (PropDstArgs.contains(I)) {
      LLVM_DEBUG(llvm::dbgs() << "PreCall<"; Call.dump(llvm::dbgs());
                 llvm::dbgs() << "> prepares tainting arg index: " << I
                              << " Flow Id: " << TaintFlowId << '\n';);
      ArgIdxFlowTy Flow(I, TaintFlowId);
      Result = F.add(Result, Flow);
    }

    // TODO: We should traverse all reachable memory regions via the
    // escaping parameter. Instead of doing that we simply mark only the
    // referred memory region as tainted.
    if (WouldEscape(V, E->getType())) {
      LLVM_DEBUG(if (!Result.contains(I)) {
        llvm::dbgs() << "PreCall<";
        Call.dump(llvm::dbgs());
        llvm::dbgs() << "> prepares tainting arg index: " << I
                     << " Flow Id: " << TaintFlowId << '\n';
      });
      ArgIdxFlowTy Flow(I, TaintFlowId);
      Result = F.add(Result, Flow);
    }
  });

  if (!Result.isEmpty())
    State = State->set<TaintArgsOnPostVisit>(C.getStackFrame(), Result);
  C.addTransition(State, InjectionTag);
}

bool GenericTaintRule::UntrustedEnv(CheckerContext &C) {
  return !C.getAnalysisManager()
              .getAnalyzerOptions()
              .ShouldAssumeControlledEnvironment;
}

bool GenericTaintChecker::generateReportIfTainted(const Expr *E, StringRef Msg,
                                                  CheckerContext &C) const {
  assert(E);
  std::optional<TaintData> TD = getTaintDataPointeeOrPointer(C, C.getSVal(E));

  if (!TD) {
    return false;
  }
  // Generate diagnostic.
  if (ExplodedNode *N = C.generateNonFatalErrorNode()) {
    auto report = std::make_unique<TaintBugReport>(BT, Msg, N, *TD);
    C.emitReport(std::move(report));
    return true;
  }
  return false;
}

/// TODO: remove checking for printf format attributes and socket whitelisting
/// from GenericTaintChecker, and that means the following functions:
/// getPrintfFormatArgumentNum,
/// GenericTaintChecker::checkUncontrolledFormatString,
/// GenericTaintChecker::taintUnsafeSocketProtocol

static bool getPrintfFormatArgumentNum(const CallEvent &Call,
                                       const CheckerContext &C,
                                       ArgIdxTy &ArgNum) {
  // Find if the function contains a format string argument.
  // Handles: fprintf, printf, sprintf, snprintf, vfprintf, vprintf, vsprintf,
  // vsnprintf, syslog, custom annotated functions.
  const Decl *CallDecl = Call.getDecl();
  if (!CallDecl)
    return false;
  const FunctionDecl *FDecl = CallDecl->getAsFunction();
  if (!FDecl)
    return false;

  const ArgIdxTy CallNumArgs = fromArgumentCount(Call.getNumArgs());

  for (const auto *Format : FDecl->specific_attrs<FormatAttr>()) {
    ArgNum = Format->getFormatIdx() - 1;
    if ((Format->getType()->getName() == "printf") && CallNumArgs > ArgNum)
      return true;
  }

  return false;
}

bool GenericTaintChecker::checkUncontrolledFormatString(
    const CallEvent &Call, CheckerContext &C) const {
  // Check if the function contains a format string argument.
  ArgIdxTy ArgNum = 0;
  if (!getPrintfFormatArgumentNum(Call, C, ArgNum))
    return false;

  // If either the format string content or the pointer itself are tainted,
  // warn.
  return generateReportIfTainted(Call.getArgExpr(ArgNum),
                                 MsgUncontrolledFormatString, C);
}

void GenericTaintChecker::taintUnsafeSocketProtocol(const CallEvent &Call,
                                                    CheckerContext &C) const {
  if (Call.getNumArgs() < 1)
    return;
  const IdentifierInfo *ID = Call.getCalleeIdentifier();
  if (!ID)
    return;
  if (!ID->getName().equals("socket"))
    return;

  SourceLocation DomLoc = Call.getArgExpr(0)->getExprLoc();
  StringRef DomName = C.getMacroNameOrSpelling(DomLoc);
  // Allow internal communication protocols.
  bool SafeProtocol = DomName.equals("AF_SYSTEM") ||
                      DomName.equals("AF_LOCAL") || DomName.equals("AF_UNIX") ||
                      DomName.equals("AF_RESERVED_36");
  if (SafeProtocol)
    return;

  ProgramStateRef State = C.getState();
  auto &F = State->getStateManager().get_context<ArgIdxFactory>();
  ImmutableSet<ArgIdxFlowTy> Result =
      F.add(F.getEmptySet(), ArgIdxFlowTy(ReturnValueIndex));
  State = State->set<TaintArgsOnPostVisit>(C.getStackFrame(), Result);
  C.addTransition(State);
}

/// Checker registration
void ento::registerGenericTaintChecker(CheckerManager &Mgr) {
  Mgr.registerChecker<GenericTaintChecker>();
}

bool ento::shouldRegisterGenericTaintChecker(const CheckerManager &mgr) {
  return true;
}
