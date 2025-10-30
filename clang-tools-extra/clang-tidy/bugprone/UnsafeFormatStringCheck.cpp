//===--- UnsafeFormatStringCheck.cpp - clang-tidy -----------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "UnsafeFormatStringCheck.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/Lex/Lexer.h"

using namespace clang::ast_matchers;

namespace clang::tidy::bugprone {

UnsafeFormatStringCheck::UnsafeFormatStringCheck(StringRef Name,
                                                 ClangTidyContext *Context)
    : ClangTidyCheck(Name, Context),
      MaxFieldWidth(Options.get("MaxFieldWidth", 4096U)),
      SuggestAlternatives(Options.get("SuggestAlternatives", true)) {}

void UnsafeFormatStringCheck::registerMatchers(MatchFinder *Finder) {
  // Match vulnerable format string functions
  auto VulnerableFunctions = hasAnyName(
      "sprintf", "vsprintf", "scanf", "fscanf", "sscanf", "vscanf", "vfscanf",
      "vsscanf", "wscanf", "fwscanf", "swscanf", "vwscanf", "vfwscanf", "vswscanf");

  Finder->addMatcher(
      callExpr(callee(functionDecl(VulnerableFunctions)),
               anyOf(hasArgument(0, stringLiteral().bind("format")),
                     hasArgument(1, stringLiteral().bind("format"))))
          .bind("call"),
      this);
}

void UnsafeFormatStringCheck::check(const MatchFinder::MatchResult &Result) {
  const auto *Call = Result.Nodes.getNodeAs<CallExpr>("call");
  const auto *Format = Result.Nodes.getNodeAs<StringLiteral>("format");
  
  if (!Call || !Format)
    return;

  StringRef FormatString = Format->getString();
  if (!hasUnboundedStringSpecifier(FormatString))
    return;

  const auto *Callee = cast<FunctionDecl>(Call->getCalleeDecl());
  StringRef FunctionName = Callee->getName();

  auto Diag = diag(Call->getBeginLoc(),
                   "format specifier '%%s' without field width may cause "
                   "buffer overflow")
              << Call->getSourceRange();

  if (SuggestAlternatives) {
    std::string SafeAlternative = getSafeAlternative(FunctionName);
    if (!SafeAlternative.empty()) {
      Diag << FixItHint::CreateInsertion(Call->getBeginLoc(),
                                         "/* Consider using " + SafeAlternative + " */ ");
    }
  }
}

void UnsafeFormatStringCheck::storeOptions(ClangTidyOptions::OptionMap &Opts) {
  Options.store(Opts, "MaxFieldWidth", MaxFieldWidth);
  Options.store(Opts, "SuggestAlternatives", SuggestAlternatives);
}

bool UnsafeFormatStringCheck::hasUnboundedStringSpecifier(StringRef FormatString) {
  size_t Pos = 0;
  while ((Pos = FormatString.find('%', Pos)) != StringRef::npos) {
    if (Pos + 1 >= FormatString.size())
      break;
    
    // Skip %%
    if (FormatString[Pos + 1] == '%') {
      Pos += 2;
      continue;
    }
    
    size_t SpecStart = Pos + 1;
    size_t SpecPos = SpecStart;
    
    // Skip flags
    while (SpecPos < FormatString.size() && 
           (FormatString[SpecPos] == '-' || FormatString[SpecPos] == '+' ||
            FormatString[SpecPos] == ' ' || FormatString[SpecPos] == '#' ||
            FormatString[SpecPos] == '0')) {
      SpecPos++;
    }
    
    // Check for field width
    bool HasFieldWidth = false;
    if (SpecPos < FormatString.size() && FormatString[SpecPos] == '*') {
      HasFieldWidth = true;
      SpecPos++;
    } else {
      while (SpecPos < FormatString.size() && isdigit(FormatString[SpecPos])) {
        HasFieldWidth = true;
        SpecPos++;
      }
    }
    
    // Skip precision
    if (SpecPos < FormatString.size() && FormatString[SpecPos] == '.') {
      SpecPos++;
      if (SpecPos < FormatString.size() && FormatString[SpecPos] == '*') {
        SpecPos++;
      } else {
        while (SpecPos < FormatString.size() && isdigit(FormatString[SpecPos])) {
          SpecPos++;
        }
      }
    }
    
    // Skip length modifiers
    while (SpecPos < FormatString.size() && 
           (FormatString[SpecPos] == 'h' || FormatString[SpecPos] == 'l' ||
            FormatString[SpecPos] == 'L' || FormatString[SpecPos] == 'z' ||
            FormatString[SpecPos] == 'j' || FormatString[SpecPos] == 't')) {
      SpecPos++;
    }
    
    // Check for 's' specifier without field width
    if (SpecPos < FormatString.size() && FormatString[SpecPos] == 's' && !HasFieldWidth) {
      return true;
    }
    
    Pos = SpecPos + 1;
  }
  
  return false;
}

std::string UnsafeFormatStringCheck::getSafeAlternative(StringRef FunctionName) {
  if (FunctionName == "sprintf")
    return "snprintf";
  if (FunctionName == "vsprintf")
    return "vsnprintf";
  if (FunctionName.starts_with("scanf") || FunctionName.ends_with("scanf"))
    return "add field width to %s specifiers";
  return "";
}

} // namespace clang::tidy::bugprone
