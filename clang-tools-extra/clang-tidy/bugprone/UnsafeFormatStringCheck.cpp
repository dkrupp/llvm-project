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
#include "llvm/Support/ConvertUTF.h"
#include "llvm/Support/raw_ostream.h"

using namespace clang::ast_matchers;

namespace clang::tidy::bugprone {

UnsafeFormatStringCheck::UnsafeFormatStringCheck(StringRef Name,
                                                 ClangTidyContext *Context)
    : ClangTidyCheck(Name, Context) {}

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

  std::string FormatString;
  if (Format->getCharByteWidth() == 1) {
    FormatString = Format->getString().str();
  } else if (Format->getCharByteWidth() == 2) {
    // Handle wide strings by converting to narrow string for analysis
    convertUTF16ToUTF8String(Format->getBytes(), FormatString);
  } else if (Format->getCharByteWidth() == 4) {
    // Handle wide strings by converting to narrow string for analysis
    convertUTF32ToUTF8String(Format->getBytes(), FormatString);
  }

  const auto *Callee = cast<FunctionDecl>(Call->getCalleeDecl());
  StringRef FunctionName = Callee->getName();
  
  bool IsScanfFamily = FunctionName.contains("scanf");
  
  if (!hasUnboundedStringSpecifier(FormatString, IsScanfFamily))
    return;

  auto Diag = diag(Call->getBeginLoc(),
                   IsScanfFamily 
                     ? "format specifier '%%s' without field width may cause buffer overflow; consider using '%%Ns' where N limits input length"
                     : "format specifier '%%s' without precision may cause buffer overflow; consider using '%%.Ns' where N limits output length")
              << Call->getSourceRange();

  std::string SafeAlternative = getSafeAlternative(FunctionName);
  if (!SafeAlternative.empty()) {
    Diag << FixItHint::CreateInsertion(Call->getBeginLoc(),
                                       "/* Consider using " + SafeAlternative + " */ ");
  }
}


bool UnsafeFormatStringCheck::hasUnboundedStringSpecifier(StringRef FormatString, bool IsScanfFamily) {
  size_t Pos = 0;
  while ((Pos = FormatString.find('%', Pos)) != StringRef::npos) {
    if (Pos + 1 >= FormatString.size())
      break;

    // Skip %%
    if (FormatString[Pos + 1] == '%') {
      Pos += 2;
      continue;
    }

    size_t SpecPos = Pos + 1;

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

    // Check for precision
    bool HasPrecision = false;
    if (SpecPos < FormatString.size() && FormatString[SpecPos] == '.') {
      SpecPos++;
      if (SpecPos < FormatString.size() && FormatString[SpecPos] == '*') {
        HasPrecision = true;
        SpecPos++;
      } else {
        while (SpecPos < FormatString.size() && isdigit(FormatString[SpecPos])) {
          HasPrecision = true;
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

    // Check for 's' specifier
    if (SpecPos < FormatString.size() && FormatString[SpecPos] == 's') {
      if (IsScanfFamily) {
        // For scanf family, field width provides protection
        if (!HasFieldWidth) {
          return true;
        }
      } else {
        // For sprintf family, only precision provides protection
        if (!HasPrecision) {
          return true;
        }
      }
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
