// RUN: %check_clang_tidy %s bugprone-unsafe-format-string %t

#include <stdio.h>
#include <wchar.h>
#include <stdarg.h>

void test_sprintf() {
  char buffer[100];
  const char* input = "user input";
  
  /* Positive: unsafe %s without field width */
  sprintf(buffer, "%s", input);
  // CHECK-MESSAGES: :[[@LINE-1]]:3: warning: format specifier '%s' without field width may cause buffer overflow [bugprone-unsafe-format-string]
  
  /* Negative: safe %s with field width */
  sprintf(buffer, "%99s", input);
  /* no-warning */
  
  /* Negative: other format specifiers are safe */
  sprintf(buffer, "%d %f", 42, 3.14);
  /* no-warning */
}

void test_vsprintf() {
  char buffer[100];
  va_list args;
  
  /* Positive: unsafe %s without field width */
  vsprintf(buffer, "%s", args);
  // CHECK-MESSAGES: :[[@LINE-1]]:3: warning: format specifier '%s' without field width may cause buffer overflow [bugprone-unsafe-format-string]
}

void test_vsprintf_safe_wrapper(const char* format, ...) {
  char buffer[100];
  va_list args;
  va_start(args, format);
  
  /* Negative: vsnprintf is safe */
  vsnprintf(buffer, sizeof(buffer), format, args);
  /* no-warning */
  
  va_end(args);
}

void test_scanf() {
  char buffer[100];
  
  /* Positive: unsafe %s without field width */
  scanf("%s", buffer);
  // CHECK-MESSAGES: :[[@LINE-1]]:3: warning: format specifier '%s' without field width may cause buffer overflow [bugprone-unsafe-format-string]
  
  /* Negative: safe %s with field width */
  scanf("%99s", buffer);
  /* no-warning */
}

void test_fscanf() {
  char buffer[100];
  FILE* file = 0;
  
  /* Positive: unsafe %s without field width */
  fscanf(file, "%s", buffer);
  // CHECK-MESSAGES: :[[@LINE-1]]:3: warning: format specifier '%s' without field width may cause buffer overflow [bugprone-unsafe-format-string]
  
  /* Negative: safe %s with field width */
  fscanf(file, "%99s", buffer);
  /* no-warning */
}

void test_sscanf() {
  char buffer[100];
  const char* source = "input";
  
  /* Positive: unsafe %s without field width */
  sscanf(source, "%s", buffer);
  // CHECK-MESSAGES: :[[@LINE-1]]:3: warning: format specifier '%s' without field width may cause buffer overflow [bugprone-unsafe-format-string]
  
  /* Negative: safe %s with field width */
  sscanf(source, "%99s", buffer);
  /* no-warning */
}

void test_vfscanf() {
  FILE* file = 0;
  va_list args;
  
  /* Positive: unsafe %s without field width */
  vfscanf(file, "%s", args);
  // CHECK-MESSAGES: :[[@LINE-1]]:3: warning: format specifier '%s' without field width may cause buffer overflow [bugprone-unsafe-format-string]
}

void test_vsscanf() {
  const char* source = "input";
  va_list args;
  
  /* Positive: unsafe %s without field width */
  vsscanf(source, "%s", args);
  // CHECK-MESSAGES: :[[@LINE-1]]:3: warning: format specifier '%s' without field width may cause buffer overflow [bugprone-unsafe-format-string]
}

void test_vscanf() {
  va_list args;
  
  /* Positive: unsafe %s without field width */
  vscanf("%s", args);
  // CHECK-MESSAGES: :[[@LINE-1]]:3: warning: format specifier '%s' without field width may cause buffer overflow [bugprone-unsafe-format-string]
}

void test_wscanf() {
  wchar_t buffer[100];
  
  /* Positive: unsafe %s without field width */
  wscanf(L"%s", buffer);
  // CHECK-MESSAGES: :[[@LINE-1]]:3: warning: format specifier '%s' without field width may cause buffer overflow [bugprone-unsafe-format-string]
  
  /* Negative: safe %s with field width */
  wscanf(L"%99s", buffer);
  /* no-warning */
}

void test_fwscanf() {
  wchar_t buffer[100];
  FILE* file = 0;
  
  /* Positive: unsafe %s without field width */
  fwscanf(file, L"%s", buffer);
  // CHECK-MESSAGES: :[[@LINE-1]]:3: warning: format specifier '%s' without field width may cause buffer overflow [bugprone-unsafe-format-string]
  
  /* Negative: safe %s with field width */
  fwscanf(file, L"%99s", buffer);
  /* no-warning */
}

void test_swscanf() {
  wchar_t buffer[100];
  const wchar_t* source = L"input";
  
  /* Positive: unsafe %s without field width */
  swscanf(source, L"%s", buffer);
  // CHECK-MESSAGES: :[[@LINE-1]]:3: warning: format specifier '%s' without field width may cause buffer overflow [bugprone-unsafe-format-string]
  
  /* Negative: safe %s with field width */
  swscanf(source, L"%99s", buffer);
  /* no-warning */
}

void test_vwscanf() {
  va_list args;
  
  /* Positive: unsafe %s without field width */
  vwscanf(L"%s", args);
  // CHECK-MESSAGES: :[[@LINE-1]]:3: warning: format specifier '%s' without field width may cause buffer overflow [bugprone-unsafe-format-string]
}

void test_vfwscanf() {
  FILE* file = 0;
  va_list args;
  
  /* Positive: unsafe %s without field width */
  vfwscanf(file, L"%s", args);
  // CHECK-MESSAGES: :[[@LINE-1]]:3: warning: format specifier '%s' without field width may cause buffer overflow [bugprone-unsafe-format-string]
}

void test_vswscanf() {
  const wchar_t* source = L"input";
  va_list args;
  
  /* Positive: unsafe %s without field width */
  vswscanf(source, L"%s", args);
  // CHECK-MESSAGES: :[[@LINE-1]]:3: warning: format specifier '%s' without field width may cause buffer overflow [bugprone-unsafe-format-string]
}

void test_safe_alternatives() {
  char buffer[100];
  const char* input = "user input";
  
  /* Negative: snprintf is inherently safe */
  snprintf(buffer, sizeof(buffer), "%s", input);
  /* no-warning */
  
  /* Negative: printf family doesn't write to buffers */
  printf("%s", input);
  /* no-warning */
  
  /* Negative: fprintf doesn't write to user buffers */
  fprintf(stderr, "%s", input);
  /* no-warning */
}
