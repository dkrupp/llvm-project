# Clang-Tidy Check Specification: `bugprone-unsafe-format-string`

## Overview
Detects usage of vulnerable format string functions with unbounded `%s` specifiers that can cause buffer overflows.

## Check Name
`bugprone-unsafe-format-string`

## Description
Warns when format string functions without built-in buffer limits use `%s` specifier without field width restrictions.

## Targeted Functions
```cpp
// Output functions
sprintf, vsprintf

// Input functions  
scanf, fscanf, sscanf, vscanf, vfscanf, vsscanf

// Wide character functions
wscanf, fwscanf, swscanf, vwscanf, vfwscanf, vswscanf
```

## Detection Logic
1. Match calls to vulnerable functions
2. Extract format string (literal or traceable constant)
3. Parse format string for `%s` specifiers
4. Flag `%s` without field width (e.g., `%10s` is safe, `%s` is not)

## Examples

**Unsafe (triggers warning):**
```cpp
char buf[100];
sprintf(buf, "Hello %s", name);           // Warning
scanf("%s", buffer);                      // Warning
sscanf(input, "%s %d", str, &num);       // Warning
```

**Safe (no warning):**
```cpp
char buf[100];
snprintf(buf, sizeof(buf), "Hello %s", name);  // Safe alternative
sprintf(buf, "Hello %.99s", name);             // Field width specified
scanf("%99s", buffer);                         // Field width specified
```

## Diagnostic Message
```
warning: format specifier '%s' without field width may cause buffer overflow [bugprone-unsafe-format-string]
```

## Fix-It Hints
- Suggest `snprintf()` for `sprintf()`
- Suggest field width for `%s` specifiers
- Provide buffer size calculation when possible

## Implementation Notes
- Handle both string literals and const char* format parameters
- Support variadic and va_list variants
- Consider format string concatenation patterns
- Integrate with existing `bugprone` module
