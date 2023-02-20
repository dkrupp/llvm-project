// RUN: %clang_cc1 -analyze -analyzer-checker=alpha.security.taint,core,alpha.security.ArrayBoundV2 -analyzer-output=text -verify %s

// This file is for testing enhanced diagnostics produced by the GenericTaintChecker

typedef unsigned long size_t;
struct _IO_FILE;
typedef struct _IO_FILE FILE;

int scanf(const char *restrict format, ...);
int system(const char *command);
char* getenv( const char* env_var );
size_t strlen( const char* str );
void *malloc(size_t size );
char *fgets(char *str, int n, FILE *stream);
FILE *stdin;

void taintDiagnostic(void)
{
  char buf[128];
  scanf("%s", buf); // expected-note {{Taint originated here}}
  system(buf); // expected-warning {{Untrusted data is passed to a system call}} // expected-note {{Untrusted data is passed to a system call (CERT/STR02-C. Sanitize data passed to complex subsystems)}}
}

int taintDiagnosticOutOfBound(void) {
  int index;
  int Array[] = {1, 2, 3, 4, 5};
  scanf("%d", &index); // expected-note {{Taint originated here}}
  return Array[index]; // expected-warning {{Out of bound memory access (index is tainted)}}
                       // expected-note@-1 {{Out of bound memory access (index is tainted)}}
}

int taintDiagnosticDivZero(int operand) {
  scanf("%d", &operand); // expected-note {{Value assigned to 'operand'}}
                         // expected-note@-1 {{Taint originated here}}
  return 10 / operand; // expected-warning {{Division by a tainted value, possibly zero}}
                       // expected-note@-1 {{Division by a tainted value, possibly zero}}
}

void taintDiagnosticVLA(void) {
  int x;
  scanf("%d", &x); // expected-note {{Value assigned to 'x'}}
                   // expected-note@-1 {{Taint originated here}}
  int vla[x]; // expected-warning {{Declared variable-length array (VLA) has tainted size}}
              // expected-note@-1 {{Declared variable-length array (VLA) has tainted size}}
}

//Tests if the originated note is correctly placed even if the path is
//propagating through variables and expressions
char* taintDiagnosticPropagation(){
  char *pathbuf;
  char *pathlist=getenv("PATH"); // expected-note {{Taint originated here}}
  if (pathlist){ // expected-note {{Assuming 'pathlist' is non-null}}
	               // expected-note@-1 {{Taking true branch}}
    pathbuf=(char*) malloc(strlen(pathlist)+1); // expected-warning{{Untrusted data is used to specify the buffer size}}
                                                // expected-note@-1{{Untrusted data is used to specify the buffer size}}
    return pathbuf;
  }
  return 0;
}


//Taint origin should be marked correctly even if there are multiple taint
//sources in the function
char* taintDiagnosticPropagation2(){
  char *pathbuf;
  char *user_env2=getenv("USER_ENV_VAR2");//unrelated taint source
  char *pathlist=getenv("PATH"); // expected-note {{Taint originated here}}
  char *user_env=getenv("USER_ENV_VAR");//unrelated taint source
  if (pathlist){ // expected-note {{Assuming 'pathlist' is non-null}}
	               // expected-note@-1 {{Taking true branch}}
    pathbuf=(char*) malloc(strlen(pathlist)+1); // expected-warning{{Untrusted data is used to specify the buffer size}}
                                                // expected-note@-1{{Untrusted data is used to specify the buffer size}}
    return pathbuf;
  }
  return 0;
}

void testReadStdIn(){
  char buf[1024];
  fgets(buf, sizeof(buf), stdin);// expected-note {{Taint originated here}}
  system(buf);// expected-warning {{Untrusted data is passed to a system call}} // expected-note {{Untrusted data is passed to a system call (CERT/STR02-C. Sanitize data passed to complex subsystems)}}

}
