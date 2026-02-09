// RUN: %clang_cc1 -analyze -analyzer-checker=optin.taint,core,alpha.security.ArrayBoundV2,optin.taint.TaintedAlloc -analyzer-checker=debug.ExprInspection \
// RUN: -analyzer-config optin.taint.TaintPropagation:TaintPropagationMode=spread -analyzer-output=text -verify %s

// This file is for testing enhanced diagnostics produced by the GenericTaintChecker

typedef __typeof(sizeof(int)) size_t;
struct _IO_FILE;
typedef struct _IO_FILE FILE;

int scanf(const char *restrict format, ...);
int system(const char *command);
char* getenv( const char* env_var );
size_t strlen( const char* str );
char *strcat( char *dest, const char *src );
char* strcpy( char* dest, const char* src );
void *malloc(size_t size );
void free( void *ptr );
char *fgets(char *str, int n, FILE *stream);
char *strncat( char *dest, const char *src, unsigned long count);
extern FILE *stdin;


void clang_analyzer_isTainted_ptr(void *);
void clang_analyzer_isTainted(int);
void clang_analyzer_isTainted_any_suffix(char);
void clang_analyzer_isTainted_many_arguments(char, int, int);

// Tests if the diagnostics are properly printed
// along the taint propagation dataflow in spread propagation mode

// Calling an external unkown function before the sink.
// With spread propagation filename_transformed should be
// tainted too.

void unknownTransformInOut(char* in, char* out);

void fetchTaintedString(char *txt){
  scanf("%s", txt);// expected-note{{Taint originated here}}
                   // expected-note@-1{{Taint propagated to the 2nd argument}}
}

void test_unknown_transform2(int input){
  char cmd[2048] = "/bin/cat ";
  char filename[1024];
  char filename_transformed[1024];
  fetchTaintedString (filename); // expected-note{{Calling 'fetchTaintedString'}}
                                 // expected-note@-1{{Returning from 'fetchTaintedString'}}
  unknownTransformInOut(filename, filename_transformed); // expected-note {{Taint propagated to the 2nd argument}}
  clang_analyzer_isTainted(*filename); // expected-note{{YES}}
                                       // expected-warning@-1{{YES}}
  clang_analyzer_isTainted(*filename_transformed); // expected-note{{YES}}                                                   
                                                   // expected-warning@-1{{YES}}
  strncat(cmd, filename_transformed, sizeof(cmd) - 1); // expected-note {{Taint propagated to the 1st argument}}
  system(cmd);// expected-warning {{Untrusted data is passed to a system call}}
              // expected-note@-1 {{Untrusted data is passed to a system call}}
}

