// RUN: %clang_analyze_cc1 -analyzer-checker=optin.taint,core \
// RUN: -analyzer-config optin.taint.TaintPropagation:Config=%S/taint-config.yaml \
// RUN: -analyzer-config optin.taint.TaintPropagation:TaintPropagationMode=forget \
// RUN: -analyzer-config analyzer-focused-taint=false \
// RUN: -analyzer-checker=debug.ExprInspection \
// RUN: -analyzer-config analyzer-inline-taint-only=false \
// RUN: -analyzer-config analyzer-always-inline-tainted=false \
// RUN: -Wno-format-security -verify=expected,forget %s


// RUN: %clang_analyze_cc1 -analyzer-checker=optin.taint,core \
// RUN: -analyzer-config optin.taint.TaintPropagation:Config=%S/taint-config.yaml \
// RUN: -analyzer-config optin.taint.TaintPropagation:TaintPropagationMode=keep \
// RUN: -analyzer-config analyzer-focused-taint=false \
// RUN: -analyzer-checker=debug.ExprInspection \
// RUN: -analyzer-config analyzer-inline-taint-only=false \
// RUN: -analyzer-config analyzer-always-inline-tainted=false \
// RUN: -Wno-format-security -verify=expected,keep %s


// RUN: %clang_analyze_cc1 -analyzer-checker=optin.taint,core \
// RUN: -analyzer-config optin.taint.TaintPropagation:Config=%S/taint-config.yaml \
// RUN: -analyzer-config optin.taint.TaintPropagation:TaintPropagationMode=spread \
// RUN: -analyzer-config analyzer-focused-taint=false \
// RUN: -analyzer-checker=debug.ExprInspection \
// RUN: -analyzer-config analyzer-inline-taint-only=false \
// RUN: -analyzer-config analyzer-always-inline-tainted=false \
// RUN: -Wno-format-security -verify=expected,spread %s

//void clang_analyzer_isTainted(char);
void clang_analyzer_isTainted_ptr(void *);
void clang_analyzer_isTainted(int);
void clang_analyzer_isTainted_any_suffix(char);
void clang_analyzer_isTainted_many_arguments(char, int, int);

typedef long long rsize_t;
typedef rsize_t size_t;
int system(const char *command);
int scanf(const char *restrict format, ...);
char *gets(char *str);
char *gets_s(char *str, rsize_t n);
int getchar(void);
int system(const char *command);
char *strcat( char *dest, const char *src );
char *strncat( char *dest, const char *src, unsigned long count);
char* strcpy( char* dest, const char* src );
char * strncpy ( char * destination, const char * source, unsigned long num );
unsigned long strlen( const char* str );
int printf( const char* format, ... );
int sprintf( char* buffer, const char* format, ... );
int snprintf ( char * s, unsigned long n, const char * format, ... );
void *malloc(unsigned long);
void free( void *ptr );



char buf[1024];

void fetchTaintedString(char *txt){
  scanf("%s", txt);
}

void fetchTaintedNumber(int *num){
  scanf("%d", num);
}

void exec(char* cmd){
  system(cmd);// expected-warning {{Untrusted data is passed to a system call}}

}

// Test1
// Interprocedural test
// PASSES in baseline

void vulnerableCat(){
  char cmd[2048] = "/bin/cat ";
  char filename[1024];
  fetchTaintedString (filename);
  clang_analyzer_isTainted(*filename); // expected-warning{{YES}}
  strncat(cmd, filename, sizeof(cmd) - 1);
  exec(cmd);
}

void printNum(int data){
  printf("Data:%d\n",data);
}

//This function should not be inlined in
//focused taint analysis mode as it only calls a taint source
void topLevelSrcOnly(){
  char cmd[2048] = "/bin/cat ";
  char filename[1024];
  fetchTaintedString (filename);
  printNum(1);
}


//This function should not be inlined in
//focused taint analysis mode as it only calls a taint source
void topLevelSinkOnly(){
  char cmd[2048] = "/bin/cat ";
  exec(cmd);
}

// Test 2
// symbolic bounded loop before sink
// PASSES in baseline

extern void unknownFunction();

void topLevel2(int input){
  char cmd[2048] = "/bin/cat ";
  char filename[1024];
  fetchTaintedString (filename);
  int i=0;
  while(i<input){
    unknownFunction();
    i++;
  }
  strncat(cmd, filename, sizeof(cmd) - 1);
  system(cmd);// expected-warning {{Untrusted data is passed to a system call}}
}

// Test 3
// large loop before sink
// FAILS in baseline
void test3(int input){
  char cmd[2048] = "/bin/cat ";
  char filename[1024];
  fetchTaintedString (filename);
  clang_analyzer_isTainted(*filename); // expected-warning{{YES}}
  int i=0;
  while(i<1000){//analysis does not progress beyond this point
    i++;
  }
  strncat(cmd, filename, sizeof(cmd) - 1);
  system(cmd);// KNOWN-TO-FAIL-expected-warning {{Untrusted data is passed to a system call}}
}



// Test large_loop2
// large loop before sink in a complex function
// but does not get the tainted string as a parameter
// PASSES in baseline

int complex_function(char* filename){
  int i=0;
  while(i<1000){//analysis does not progress beyond this point
    i++;
  }
  return strlen(filename);
}


void test_large_loop2(int input){
  char cmd[2048] = "/bin/cat ";
  char filename[1024];
  fetchTaintedString (filename);
  int i = complex_function(cmd);
  clang_analyzer_isTainted(*filename); // expected-warning{{YES}}
  strncat(cmd, filename, sizeof(cmd) - 1);
  system(cmd);// expected-warning {{Untrusted data is passed to a system call}}
}

// Test large_loop3
// large loop before sink in a complex function
// which receives the tainted string as a parameter
// FAILS in baseline

void test_large_loop3(int input){
  char cmd[2048] = "/bin/cat ";
  char filename[1024];
  fetchTaintedString (filename);
  int i = complex_function(filename); // tainted value is lost from filename because complex function cannot be analyzed
  clang_analyzer_isTainted(i); // forget-warning{{NO}}
                               // keep-warning@-1{{NO}}
                               // spread-warning@-2{{YES}}

  clang_analyzer_isTainted(*filename); // forget-warning{{NO}}
                                       // keep-warning@-1{{YES}}
                                       // spread-warning@-2{{YES}}
  strncat(cmd, filename, sizeof(cmd) - 1);
  system(cmd);// keep-warning {{Untrusted data is passed to a system call}}
              // spread-warning@-1{{Untrusted data is passed to a system call}}
}


// Test large_loop4
// large loop before sink in a complex function
// which receives the tainted string as a parameter
// FAILS in baseline

int complex_function_const(const char* filename){
  int i=0;
  while(i<1000){//analysis does not progress beyond this point
    i++;
  }
  return strlen(filename);
}

void test_large_loop4(int input){
  char cmd[2048] = "/bin/cat ";
  char filename[1024];
  fetchTaintedString (filename);
  int i = complex_function_const(filename); // tainted value is lost from filename because complex function cannot be analyzed
  clang_analyzer_isTainted(*filename); // expected-warning{{YES}}
  strncat(cmd, filename, sizeof(cmd) - 1);
  system(cmd);// expected-warning {{Untrusted data is passed to a system call}}
}



// Test Unknown Function1
// calling an external unkown function before the sink
// with keep and spread propagation unknownTransform(filename)
// should keep taintedness on filename
// FAILS in baseline

extern void unknownTransform(char* txt);

void test_unkown_transform1(int input){
  char cmd[2048] = "/bin/cat ";
  char filename[1024];
  fetchTaintedString (filename);
  unknownTransform(filename); // taintedness gets lost here
  strncat(cmd, filename, sizeof(cmd) - 1);
  system(cmd);// keep-warning {{Untrusted data is passed to a system call}}
              // spread-warning@-1 {{Untrusted data is passed to a system call}}
}


// Test Unknown Function 2
// calling an external unkown function before the sink
// with spread propagation filename_transformed should be
// tainted too
// FAILS in baseline

void unknownTransformInOut(char* in, char* out);

void test_unknown_transform2(int input){
  char cmd[2048] = "/bin/cat ";
  char filename[1024];
  char filename_transformed[1024];
  fetchTaintedString (filename);
  unknownTransformInOut(filename, filename_transformed); // taintedness gets lost here
  clang_analyzer_isTainted(*filename); // forget-warning{{NO}}
                                       // keep-warning@-1{{YES}}
                                       // spread-warning@-2{{YES}}
  clang_analyzer_isTainted(*filename_transformed); // forget-warning{{NO}}
                                                   // keep-warning@-1{{NO}}
                                                   // spread-warning@-2{{YES}}
  strncat(cmd, filename_transformed, sizeof(cmd) - 1);
  system(cmd);// spread-warning {{Untrusted data is passed to a system call}}
}

// Test

void knownTransformInOut(char* in, char* out){ //out is not a tainted string even if in is tainted
  sprintf(out,"%s","hello");
}
void test_known_transform(int input){
  char cmd[2048] = "/bin/cat ";
  char filename[1024];
  char filename_transformed[1024];
  fetchTaintedString (filename);
  knownTransformInOut(filename, filename_transformed); // taintedness gets lost here
  clang_analyzer_isTainted(*filename); // expected-warning{{YES}}
  clang_analyzer_isTainted(*filename_transformed); // expected-warning{{NO}}
  strncat(cmd, filename_transformed, sizeof(cmd) - 1);
  system(cmd);
}



// Test tainted heap
// tainted data on heap
// PASSES in baseline

void test_tainted_heap(int input){
  char cmd[2048] = "/bin/cat ";
  char* filenameOnHeap = (char*) malloc(1024);
  fetchTaintedString (filenameOnHeap);
  strncat(cmd, filenameOnHeap, sizeof(cmd) - 1);
  system(cmd);// expected-warning {{Untrusted data is passed to a system call}}
  free(filenameOnHeap);
}



// Test tainted global heap async
// Read tainted data into a heap variable in test_tainted_global_heap
// and using that tainted variable in asyncSystemCmd
// could be handled with multiphase analysis
// FAILS in baseline

extern void unknownTransform(char*txt);

char* filenameOnHeap_global;

void test_tainted_global_heap(int input){
  filenameOnHeap_global = (char*) malloc(1024);
  fetchTaintedString(filenameOnHeap_global);
}

void asyncSystemCmd(void){
  char cmd[2048] = "/bin/cat ";
  strncat(cmd, filenameOnHeap_global, sizeof(cmd) - 1);
  system(cmd);// KNOWN-TO-FAIL-expected-warning {{Untrusted data is passed to a system call}}
  free(filenameOnHeap_global);
}



// Testing taint propagation when the destination
// is a pointer arithm
// PASSES in baseline

void test_tainted_pointer_arithm(int input){
  char cmd[2048] = "/bin/cat ";
  char* filenameOnHeap = (char*) malloc(1024);
  fetchTaintedString (filenameOnHeap);
  strncat(cmd+3, filenameOnHeap, sizeof(cmd) - 4); //performing arithmetic on pointer
  clang_analyzer_isTainted(*(cmd+3)); // expected-warning{{YES}}
  system(cmd+3);// expected-warning {{Untrusted data is passed to a system call}}
  free(filenameOnHeap);
}

// Testing taint propagation when the destination
// is a pointer arithm
// PASSES in baseline

void test_tainted_pointer_arithm2(int input){
  char cmd[2048] = "/bin/cat ";
  char* filenameOnHeap = (char*) malloc(1024);
  fetchTaintedString (filenameOnHeap);
  strncat(cmd+6, filenameOnHeap, sizeof(cmd) - 7); //performing arithmetic on pointer
  clang_analyzer_isTainted(*cmd); // expected-warning{{NO}}
  system(cmd);// expected-warning {{Untrusted data is passed to a system call}}
  free(filenameOnHeap);
}


void test_lost_printf(){
  char cmd[2048] = "/bin/cat ";
  char* filenameOnHeap = (char*) malloc(1024);
  fetchTaintedString (filenameOnHeap);
  printf("tainted input:%s\n",filenameOnHeap); // taintedness gets lost here
  clang_analyzer_isTainted(*filenameOnHeap); // forget-warning{{NO}}
                                             // keep-warning@-1{{YES}}
                                             // spread-warning@-2{{YES}}
  strncat(cmd, filenameOnHeap, sizeof(cmd) - 1);
  clang_analyzer_isTainted(*cmd); // forget-warning{{NO}}
                                  // keep-warning@-1{{YES}}
                                  // spread-warning@-2{{YES}}
  system(cmd);// keep-warning {{Untrusted data is passed to a system call}}
              // spread-warning@-1 {{Untrusted data is passed to a system call}}
  free(filenameOnHeap);
}

extern char* unknownTransformRet(char* txt);

// When a function is not inlined
// the return value must be tainted
// when spread propagation is enabled
void test_spread_return(){
  char cmd[2048] = "/bin/cat ";
  char* filenameOnHeap = (char*) malloc(1024);
  fetchTaintedString (filenameOnHeap);
  char* ret = unknownTransformRet(filenameOnHeap);
  clang_analyzer_isTainted(*ret); // forget-warning{{NO}}
                                  // keep-warning@-1{{NO}}
                                  // spread-warning@-2{{YES}}
  strncat(cmd, ret, sizeof(cmd) - 1);
  clang_analyzer_isTainted(*cmd); // forget-warning{{NO}}
                                  // keep-warning@-1{{NO}}
                                  // spread-warning@-2{{YES}}

  system(cmd);// spread-warning {{Untrusted data is passed to a system call}}
  free(filenameOnHeap);
  free (ret);
}


char* knownTranforReturn(char* txt){
  char* ret = (char*) malloc(strlen("hello")+1);
  strcpy(ret,"hello");
  return ret;
}
// When a function is properly inlined
// the return value must not be tainted
// even with spread propagation
void test_known_return(){
  char cmd[2048] = "/bin/cat ";
  char* filenameOnHeap = (char*) malloc(1024);
  fetchTaintedString (filenameOnHeap);
  char* goodString = knownTranforReturn(filenameOnHeap);
  strncat(cmd, goodString, sizeof(cmd) - 1);
  clang_analyzer_isTainted(*cmd); // expected-warning{{NO}}
  system(cmd);
  free(filenameOnHeap);
  free (goodString);
}


// Unsafe String Handling functions

//strcpy: src should be a taint sink
void test_strcpy() {
  char filename[1024];
  char txt[2048];
  fetchTaintedString (txt);
  clang_analyzer_isTainted(*txt); // expected-warning{{YES}}
  strcpy(filename, txt);// expected-warning {{Unrestricted copy of untrusted data can cause buffer overflow}}
}

//strncpy size parameter should be a taint sink
void test_strncpy() {
  char filename[1024];
  char txt[2048];
  int size=0;
  fetchTaintedNumber(&size);
  clang_analyzer_isTainted(size); // expected-warning{{YES}}
  strncpy(filename, txt, size);// expected-warning {{The size parameter can be controlled by an attacker to cause buffer overflow.}}
}


//sprintf
void test_sprintf(){
  char cmd[2048];
  char* filenameOnHeap = (char*) malloc(1024);
  fetchTaintedString (filenameOnHeap);
  sprintf(cmd, "/bin/cat %s",filenameOnHeap); // taint should be propagated to cmd
  clang_analyzer_isTainted(*cmd); // expected-warning{{YES}}
  system(cmd); // expected-warning {{Untrusted data is passed to a system call}}
  free(filenameOnHeap);
}

//snprintf
void test_snprintf(){
  char cmd[2048];
  char* filenameOnHeap = (char*) malloc(1024);
  fetchTaintedString (filenameOnHeap);
  int size=0;
  fetchTaintedNumber(&size);
  snprintf(cmd, size , "/bin/cat %s",filenameOnHeap); // expected-warning {{The size parameter can be controlled by an attacker to cause buffer overflow.}}
  system(cmd); // expected-warning {{Untrusted data is passed to a system call}}
  free(filenameOnHeap);
}


// va_args should be tainted

//argv should be a taint source
int main(int argc, char * argv[]) {
  if (argc < 1)
    return 1;
  char cmd[2048] = "/bin/cat ";
  clang_analyzer_isTainted(*argv[0]); // expected-warning{{YES}}
  strncat(cmd, argv[0], sizeof(cmd) - strlen(cmd)-1);
  system(cmd);// expected-warning {{Untrusted data is passed to a system call}}
  return 0;
}


char* returnSecond(char *a, char* b){
  clang_analyzer_isTainted(*a); //expected-warning{{YES}}
  clang_analyzer_isTainted(*b); //expected-warning{{NO}}
  return b;

}

//Tests that spread taint propagation
//should not taint writeable parameters of
//functions which are inlined
void test_faultyPropagation(){
  char cmd[2048];
  char* fileNameOnHeap = (char*) malloc(1024);
  fetchTaintedString (fileNameOnHeap);
  int size=0;
  char *safeString = (char*) malloc(100);
  strcpy(safeString, "hello");
  //tests if spread taint propagation would not spread taintedess falsely
  //to the second arg
  char* notTaintedString = returnSecond(fileNameOnHeap, safeString);
  snprintf(cmd, size , "/bin/cat %s",notTaintedString);
  system(cmd);//no warning!
  clang_analyzer_isTainted(*notTaintedString); //expected-warning{{NO}}
  free(fileNameOnHeap);
}
