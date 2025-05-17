// RUN: %clang_analyze_cc1 -analyzer-checker=optin.taint,core,alpha.security.ArrayBoundV2 \
// RUN: -analyzer-config optin.taint.TaintPropagation:Config=%S/taint-config.yaml \
// RUN: -analyzer-config optin.taint.TaintPropagation:AggressiveTaintPropagation=true \
// RUN: -analyzer-config analyzer-focused-taint=false \
// RUN: -analyzer-checker=debug.ExprInspection \
// RUN: -analyzer-config analyzer-inline-taint-only=false \
// RUN: -analyzer-config analyzer-always-inline-tainted=true \
// RUN: -Wno-format-security -verify %s

//void clang_analyzer_isTainted(char);
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
int printf( const char* format, ... );
int sprintf( char* buffer, const char* format, ... );
void *malloc(unsigned long);
void free( void *ptr );



char buf[1024];

void fetchTaintedString(char *txt){
  scanf("%s", txt);
}

void exec(char* cmd){
  system(cmd);// expected-warning {{Untrusted data is passed to a system call}}

}

// Test1
// Interprocedural test
// PASSES in baseline

void topLevel(){
  char cmd[2048] = "/bin/cat ";
  char filename[1024];
  fetchTaintedString (filename);
  clang_analyzer_isTainted(*filename); // expected-warning{{YES}}
  strcat(cmd, filename);
  exec(cmd);
}

void printNum(int data){
  printf("Data:%d\n",data);
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
  strcat(cmd, filename);
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
  strcat(cmd, filename);
  system(cmd);// expected-warning {{Untrusted data is passed to a system call}}
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
  return i;
}


void test_large_loop2(int input){
  char cmd[2048] = "/bin/cat ";
  char filename[1024];
  fetchTaintedString (filename);
  int i = complex_function(cmd);
  clang_analyzer_isTainted(*filename); // expected-warning{{YES}}
  strcat(cmd, filename);
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
  clang_analyzer_isTainted(i); // expected-warning{{YES}}
  clang_analyzer_isTainted(*filename); // expected-warning{{YES}}
  strcat(cmd, filename);
  system(cmd);// expected-warning {{Untrusted data is passed to a system call}}
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
  return i;
}

void test_large_loop4(int input){
  char cmd[2048] = "/bin/cat ";
  char filename[1024];
  fetchTaintedString (filename);
  int i = complex_function_const(filename); // tainted value is lost from filename because complex function cannot be analyzed
  clang_analyzer_isTainted(*filename); // expected-warning{{YES}}
  strcat(cmd, filename);
  system(cmd);// expected-warning {{Untrusted data is passed to a system call}}
}



// Test Unknown Function1
// calling an external unkown function before the sink
// with aggressive propagation unknownTransform(filename)
// should keep taintedness on filename
// FAILS in baseline

extern void unknownTransform(char* txt);

void test_unkown_transform1(int input){
  char cmd[2048] = "/bin/cat ";
  char filename[1024];
  fetchTaintedString (filename);
  unknownTransform(filename); // taintedness gets lost here
  strcat(cmd, filename);
  system(cmd);// expected-warning {{Untrusted data is passed to a system call}}
}


// Test Unknown Function 2
// calling an external unkown function before the sink
// with aggressive propagation filename_transformed should be
// tainted too
// FAILS in baseline

void unknownTransformInOut(char* in, char* out);

void test_unknown_transform2(int input){
  char cmd[2048] = "/bin/cat ";
  char filename[1024];
  char filename_transformed[1024];
  fetchTaintedString (filename);
  unknownTransformInOut(filename, filename_transformed); // taintedness gets lost here
  clang_analyzer_isTainted(*filename); // expected-warning{{YES}}
  clang_analyzer_isTainted(*filename_transformed); // expected-warning{{YES}}
  strcat(cmd, filename_transformed);
  system(cmd);// expected-warning {{Untrusted data is passed to a system call}}
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
  strcat(cmd, filename_transformed);
  system(cmd);
}



// Test tainted heap
// tainted data on heap
// PASSES in baseline

void test_tainted_heap(int input){
  char cmd[2048] = "/bin/cat ";
  char* filenameOnHeap = (char*) malloc(1024);
  fetchTaintedString (filenameOnHeap);
  strcat(cmd, filenameOnHeap);
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
  strcat(cmd, filenameOnHeap_global);
  system(cmd);// expected-warning {{Untrusted data is passed to a system call}}
  free(filenameOnHeap_global);
}



// Testing taint propagation when the destination
// is a pointer arithm
// PASSES in baseline

void test_tainted_pointer_arithm(int input){
  char cmd[2048] = "/bin/cat ";
  char* filenameOnHeap = (char*) malloc(1024);
  fetchTaintedString (filenameOnHeap);
  strcat(cmd+3, filenameOnHeap); //performing arithmetic on pointer
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
  strcat(cmd+6, filenameOnHeap); //performing arithmetic on pointer
  clang_analyzer_isTainted(*cmd); // expected-warning{{NO}}
  system(cmd);// expected-warning {{Untrusted data is passed to a system call}}
  free(filenameOnHeap);
}
