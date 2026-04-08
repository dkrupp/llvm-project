// RUN: %clang_analyze_cc1 -analyzer-checker=optin.taint,core \
// RUN: -analyzer-checker=debug.ExprInspection \
// RUN: -Wno-format-security -verify=expected %s

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

void fetchTaintedString(char *txt){
  scanf("%s", txt);
}

void fetchTaintedNumber(int *num){
  scanf("%d", num);
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

