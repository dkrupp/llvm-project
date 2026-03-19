// RUN: %clang_analyze_cc1 -analyzer-checker=optin.taint \
// RUN: -analyzer-checker=debug.ExprInspection \

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


void test_tainted_for(void){
  long limit;
  scanf("%ld", &limit);
  clang_analyzer_isTainted(limit); // expected-warning{{YES}}
  for (int i=0; i < limit; i++){  // expected-warning {{Loop condition is a tainted, attacker controlled value}}
    printf("%d ",i);
  }
}

void test_tainted_for2(void){
  int limit;
  scanf("%d", &limit);
  clang_analyzer_isTainted(limit); // expected-warning{{YES}}
  for (int i=0; i < limit-1; i++){  // expected-warning {{Loop condition is a tainted, attacker controlled value}}
    printf("%d ",i);
  }
}

void test_tainted_while(void){
  int limit;
  scanf("%d", &limit);
  clang_analyzer_isTainted(limit); // expected-warning{{YES}}
  int i=0;
  while(i < limit) {  // expected-warning {{Loop condition is a tainted, attacker controlled value}}
    printf("%d ",i);
    i++;
  }
}

void test_tainted_if(void){
  int limit;
  scanf("%d", &limit);
  clang_analyzer_isTainted(limit); // expected-warning{{YES}}
  int i=0;
  if(i < limit) {  // no report expected for if conditions
    printf("%d ",i);
    i++;
  }
}


void test_tainted_for_char(void){
  char limit;
  scanf("%c", &limit);
  clang_analyzer_isTainted(limit); // expected-warning{{YES}}
  for (char i=0; i < limit; i++){  // no warning expected for such a small type
    printf("%d ",i);
  }
}



void test_tainted_for_bounded(void){
  long limit;
  scanf("%ld", &limit);
  if (limit > 1000)
    return;
  clang_analyzer_isTainted(limit); // expected-warning{{YES}}
  for (int i=0; i < limit; i++){  // No warning expected due to bounded upper limit
    printf("%d ",i);
  }
}