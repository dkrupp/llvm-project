// RUN: %clang_analyze_cc1  -analyzer-checker=optin.taint,core,alpha.security.ArrayBoundV2 \
// RUN: -analyzer-config optin.taint.TaintPropagation:Config=%S/taint-config.yaml \
// RUN: -analyzer-config optin.taint.TaintPropagation:AggressiveTaintPropagation=true \
// RUN: -analyzer-config analyzer-focused-taint=true \
// RUN: -analyzer-config analyzer-inline-taint-only=false \
// RUN: -analyzer-config analyzer-always-inline-tainted=true \
// RUN: -analyzer-config analyzer-always-inline-tainted=true \
// RUN: -Wno-format-security -verify %s

typedef long long rsize_t;
int system(const char *command);
int scanf(const char *restrict format, ...);
char *gets(char *str);
char *gets_s(char *str, rsize_t n);
int getchar(void);
int system(const char *command);
char *strcat( char *dest, const char *src );
int printf( const char* format, ... );

char buf[1024];

void fetchTaintedString(char *txt){
  scanf("%s", txt);
}

void exec(char* cmd){
  system(cmd);// expected-warning {{Untrusted data is passed to a system call}}

}

//Test1

void topLevel(){
  char cmd[2048] = "/bin/cat ";
  char filename[1024];
  fetchTaintedString (filename);
  strcat(cmd, filename);
  exec(cmd);
}

void printNum(int data){
  printf("Data:%d\n",data);
}

// Test 2

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
