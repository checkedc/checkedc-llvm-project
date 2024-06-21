// RUN: rm -rf %t*
// RUN: 3c -base-dir=%S -alltypes -addcr %s -- -Wno-error=incompatible-function-pointer-types | FileCheck -match-full-lines -check-prefixes="CHECK_ALL","CHECK" %s
// RUN: 3c -base-dir=%S -addcr %s -- -Wno-error=incompatible-function-pointer-types | FileCheck -match-full-lines -check-prefixes="CHECK_NOALL","CHECK" %s
// RUN: 3c -base-dir=%S -addcr %s -- -Wno-error=incompatible-function-pointer-types | %clang -c -Wno-error=incompatible-function-pointer-types -fcheckedc-extension -x c -o /dev/null -

// RUN: 3c -base-dir=%S -alltypes -output-dir=%t.checked %s -- -Wno-error=incompatible-function-pointer-types
// RUN: 3c -base-dir=%t.checked -alltypes %t.checked/fptrunsafecallee.c -- -Wno-error=incompatible-function-pointer-types | diff %t.checked/fptrunsafecallee.c -

/******************************************************************************/

/*This file tests three functions: two callers bar and foo, and a callee sus*/
/*In particular, this file tests: converting the callee into a function pointer
  unsafely via cast and using that pointer for computations*/
/*In this test, foo and bar will treat their return values safely, but sus will
  not, through invalid pointer arithmetic, an unsafe cast, etc*/

/******************************************************************************/

#include <stddef.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

struct general {
  int data;
  struct general *next;
  //CHECK: struct general *next;
};

struct warr {
  int data1[5];
  //CHECK_NOALL: int data1[5];
  //CHECK_ALL: int data1 _Checked[5];
  char *name;
  //CHECK: _Ptr<char> name;
};

struct fptrarr {
  int *values;
  //CHECK: _Ptr<int> values;
  char *name;
  //CHECK: _Ptr<char> name;
  int (*mapper)(int);
  //CHECK: _Ptr<int (int)> mapper;
};

struct fptr {
  int *value;
  //CHECK: _Ptr<int> value;
  int (*func)(int);
  //CHECK: _Ptr<int (int)> func;
};

struct arrfptr {
  int args[5];
  //CHECK_NOALL: int args[5];
  //CHECK_ALL: int args _Checked[5];
  int (*funcs[5])(int);
  //CHECK_NOALL: int (*funcs[5])(int);
  //CHECK_ALL: _Ptr<int (int)> funcs _Checked[5];
};

int add1(int x) {
  //CHECK: int add1(int x) _Checked {
  return x + 1;
}

int sub1(int x) {
  //CHECK: int sub1(int x) _Checked {
  return x - 1;
}

int fact(int n) {
  //CHECK: int fact(int n) _Checked {
  if (n == 0) {
    return 1;
  }
  return n * fact(n - 1);
}

int fib(int n) {
  //CHECK: int fib(int n) _Checked {
  if (n == 0) {
    return 0;
  }
  if (n == 1) {
    return 1;
  }
  return fib(n - 1) + fib(n - 2);
}

int zerohuh(int n) {
  //CHECK: int zerohuh(int n) _Checked {
  return !n;
}

int *mul2(int *x) {
  //CHECK: _Ptr<int> mul2(_Ptr<int> x) _Checked {
  *x *= 2;
  return x;
}

int *sus(struct general *x, struct general *y) {
  //CHECK: int *sus(struct general *x, struct general *y) {

  x = (struct general *)5;
  //CHECK: x = (struct general *)5;
  int *z = calloc(5, sizeof(int));
  //CHECK: int *z = calloc<int>(5, sizeof(int));
  struct general *p = y;
  //CHECK: struct general *p = y;
  int i;
  for (i = 0; i < 5; p = p->next, i++) {
    z[i] = p->data;
  }

  z += 2;
  return z;
}

int *foo() {
  //CHECK: int *foo(void) : itype(_Ptr<int>) {

  struct general *x = malloc(sizeof(struct general));
  //CHECK: struct general *x = malloc<struct general>(sizeof(struct general));
  struct general *y = malloc(sizeof(struct general));
  //CHECK: struct general *y = malloc<struct general>(sizeof(struct general));
  struct general *curr = y;
  //CHECK: struct general *curr = y;
  int i;
  for (i = 1; i < 5; i++, curr = curr->next) {
    curr->data = i;
    curr->next = malloc(sizeof(struct general));
    curr->next->data = i + 1;
  }
  int (*sus_ptr)(struct fptr *, struct fptr *) = sus;
  //CHECK: int (*sus_ptr)(struct fptr *, struct fptr *) = sus;
  int *z = (int *)sus_ptr(x, y);
  //CHECK: int *z = (int *)sus_ptr(x, y);

  return z;
}

int *bar() {
  //CHECK: int *bar(void) : itype(_Ptr<int>) {

  struct general *x = malloc(sizeof(struct general));
  //CHECK: struct general *x = malloc<struct general>(sizeof(struct general));
  struct general *y = malloc(sizeof(struct general));
  //CHECK: struct general *y = malloc<struct general>(sizeof(struct general));
  struct general *curr = y;
  //CHECK: struct general *curr = y;
  int i;
  for (i = 1; i < 5; i++, curr = curr->next) {
    curr->data = i;
    curr->next = malloc(sizeof(struct general));
    curr->next->data = i + 1;
  }
  int (*sus_ptr)(struct fptr *, struct fptr *) = sus;
  //CHECK: int (*sus_ptr)(struct fptr *, struct fptr *) = sus;
  int *z = (int *)sus_ptr(x, y);
  //CHECK: int *z = (int *)sus_ptr(x, y);

  return z;
}
