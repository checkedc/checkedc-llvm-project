// RUN: cconv-standalone -alltypes %s -- | FileCheck -match-full-lines -check-prefixes="CHECK_ALL" %s
//RUN: cconv-standalone %s -- | FileCheck -match-full-lines -check-prefixes="CHECK_NOALL" %s
//RUN: cconv-standalone -output-postfix=checkedNOALL %s
//RUN: %clang -c %S/fptrarrinstructcallee.checkedNOALL.c
//RUN: rm %S/fptrarrinstructcallee.checkedNOALL.c


/*********************************************************************************/

/*This file tests three functions: two callers bar and foo, and a callee sus*/
/*In particular, this file tests: how the tool behaves when there is an array
of function pointers in a struct*/
/*In this test, foo and bar will treat their return values safely, but sus will
not, through invalid pointer arithmetic, an unsafe cast, etc*/

/*********************************************************************************/


#define size_t int
#define NULL 0
extern _Itype_for_any(T) void *calloc(size_t nmemb, size_t size) : itype(_Array_ptr<T>) byte_count(nmemb * size);
extern _Itype_for_any(T) void free(void *pointer : itype(_Array_ptr<T>) byte_count(0));
extern _Itype_for_any(T) void *malloc(size_t size) : itype(_Array_ptr<T>) byte_count(size);
extern _Itype_for_any(T) void *realloc(void *pointer : itype(_Array_ptr<T>) byte_count(1), size_t size) : itype(_Array_ptr<T>) byte_count(size);
extern int printf(const char * restrict format : itype(restrict _Nt_array_ptr<const char>), ...);
extern _Unchecked char *strcpy(char * restrict dest, const char * restrict src : itype(restrict _Nt_array_ptr<const char>));

struct general { 
    int data; 
    struct general *next;
};
//CHECK_NOALL:     _Ptr<struct general> next;

//CHECK_ALL:     _Ptr<struct general> next;


struct warr { 
    int data1[5];
    char *name;
};
//CHECK_NOALL:     int data1[5];
//CHECK_NOALL:     _Ptr<char> name;

//CHECK_ALL:     int data1 _Checked[5];
//CHECK_ALL:     _Ptr<char> name;


struct fptrarr { 
    int *values; 
    char *name;
    int (*mapper)(int);
};
//CHECK_NOALL:     _Ptr<int> values; 
//CHECK_NOALL:     _Ptr<char> name;
//CHECK_NOALL:     _Ptr<int (int )> mapper;

//CHECK_ALL:     _Ptr<int> values; 
//CHECK_ALL:     _Ptr<char> name;
//CHECK_ALL:     _Ptr<int (int )> mapper;


struct fptr { 
    int *value; 
    int (*func)(int);
};  
//CHECK_NOALL:     _Ptr<int> value; 
//CHECK_NOALL:     _Ptr<int (int )> func;

//CHECK_ALL:     _Ptr<int> value; 
//CHECK_ALL:     _Ptr<int (int )> func;


struct arrfptr { 
    int args[5]; 
    int (*funcs[5]) (int);
};
//CHECK_NOALL:     int args[5]; 
//CHECK_NOALL:     int (*funcs[5]) (int);

//CHECK_ALL:     int args _Checked[5]; 
//CHECK_ALL:     _Ptr<int (int )> funcs _Checked[5];


int add1(int x) { 
    return x+1;
} 

int sub1(int x) { 
    return x-1; 
} 

int fact(int n) { 
    if(n==0) { 
        return 1;
    } 
    return n*fact(n-1);
} 

int fib(int n) { 
    if(n==0) { return 0; } 
    if(n==1) { return 1; } 
    return fib(n-1) + fib(n-2);
} 

int zerohuh(int n) { 
    return !n;
}

int *mul2(int *x) { 
    *x *= 2; 
    return x;
}

//CHECK_NOALL: _Ptr<int> mul2(_Ptr<int> x) { 

//CHECK_ALL: _Ptr<int> mul2(_Ptr<int> x) { 

struct arrfptr * sus(struct arrfptr *x, struct arrfptr *y) {
 
        x = (struct arrfptr *) 5; 
        struct arrfptr *z = malloc(sizeof(struct arrfptr)); 
        for(int i = 0; i < 5; i++) { 
            z->args[i] = i + 1; 
        } 
        z->funcs[0] = add1;
        z->funcs[1] = sub1; 
        z->funcs[2] = zerohuh;
        z->funcs[3] = fib;
        z->funcs[4] = fact;
        
z += 2;
return z; }
//CHECK_NOALL: struct arrfptr * sus(struct arrfptr *x, _Ptr<struct arrfptr> y) {
//CHECK_NOALL:         struct arrfptr *z = malloc(sizeof(struct arrfptr)); 
//CHECK_ALL: struct arrfptr * sus(struct arrfptr *x, _Ptr<struct arrfptr> y) {
//CHECK_ALL:         struct arrfptr *z = malloc(sizeof(struct arrfptr)); 

struct arrfptr * foo() {
 
        struct arrfptr * x = malloc(sizeof(struct arrfptr));
        struct arrfptr * y =  malloc(sizeof(struct arrfptr));
       
        struct arrfptr *z = sus(x, y); 
        for(int i = 0; i < 5; i++) { 
            z->args[i] = z->funcs[i](z->args[i]);
        }
        
return z; }
//CHECK_NOALL: struct arrfptr * foo() {
//CHECK_NOALL:         struct arrfptr * x = malloc(sizeof(struct arrfptr));
//CHECK_NOALL:         _Ptr<struct arrfptr> y =   malloc(sizeof(struct arrfptr));
//CHECK_NOALL:         struct arrfptr *z = sus(x, y); 
//CHECK_ALL: struct arrfptr * foo() {
//CHECK_ALL:         struct arrfptr * x = malloc(sizeof(struct arrfptr));
//CHECK_ALL:         _Ptr<struct arrfptr> y =   malloc(sizeof(struct arrfptr));
//CHECK_ALL:         struct arrfptr *z = sus(x, y); 

struct arrfptr * bar() {
 
        struct arrfptr * x = malloc(sizeof(struct arrfptr));
        struct arrfptr * y =  malloc(sizeof(struct arrfptr));
       
        struct arrfptr *z = sus(x, y); 
        for(int i = 0; i < 5; i++) { 
            z->args[i] = z->funcs[i](z->args[i]);
        }
        
return z; }
//CHECK_NOALL: struct arrfptr * bar() {
//CHECK_NOALL:         struct arrfptr * x = malloc(sizeof(struct arrfptr));
//CHECK_NOALL:         _Ptr<struct arrfptr> y =   malloc(sizeof(struct arrfptr));
//CHECK_NOALL:         struct arrfptr *z = sus(x, y); 
//CHECK_ALL: struct arrfptr * bar() {
//CHECK_ALL:         struct arrfptr * x = malloc(sizeof(struct arrfptr));
//CHECK_ALL:         _Ptr<struct arrfptr> y =   malloc(sizeof(struct arrfptr));
//CHECK_ALL:         struct arrfptr *z = sus(x, y); 
