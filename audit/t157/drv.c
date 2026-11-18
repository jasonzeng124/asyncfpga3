/* agentA's own driver. Reads stdin: lines "CALL i w0 w1 ... wn" (all words of a call, flattened, hex),
   maps them by hand-written per-kernel code, prints "i result_hex". Arrays are malloc'd at the exact C length
   so ASan sees any out-of-bounds read. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static unsigned W[4096]; static int NW;
static int rd(void){ int i; char tag[8]; if (scanf("%7s %d", tag, &i) != 2) return -1; NW = 0;
  unsigned x; int c; while ((c = getchar()) != '\n' && c != EOF) { ungetc(c, stdin); if (scanf("%x", &x)==1) W[NW++]=x; else break; } return i; }
#define I32(k) ((int)W[k])
static int *arr32(int off, int n){ int *p = malloc(sizeof(int)*n); for (int i=0;i<n;i++) p[i]=(int)W[off+i]; return p; }
#if defined(K_factorial)
int factorial(int n);
#define CALLK(i) do{ if(NW!=2) abort(); r = (unsigned)factorial(I32(0)); }while(0)
#elif defined(K_iterative_division)
int iterative_division(int, int);
#define CALLK(i) do{ if(NW!=2) abort(); r = (unsigned)iterative_division(I32(0), I32(1)); }while(0)
#elif defined(K_iterative_sqrt)
int iterative_sqrt(int);
#define CALLK(i) do{ if(NW!=2) abort(); r = (unsigned)iterative_sqrt(I32(0)); }while(0)
#elif defined(K_test_int16)
int16_t test_int16();
#define CALLK(i) do{ r = (unsigned)(uint16_t)test_int16(); }while(0)
#elif defined(K_test_loop_free)
int test_loop_free(int,int,int,int);
#define CALLK(i) do{ if(NW!=4) abort(); r = (unsigned)test_loop_free(I32(0),I32(1),I32(2),I32(3)); }while(0)
#elif defined(K_unused_arg)
int unused_arg(int a[1], int used[1], int b);
static unsigned AFILL;
#define CALLK(i) do{ if(NW!=2) abort(); int *a = malloc(sizeof(int)); a[0]=(int)AFILL; int *u = arr32(1,1); \
   r = (unsigned)unused_arg(a, u, I32(0)); free(a); free(u);}while(0)
#elif defined(K_if_loop_1) || defined(K_if_loop_2)
#ifdef K_if_loop_1
int if_loop_1(int a[100], int n);
#define FN if_loop_1
#else
int if_loop_2(int a[100], int n);
#define FN if_loop_2
#endif
#define CALLK(i) do{ if(NW!=101) abort(); int *a = arr32(1,100); r = (unsigned)FN(a, I32(0)); free(a);}while(0)
#elif defined(K_sumi3_mem)
int sumi3_mem(int a[1000]);
#define CALLK(i) do{ if(NW!=1000) abort(); int *a = arr32(0,1000); r = (unsigned)sumi3_mem(a); free(a);}while(0)
#elif defined(K_fir)
int fir(int di[1000], int idx[1000]);
#define CALLK(i) do{ if(NW!=2000) abort(); int *d = arr32(0,1000), *x = arr32(1000,1000); r = (unsigned)fir(d, x); free(d); free(x);}while(0)
#elif defined(K_dot2) || defined(K_gather)
#ifdef K_dot2
int dot2(int a[32], int b[32], int n);
#define FN dot2
#else
int gather(int a[32], int b[32], int n);
#define FN gather
#endif
#define CALLK(i) do{ if(NW!=65) abort(); int *a = arr32(1,32), *b = arr32(33,32); r = (unsigned)FN(a, b, I32(0)); free(a); free(b);}while(0)
#elif defined(K_memsum)
int memsum(int a[32], int n);
#define CALLK(i) do{ if(NW!=33) abort(); int *a = arr32(1,32); r = (unsigned)memsum(a, I32(0)); free(a);}while(0)
#elif defined(K_test_bitint)
unsigned _BitInt(32) test_bitint(unsigned _BitInt(16) arr[10], unsigned _BitInt(5) weight[10]);
#define CALLK(i) do{ if(NW!=20) abort(); unsigned _BitInt(16) *a = malloc(sizeof(*a)*10); unsigned _BitInt(5) *w = malloc(sizeof(*w)*10); \
  for(int j=0;j<10;j++){ if (W[j]>0xffff || W[10+j]>31) fprintf(stderr,"RANGE call %d elem %d\n", i, j); \
   a[j]=(unsigned _BitInt(16))W[j]; w[j]=(unsigned _BitInt(5))W[10+j]; } \
  r = (unsigned)test_bitint(a, w); free(a); free(w);}while(0)
#endif
int main(int argc, char **argv){
#ifdef K_unused_arg
  AFILL = argc > 1 ? strtoul(argv[1],0,0) : 0;
#endif
  int i; unsigned r;
  while ((i = rd()) >= 0) { fprintf(stderr, "@@CALL %d\n", i); fflush(stderr); CALLK(i); printf("%d %08x\n", i, r); fflush(stdout); }
  return 0;
}
