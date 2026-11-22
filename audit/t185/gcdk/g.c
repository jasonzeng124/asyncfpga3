#include <stdlib.h>
//===- gcd.c - Computes GCD of two integers  ----------------------*- C -*-===//
//
// Implements the gcd kernel (https://en.algorithmica.org/hpc/algorithms/gcd/).
//
//===----------------------------------------------------------------------===//

typedef int in_int_t; unsigned kmax=0;


int gcd(in_int_t a, in_int_t b) {
  if (a == 0)
    return b;
  if (b == 0)
    return a;

  // Find the greatest power of 2 that divides both a and b
  unsigned k = 0;
  while (((a | b) & 1) == 0) {
    a >>= 1;
    b >>= 1;
    k++;
  }
  if (k>kmax) kmax=k; if (getenv("KONLY")) return 0;

  // a := __builtin_ctz(a)
  while (a > 0 && (a & 1) == 0)
    a >>= 1;
  // b := __builtin_ctz(b)
  while (b > 0 && (b & 1) == 0)
    b >>= 1;

  while (a != 0) {
    in_int_t diff = a - b;
    // b := min(a, b);
    if (a < b)
      b = a;
    // a := abs(diff)
    if (diff >= 0)
      a = diff;
    else
      a = -diff;
    // a := __builtin_ctz(a)
    while (a > 0 && (a & 1) == 0)
      a >>= 1;
  }

  return (int)((unsigned)b << k);
}

#include <stdio.h>
#include <limits.h>
#include <stdlib.h>
int main(){ int v[]={0,1,-1,2,-2,INT_MIN,INT_MAX,1<<30,-(1<<30),1<<16,3<<29,INT_MIN+2};
 int n=sizeof v/sizeof v[0];
 for(int i=0;i<n;i++)for(int j=0;j<n;j++){gcd(v[i],v[j]);}
 printf("edge kmax=%u\n",kmax);
 srand(1); for(long t=0;t<2000000;t++){int a=(int)(((unsigned)rand()<<16)^rand()); int b=(int)(((unsigned)rand()<<16)^rand()); int s=rand()%32; a=(int)((unsigned)a<<s); b=(int)((unsigned)b<<s); if(a>0||b>0||1) gcd(a,b);}
 printf("all kmax=%u\n",kmax); unsigned kk=kmax; kmax=0; gcd(INT_MIN,INT_MIN); printf("INT_MIN,INT_MIN k=%u\n",kmax); return 0;}
