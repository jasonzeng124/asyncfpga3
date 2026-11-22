#include <stdio.h>
typedef int in_int_t;
int varshift(in_int_t x, in_int_t n) {
  unsigned v = (unsigned)x;
  unsigned acc = 0x5bd1e995u;
  for (int i = 0; i < n; i++) {
    unsigned k = acc >> 27;
    acc = (acc << (k & 7u)) ^ (v >> k) ^ (unsigned)((int)acc >> (31u - k)) ^ (unsigned)i;
  }
  return (int)acc;
}
int main(){int x,n; while(scanf("%d %d",&x,&n)==2) printf("%u\n",(unsigned)varshift(x,n)); return 0;}
