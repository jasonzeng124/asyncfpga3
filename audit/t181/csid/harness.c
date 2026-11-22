#include <stdio.h>
typedef int in_int_t;
int xorshift(in_int_t seed, in_int_t rounds) {
  unsigned x = (unsigned)seed;
  int i = 0;

  while (i < rounds) {
    x = x ^ (x << 13);
    x = x ^ (x >> 17);
    x = x ^ (x << 5);
    i = i + 1;
  }

  return (int)x;
}
int main(void){ unsigned s; long long k; while(scanf("%u %lld",&s,&k)==2){ int r=xorshift((int)s,(int)k); printf("%u %lld %u\n",s,k,(unsigned)r);} return 0;}
