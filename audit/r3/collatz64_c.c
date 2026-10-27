#include <stdio.h>
#include <stdlib.h>
typedef long long in_int_t;
/* verbatim kernel body from kernels/collatz64/collatz64.c */
int collatz64(in_int_t n) {
  int steps = 0;
  while (n != 1) {
    if ((n & 1) == 0) n = n >> 1; else n = 3 * n + 1;
    steps = steps + 1;
  }
  return steps;
}
int main(int argc, char **argv) {
  for (int i = 1; i < argc; i++) {
    long long n = atoll(argv[i]);
    long long m = n, x = n;
    while (x != 1) { x = (x & 1) ? 3*x+1 : x>>1; if (x > m) m = x; }
    printf("%lld %d %lld\n", n, collatz64(n), m);
  }
  return 0;
}
