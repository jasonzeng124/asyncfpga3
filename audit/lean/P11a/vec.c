/* P11a item 5: reference vectors from the research C kernels (bodies copied verbatim from
   kernels/xorshift/xorshift.c and kernels/collatz/collatz.c, in_int_t = int). */
#include <stdio.h>
typedef int in_int_t;
int xorshift(in_int_t seed, in_int_t rounds) {
  unsigned x = (unsigned)seed; int i = 0;
  while (i < rounds) { x = x ^ (x << 13); x = x ^ (x >> 17); x = x ^ (x << 5); i = i + 1; }
  return (int)x; }
int collatz(in_int_t n) {
  int steps = 0;
  while (n != 1) { if ((n & 1) == 0) n = n >> 1; else n = 3 * n + 1; steps = steps + 1; }
  return steps; }
int main(void) {
  unsigned xs[][2] = {{2463534242u,4},{1,1},{0xFFFFFFFFu,10},{123456789u,1000},{5,0x80000000u},{0xDEADBEEFu,0xFFFFFFFFu},{7,0}};
  for (int i = 0; i < 7; i++) printf("xs %u %u -> %u\n", xs[i][0], xs[i][1], (unsigned)xorshift((int)xs[i][0], (int)xs[i][1]));
  int cs[] = {1, 7, 27, 97, 255, 871};
  for (int i = 0; i < 6; i++) printf("cz %d -> %d\n", cs[i], collatz(cs[i]));
  return 0; }
