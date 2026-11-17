// tools-B/preload/oracle.c (shard B): kernels/xorshift/xorshift.c's loop, started from a preloaded state.
// The body is copied verbatim from kernels/xorshift/xorshift.c; the only change is `int i = i0` (was `int i = 0`).
// Usage: oracle xorshift I0 SEED,ROUNDS ...   -> comma-separated results (unsigned 32-bit), as simx --want takes.
// Valid as "the hardware from the same state" only for I0 < ROUNDS (the hardware runs the body once before its
// first test; at I0 = 0 that equals the C, and for 0 <= I0 < ROUNDS too). The caller enforces it.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef int in_int_t;
static int xorshift_from(in_int_t seed, in_int_t rounds, int i0) {
  unsigned x = (unsigned)seed;
  int i = i0;

  while (i < rounds) {
    x = x ^ (x << 13);
    x = x ^ (x >> 17);
    x = x ^ (x << 5);
    i = i + 1;
  }

  return (int)x;
}
int main(int argc, char** argv) {
  if (argc < 4 || strcmp(argv[1], "xorshift")) { fprintf(stderr, "usage: oracle xorshift I0 SEED,ROUNDS ...\n"); return 1; }
  long long i0 = strtoll(argv[2], 0, 0);
  for (int k = 3; k < argc; k++) {
    char* c = strchr(argv[k], ','); if (!c) return 1;
    long long s = strtoll(argv[k], 0, 0), r = strtoll(c + 1, 0, 0);
    if (!(0 <= i0 && i0 < r && r <= 0x7fffffffLL)) { fprintf(stderr, "oracle: need 0 <= I0 < ROUNDS < 2^31 (I0 %lld, ROUNDS %lld)\n", i0, r); return 1; }
    printf("%s%u", k > 3 ? "," : "", (unsigned)xorshift_from((in_int_t)(unsigned)s, (in_int_t)r, (int)i0));
  }
  printf("\n");
  return 0;
}
