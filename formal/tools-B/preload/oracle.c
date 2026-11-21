// tools-B/preload/oracle.c (shard B): kernels' loops started from a preloaded state; the bodies are copied verbatim
// from kernels/<k>/<k>.c, the only change being the counter's initial value (`int i = i0` / `int steps = s0`).
//   oracle xorshift  I0 SEED,ROUNDS ...   (I0 = the loop counter i at the loop header)
//   oracle collatz   S0 N[,x] ...          (S0 = the step counter at the loop header; int n)
//   oracle collatz64 S0 N[,x] ...          (long long n)
//   oracle isprime   D0 N[,x] ...          (D0 = the trial divisor d at the loop's first pass; int n)
// Prints the comma-separated results (unsigned 32-bit), as simx --want takes them. Refuses inputs where "the
// hardware from the same state" and this C differ or the C is undefined:
//  - xorshift: needs 0 <= I0 < ROUNDS (the rotated hardware loop runs the body once before its first test);
//  - collatz*: needs N != 1 when S0 != 0 (the hardware answers N == 1 from a separate constant-0 path, not the
//    counter), and no signed overflow (3n+1 within the type, S0 + steps < 2^31), checked step by step.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
static int xorshift_from(int seed, int rounds, int i0) {
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
#define COLLATZ_FROM(NAME, T, TMAX)                                                         \
static int NAME(T n, int s0, int* bad) {                                                    \
  int steps = s0;                                                                           \
  while (n != 1) {                                                                          \
    if (n <= 0 || ((n & 1) && n > (TMAX - 1) / 3) || steps == INT_MAX) { *bad = 1; return 0; } \
    if ((n & 1) == 0)                                                                       \
      n = n >> 1;                                                                           \
    else                                                                                    \
      n = 3 * n + 1;                                                                        \
    steps = steps + 1;                                                                      \
  }                                                                                         \
  return steps;                                                                             \
}
COLLATZ_FROM(collatz_from, int, INT_MAX)
COLLATZ_FROM(collatz64_from, long long, LLONG_MAX)
// isprime: the C loop with the divisor's initial value d = d0 instead of 2, in the order the compiled loop runs it
// (cf_transformed.mlir: n < 2 -> 0 and n < 4 -> 1 are tested first with their own constants, then the body runs once
// with d = d0 BEFORE the first `d * d <= n` test; the test is cmpi sgt on a 32-bit muli, i.e. wrapping: -fwrapv
// semantics, written here with unsigned arithmetic so the C itself is defined). With d0 = 2 this is kernels/isprime.
static int isprime_from(int n, int d0) {
  if (n < 2) return 0;
  if (n < 4) return 1;
  int d = d0;
  for (;;) {
    int r = n;
    int s = d;
    int half = n >> 1;
    while (s <= half)
      s = (int)((unsigned)s << 1);
    while (s >= d) {
      if (r >= s)
        r = (int)((unsigned)r - (unsigned)s);
      s = s >> 1;
    }
    if (r == 0)
      return 0;
    d = (int)((unsigned)d + 1u);
    if ((int)((unsigned)d * (unsigned)d) > n) return 1;
  }
}
int main(int argc, char** argv) {
  if (argc < 4) { fprintf(stderr, "usage: oracle xorshift|collatz|collatz64 START V ...\n"); return 1; }
  const char* k = argv[1]; long long st = strtoll(argv[2], 0, 0);
  for (int a = 3; a < argc; a++) {
    char* c = strchr(argv[a], ','); unsigned long long v = strtoull(argv[a], 0, 0); long long r = c ? strtoll(c + 1, 0, 0) : 0;
    unsigned res;
    if (!strcmp(k, "xorshift")) {
      if (!c || !(0 <= st && st < r && r <= INT_MAX)) { fprintf(stderr, "oracle: xorshift needs 0 <= I0 < ROUNDS < 2^31 (I0 %lld, ROUNDS %lld)\n", st, r); return 1; }
      res = (unsigned)xorshift_from((int)(unsigned)v, (int)r, (int)st);
    } else if (!strcmp(k, "collatz") || !strcmp(k, "collatz64")) {
      int bad = 0;
      if (st < 0 || st > INT_MAX || (st != 0 && v == 1)) { fprintf(stderr, "oracle: %s S0 %lld with n %llu not comparable\n", k, st, v); return 1; }
      res = !strcmp(k, "collatz") ? (unsigned)collatz_from((int)(unsigned)v, (int)st, &bad) : (unsigned)collatz64_from((long long)v, (int)st, &bad);
      if (bad) { fprintf(stderr, "oracle: %s(%llu) from %lld leaves the defined range\n", k, v, st); return 1; }
    } else if (!strcmp(k, "isprime")) {
      // the loop must end in the oracle: a divisor or (d+1)^2 > n with no wrap before it (d0 <= 46340)
      if (st < 2 || st > 46340) { fprintf(stderr, "oracle: isprime needs 2 <= D0 <= 46340 (D0 %lld)\n", st); return 1; }
      res = (unsigned)isprime_from((int)(unsigned)v, (int)st);
    } else { fprintf(stderr, "oracle: unknown kernel %s\n", k); return 1; }
    printf("%s%u", a > 3 ? "," : "", res);
  }
  printf("\n");
  return 0;
}
