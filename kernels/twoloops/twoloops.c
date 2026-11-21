//===- twoloops.c - two loops in sequence -------------------------*- C -*-===//
//
// SUITE KERNEL (2026-11-17; research/PROGRAM.md "A benchmark suite for the compiler"; kernels/SUITE.md).
// SHAPE: two loops in sequence. The second loop's trip count (x & 255) is the first loop's result, so the
// second ring cannot start before the first has drained.
// EXERCISES: two rings in series with a value handed from one to the other; a zero-trip second loop whenever
// x & 255 == 0.
// INPUT RANGE: a any int32; n <= 128 (any negative n is 0 trips); second loop <= 255 trips. Unsigned mixing: no UB.
// (The range is the routed-GLS budget: the gate simulates ~0.2 us of circuit time per wall second, so the declared
// range keeps trip counts in the hundreds.)
//
//===----------------------------------------------------------------------===//
#include "twoloops.h"
#include "dynamatic/Integration.h"

int twoloops(in_int_t a, in_int_t n) {
  unsigned x = (unsigned)a;
  for (int i = 0; i < n; i++)
    x = (x ^ (x << 7)) + (unsigned)i;
  int m = (int)(x & 255u);
  unsigned y = x;
  for (int j = 0; j < m; j++)
    y = (y ^ (y >> 3)) + 0x9e37u;
  return (int)y;
}

int main(void) {
  in_int_t a = 77, n = 30;
  CALL_KERNEL(twoloops, a, n);
  return 0;
}
