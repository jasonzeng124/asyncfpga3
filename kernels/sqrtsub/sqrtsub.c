//===- sqrtsub.c - a trip count that depends on the data ----------*- C -*-===//
//
// SUITE KERNEL (2026-11-17; research/PROGRAM.md "A benchmark suite for the compiler"; kernels/SUITE.md).
// SHAPE: a trip count that depends on the data -- the exit test compares two values the loop itself computes
// (what is left of n against the next odd number), so the count is not known at loop entry.
// EXERCISES: a loop-carried compare of two loop-carried values, three live values, no multiply or divide.
// Computes floor(sqrt(n)) for n >= 0 by subtracting 1, 3, 5, ... (their partial sums are the squares); 0 for n < 0.
// INPUT RANGE: n <= 65536 = 2^16 (trip count floor(sqrt(n)) <= 256); any negative n is 0 trips. No overflow:
// n - odd is only taken when n >= odd, and odd <= 2 * 46341 + 1 for any int32 n.
// (The range is the routed-GLS budget: the gate simulates ~0.2 us of circuit time per wall second, so the declared
// range keeps trip counts in the hundreds.)
//
//===----------------------------------------------------------------------===//
#include "sqrtsub.h"
#include "dynamatic/Integration.h"

int sqrtsub(in_int_t n) {
  int r = 0;
  int odd = 1;
  while (n >= odd) {
    n = n - odd;
    odd = odd + 2;
    r = r + 1;
  }
  return r;
}

int main(void) {
  in_int_t n = 1000;
  CALL_KERNEL(sqrtsub, n);
  return 0;
}
