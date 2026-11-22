//===- horner.c - multiply on the loop's ring (the DSP path) -------*- C -*-===//
//
// SUITE KERNEL (2026-11-17; research/PROGRAM.md "A benchmark suite for the compiler"; kernels/SUITE.md).
// SHAPE: multiply -- a variable x variable 32-bit multiply (r * x; not a constant, so --arith-reduce-strength
// leaves it a muli) on the loop-carried path, so the DSP's latency is in every iteration.
// EXERCISES: muli -> DSP48E1 (BD_DSP=1) inside a ring; Horner's rule for sum_{i<n} (i ^ 0x5a) x^(n-1-i) mod 2^32.
// INPUT RANGE: x any int32; n <= 256 (any negative n is 0 trips). Unsigned arithmetic: no UB.
// (The range is the routed-GLS budget: the gate simulates ~0.2 us of circuit time per wall second, so the declared
// range keeps trip counts in the hundreds.)
//
//===----------------------------------------------------------------------===//
#include "horner.h"
#include "dynamatic/Integration.h"

int horner(in_int_t x, in_int_t n) {
  unsigned ux = (unsigned)x;
  unsigned r = 0;
  for (int i = 0; i < n; i++)
    r = r * ux + ((unsigned)i ^ 0x5au);
  return (int)r;
}

int main(void) {
  in_int_t x = 3, n = 10;
  CALL_KERNEL(horner, x, n);
  return 0;
}
