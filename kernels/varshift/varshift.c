//===- varshift.c - shifts by a variable amount ---------------------*- C -*-===//
//
// SUITE KERNEL (2026-11-17; research/PROGRAM.md "A benchmark suite for the compiler"; kernels/SUITE.md).
// SHAPE: shifts by a variable amount -- left, logical right and arithmetic right, each by an amount computed from the
// loop-carried state (k = acc >> 27), so no shift is by a constant and none is a rotate LLVM could fold to fshl.
// EXERCISES: shli / shrui / shrsi with a data operand as the amount (barrel shifters) on a ring.
// INPUT RANGE: x any int32; n <= 256 (any negative n is 0 trips). Every shift amount is in 0 .. 31 (no UB). The
// arithmetic shift of a negative int is implementation-defined in C; gcc and clang both shift in the sign (ashr),
// which is what the oracle (gcc) and the frontend (clang) both do.
// (The range is the routed-GLS budget: the gate simulates ~0.2 us of circuit time per wall second, so the declared
// range keeps trip counts in the hundreds.)
//
//===----------------------------------------------------------------------===//
#include "varshift.h"
#include "dynamatic/Integration.h"

int varshift(in_int_t x, in_int_t n) {
  unsigned v = (unsigned)x;
  unsigned acc = 0x5bd1e995u;
  for (int i = 0; i < n; i++) {
    unsigned k = acc >> 27;
    acc = (acc << (k & 7u)) ^ (v >> k) ^ (unsigned)((int)acc >> (31u - k)) ^ (unsigned)i;
  }
  return (int)acc;
}

int main(void) {
  in_int_t x = 0x0F0F1234, n = 40;
  CALL_KERNEL(varshift, x, n);
  return 0;
}
