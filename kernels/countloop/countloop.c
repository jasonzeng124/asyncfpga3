//===- countloop.c - a counted loop -------------------------------*- C -*-===//
//
// SUITE KERNEL (2026-11-17; research/PROGRAM.md "A benchmark suite for the compiler"; kernels/SUITE.md).
// SHAPE: a counted loop -- the trip count is an argument, known when the loop is entered.
// EXERCISES: the smallest ring: a counter, its test, one accumulator and one loop-invariant operand (a) that the
// dataflow graph must carry round the loop. The body uses xor so LLVM's scalar evolution cannot replace the loop by
// a closed form (an add-only body such as s += a would be folded to a multiply).
// INPUT RANGE: a any int32; n <= 256 (trip count max(n, 0); any negative n is 0 trips). Unsigned accumulator: no UB.
// (The range is the routed-GLS budget: the gate simulates ~0.2 us of circuit time per wall second, so the declared
// range keeps trip counts in the hundreds.)
//
//===----------------------------------------------------------------------===//
#include "countloop.h"
#include "dynamatic/Integration.h"

int countloop(in_int_t a, in_int_t n) {
  unsigned s = 0;
  for (int i = 0; i < n; i++)
    s = (s + (unsigned)i) ^ (unsigned)a;
  return (int)s;
}

int main(void) {
  in_int_t a = 0x5a5a1234, n = 100;
  CALL_KERNEL(countloop, a, n);
  return 0;
}
