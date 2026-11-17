//===- nest3.c - a loop nest three deep ---------------------------*- C -*-===//
//
// SUITE KERNEL (2026-11-17; research/PROGRAM.md "A benchmark suite for the compiler"; kernels/SUITE.md).
// SHAPE: a loop nest three deep. The innermost bound (i ^ j) & 3 is 0 for a quarter of the (i, j) pairs, so the
// innermost ring is often entered and left at once, in the middle of the nest.
// EXERCISES: three rings that share one token (kernels/nested has two); an accumulator live across all three.
// INPUT RANGE: a <= 8, b <= 8 (any negative value is 0 trips); at a = b = 8: 8 + 64 + 96 iterations of the three loops.
// Unsigned accumulator; the index arithmetic stays below 2^10: no UB.
// (The range is the routed-GLS budget: the gate simulates ~0.2 us of circuit time per wall second, so the declared
// range keeps trip counts in the hundreds.)
//
//===----------------------------------------------------------------------===//
#include "nest3.h"
#include "dynamatic/Integration.h"

int nest3(in_int_t a, in_int_t b) {
  unsigned acc = 0x12345u;
  for (int i = 0; i < a; i++)
    for (int j = 0; j < b; j++)
      for (int k = 0; k < ((i ^ j) & 3); k++)
        acc = (acc ^ (acc >> 5)) + (unsigned)((i << 4) ^ (j << 2) ^ k) + 1u;
  return (int)acc;
}

int main(void) {
  in_int_t a = 4, b = 5;
  CALL_KERNEL(nest3, a, b);
  return 0;
}
