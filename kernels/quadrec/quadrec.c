//===- quadrec.c - several live values across the back edge -------*- C -*-===//
//
// SUITE KERNEL (2026-11-17; research/PROGRAM.md "A benchmark suite for the compiler"; kernels/SUITE.md).
// SHAPE: several live values across the back edge: a, b, c, d and the counter i (five), plus the invariant n.
// EXERCISES: one mux per loop-carried value, all on one ring; three of the four values are plain moves
// (a <- b <- c <- d), so the ring's storage, not its arithmetic, holds most of the state. The result weighs the four
// values differently, so a permutation of them is a wrong answer.
// INPUT RANGE: x any int32; n <= 256 (any negative n is 0 trips). Unsigned arithmetic: no UB.
// (The range is the routed-GLS budget: the gate simulates ~0.2 us of circuit time per wall second, so the declared
// range keeps trip counts in the hundreds.)
//
//===----------------------------------------------------------------------===//
#include "quadrec.h"
#include "dynamatic/Integration.h"

int quadrec(in_int_t x, in_int_t n) {
  unsigned a = (unsigned)x, b = 0x6a09e667u, c = 0xbb67ae85u, d = 0x3c6ef372u;
  for (int i = 0; i < n; i++) {
    unsigned t = a + (b ^ c) + (d >> 3);
    a = b;
    b = c;
    c = d;
    d = t;
  }
  return (int)(a ^ (b << 1) ^ (c << 2) ^ (d << 3));
}

int main(void) {
  in_int_t x = 42, n = 50;
  CALL_KERNEL(quadrec, x, n);
  return 0;
}
