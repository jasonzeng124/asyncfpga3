//===- digitdiv.c - division without modulo -------------------------*- C -*-===//
//
// SUITE KERNEL (2026-11-17; research/PROGRAM.md "A benchmark suite for the compiler"; kernels/SUITE.md).
// SHAPE: division -- kernels/digitsum with the remainder written as v - q * b, so the only divider is v / b.
// WHY A SECOND KERNEL FOR THIS SHAPE: digitsum's `%` stops in Dynamatic's own frontend (lower-cf-to-handshake cannot
// legalize arith.remui), before bdc sees anything; this one gets a divui (and a muli) through the frontend, so it
// tells whether bdc can lower a divider. Expected NOT to compile through bdc today (no cell for divui).
// INPUT RANGE: x any int32 (read as unsigned), base any int32 (read as unsigned; b < 2 means base 10). Trip count
// <= 32 (base 2). Unsigned arithmetic: no UB.
//
//===----------------------------------------------------------------------===//
#include "digitdiv.h"
#include "dynamatic/Integration.h"

int digitdiv(in_int_t x, in_int_t base) {
  unsigned v = (unsigned)x;
  unsigned b = (unsigned)base;
  if (b < 2u)
    b = 10u;
  unsigned s = 0;
  while (v != 0) {
    unsigned q = v / b;
    s = s + (v - q * b);
    v = q;
  }
  return (int)s;
}

int main(void) {
  in_int_t x = 987654321, base = 10;
  CALL_KERNEL(digitdiv, x, base);
  return 0;
}
