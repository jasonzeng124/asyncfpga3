//===- digitsum.c - division and modulo ----------------------------*- C -*-===//
//
// SUITE KERNEL (2026-11-17; research/PROGRAM.md "A benchmark suite for the compiler"; kernels/SUITE.md).
// SHAPE: division / modulo -- v % b and v / b by a variable divisor, in a loop whose trip count is the number of
// base-b digits of v. Dynamatic's frontend stops at its `%` (no remui in its handshake dialect); with
// BDC_FE_UREM=1 bdc/frontend.sh rewrites it as v - (v / b) * b and bdc builds the divider (research/data/suite/divmod.md).
// INPUT RANGE: x any int32 (read as unsigned), base any int32 (read as unsigned; b < 2 means base 10, so there is
// no division by 0 and no 1-ary loop). Trip count <= 32 (base 2). Unsigned arithmetic: no UB.
//
//===----------------------------------------------------------------------===//
#include "digitsum.h"
#include "dynamatic/Integration.h"

int digitsum(in_int_t x, in_int_t base) {
  unsigned v = (unsigned)x;
  unsigned b = (unsigned)base;
  if (b < 2u)
    b = 10u;
  unsigned s = 0;
  while (v != 0) {
    s = s + v % b;
    v = v / b;
  }
  return (int)s;
}

int main(void) {
  in_int_t x = 987654321, base = 10;
  CALL_KERNEL(digitsum, x, base);
  return 0;
}
