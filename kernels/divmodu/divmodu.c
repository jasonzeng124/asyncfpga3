//===- divmodu.c - unsigned division and remainder, no loop -----------*- C -*-===//
//
// SUITE KERNEL (2026-11-18; research/PROGRAM.md lead 4 "division and modulo"; kernels/SUITE.md).
// SHAPE: division / modulo by a variable divisor, unsigned, straight-line: q = a / b and r = a % b, returned as
// q + 2 * r (mod 2^32). Built through BDC_FE_UREM=1 (bdc/frontend.sh: Dynamatic has no remui), r is a - q * b on
// the same divider, and the result is 2a + q * (1 - 2b): 1 - 2b is odd, so every wrong quotient changes the result.
// The vectors reach what digitsum / digitdiv cannot: divisor 1 and 0xffffffff, dividend 0 and below the divisor.
// INPUT RANGE: a any uint32; b any uint32 except 0 (C: division by zero is undefined). Unsigned arithmetic: no UB.
//
//===----------------------------------------------------------------------===//
#include "divmodu.h"
#include "dynamatic/Integration.h"

int divmodu(in_int_t a, in_int_t b) {
  unsigned x = (unsigned)a;
  unsigned y = (unsigned)b;
  unsigned q = x / y;
  unsigned r = x % y;
  return (int)(q + 2u * r);
}

int main(void) {
  in_int_t a = 987654321, b = 10;
  CALL_KERNEL(divmodu, a, b);
  return 0;
}
