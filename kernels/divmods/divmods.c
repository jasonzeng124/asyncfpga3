//===- divmods.c - signed division and remainder, no loop -------------*- C -*-===//
//
// SUITE KERNEL (2026-11-18; research/PROGRAM.md lead 4 "division and modulo"; kernels/SUITE.md).
// SHAPE: signed division / modulo by a variable divisor, straight-line: q = a / b (C: truncation toward zero) and
// r = a % b (the dividend's sign), returned as q ^ r. Dynamatic lowers them to divsi and remsi: two dividers, one
// per op, so a wrong bit in either one alone flips the same bit of the result (a sum q + 2r would hide r's sign).
// INPUT RANGE: a, b any int32 except b == 0 and (a, b) == (INT_MIN, -1) (C: undefined, the quotient overflows).
//
//===----------------------------------------------------------------------===//
#include "divmods.h"
#include "dynamatic/Integration.h"

int divmods(in_int_t a, in_int_t b) {
  int q = a / b;
  int r = a % b;
  return (int)((unsigned)q ^ (unsigned)r);
}

int main(void) {
  in_int_t a = -987654321, b = 10;
  CALL_KERNEL(divmods, a, b);
  return 0;
}
