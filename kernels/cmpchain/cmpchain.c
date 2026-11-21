//===- cmpchain.c - a chain of compares ----------------------------*- C -*-===//
//
// SUITE KERNEL (2026-11-17; research/PROGRAM.md "A benchmark suite for the compiler"; kernels/SUITE.md).
// SHAPE: a chain of compares -- an if / else-if ladder of seven tests: eq, signed lt (twice, one an && of two),
// unsigned gt, signed ge against a constant, unsigned le against a constant. No loop.
// EXERCISES: cmpi with every common predicate, signed and unsigned, and the select / steer tree the ladder becomes.
// The class goes in the top four bits of the result and x - y in the rest, so a wrong class or a wrong operand both
// show. Each class 1 .. 7 is reachable (vectors: kernels/cmpchain/vec.hex has at least one of each).
// INPUT RANGE: every (x, y) in int32 x int32. x - y is computed unsigned: no UB.
//
//===----------------------------------------------------------------------===//
#include "cmpchain.h"
#include "dynamatic/Integration.h"

int cmpchain(in_int_t x, in_int_t y) {
  unsigned ux = (unsigned)x, uy = (unsigned)y;
  unsigned r;
  if (x == y)
    r = 1u;
  else if (x < 0 && y < 0)
    r = 2u;
  else if (x < y)
    r = 3u;
  else if (ux > uy)
    r = 4u;
  else if (x >= 1000000)
    r = 5u;
  else if (ux <= 255u)
    r = 6u;
  else
    r = 7u;
  return (int)((r << 28) ^ (ux - uy));
}

int main(void) {
  in_int_t x = 1000, y = -9;
  CALL_KERNEL(cmpchain, x, y);
  return 0;
}
