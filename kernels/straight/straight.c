//===- straight.c - straight-line arithmetic ----------------------*- C -*-===//
//
// SUITE KERNEL (2026-11-17; research/PROGRAM.md "A benchmark suite for the compiler"; kernels/SUITE.md).
// SHAPE: straight-line arithmetic -- no loop and no branch.
// EXERCISES: one token through a purely combinational graph (add, sub, xor, or, and, shifts by constants): the
// latency of the operators and of the fork / join tree alone, with no ring to amortise it over.
// INPUT RANGE: every (a, b) in int32 x int32. All arithmetic is unsigned, so nothing can overflow (no UB anywhere).
//
//===----------------------------------------------------------------------===//
#include "straight.h"
#include "dynamatic/Integration.h"

int straight(in_int_t a, in_int_t b) {
  unsigned x = (unsigned)a, y = (unsigned)b;
  unsigned s = x + y;
  unsigned d = x - y;
  unsigned t = (s ^ (d << 7)) + (x >> 3) - (y << 2);
  unsigned v = (t ^ (t >> 11)) + 0x9e3779b9u;
  return (int)(v - (s & d) + (x | y));
}

int main(void) {
  in_int_t a = 123456789, b = -987654;
  CALL_KERNEL(straight, a, b);
  return 0;
}
