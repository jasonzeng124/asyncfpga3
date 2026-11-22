//===- sum3.c - three scalar arguments ------------------------------*- C -*-===//
//
// WHY THIS KERNEL (suiteb, 2026-11-17; PROGRAM "A benchmark suite for the compiler"): the bench's operand file was
// two 32-bit words (cells/hw/gen_bench.py MAX_WORDS = 2), so no kernel with a third argument could be run. This is
// the smallest loop with three, each in a different role (start value, xor mask, trip count): a bench that wires
// the third word wrong, or two words in the wrong order, returns a different answer.
//
//===----------------------------------------------------------------------===//
#include "sum3.h"
#include "dynamatic/Integration.h"

int sum3(in_int_t a, in_int_t b, in_int_t n) {
  int s = a;
  for (int i = 0; i < n; i++)
    s = (s ^ b) + i;
  return s;
}

int main(void) {
  in_int_t a = 5;
  in_int_t b = 0x55;
  in_int_t n = 10;
  CALL_KERNEL(sum3, a, b, n);
  return 0;
}
