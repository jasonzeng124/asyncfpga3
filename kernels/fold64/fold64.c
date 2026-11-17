//===- fold64.c - 64-bit arithmetic --------------------------------*- C -*-===//
//
// SUITE KERNEL (2026-11-17; research/PROGRAM.md "A benchmark suite for the compiler"; kernels/SUITE.md).
// SHAPE: 64-bit arithmetic -- one i64 argument (the bench's two words, low then high), a 64-bit add with its carry
// across bit 31, 64-bit shifts, xor, an unsigned 64-bit compare and a 64-bit constant; the result is folded to 32.
// EXERCISES: i64 channels and operators on a ring (kernels/collatz64 has the i64 datapath with a shift-and-add body;
// this adds a variable-operand 64-bit add, a 64-bit compare and 64-bit constants), and the high argument word.
// INPUT RANGE: v any int64; trip count = v & 255 (0 .. 255). Unsigned arithmetic: no UB.
//
//===----------------------------------------------------------------------===//
#include "fold64.h"
#include "dynamatic/Integration.h"

int fold64(in_int_t v) {
  unsigned long long x = (unsigned long long)v;
  unsigned long long acc = 0x0123456789ABCDEFull;
  int n = (int)(x & 255u);
  for (int i = 0; i < n; i++) {
    acc = acc + (x ^ (acc << 7));
    if (acc < x)
      acc = acc + (x >> 3);
    x = x ^ (x >> 11);
  }
  return (int)(acc ^ (acc >> 32));
}

int main(void) {
  in_int_t v = 0x1122334455667788ll;
  CALL_KERNEL(fold64, v);
  return 0;
}
