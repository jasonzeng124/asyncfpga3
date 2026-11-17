//===- nested.c - two nested counted loops -------------------------*- C -*-===//
//
// WHY THIS KERNEL (research, 2026-11-17; PROGRAM "General first" item 3): a loop nest. The inner loop's exit feeds
// the outer loop's body, so the automatic path must place storage and size delays on two rings that share a token,
// which no current kernel has. The body is a cheap xor-shift-add so the rings, not the datapath, set the time.
//
//===----------------------------------------------------------------------===//
#include "nested.h"
#include "dynamatic/Integration.h"

int nested(in_int_t a, in_int_t b) {
  int acc = 1;
  for (int i = 0; i < a; i++)
    for (int j = 0; j < b; j++)
      acc = (acc ^ (acc << 3)) + i + j;
  return acc;
}

int main(void) {
  in_int_t a = 5, b = 7;
  CALL_KERNEL(nested, a, b);
  return 0;
}
