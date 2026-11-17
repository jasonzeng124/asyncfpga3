//===- branchloop.c - a branch whose arm holds a loop --------------*- C -*-===//
//
// WHY THIS KERNEL (research, 2026-11-17; PROGRAM "General first" item 3): a branch that survives if-conversion,
// because one arm contains a loop. Odd n: strip the run of trailing ones with an inner loop, then add one; even n:
// halve. Terminates for every n > 0 (each outer step lowers the bit length or clears trailing ones); n <= 1 returns 0.
//
//===----------------------------------------------------------------------===//
#include "branchloop.h"
#include "dynamatic/Integration.h"

int branchloop(in_int_t n) {
  int steps = 0;
  while (n > 1) {
    if (n & 1) {
      while ((n & 3) == 3) {
        n = n >> 1;
        steps = steps + 1;
      }
      n = n + 1;
    } else {
      n = n >> 1;
    }
    steps = steps + 1;
  }
  return steps;
}

int main(void) {
  in_int_t n = 1023;
  CALL_KERNEL(branchloop, n);
  return 0;
}
