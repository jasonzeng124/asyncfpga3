//===- ipow.c - Integer power by binary exponentiation ------------*- C -*-===//
//
// WHY THIS KERNEL
//
// It is the shortest kernel that forces two *variable x variable* multiplies.
// Every multiply gcd or collatz contains is by a literal, and
// --arith-reduce-strength rewrites those into shifts and adds before the
// backend ever sees them -- so no kernel in the shipped suite has ever made
// this backend emit a real `muli`. Both multiplies here have two live
// operands and survive that pass.
//
// The loop also runs in log2(e) steps rather than e steps, so its latency
// tracks the *bit length* of an input rather than its value -- a different
// shape of data dependence than collatz's.
//
//===----------------------------------------------------------------------===//

#include "ipow.h"
#include "dynamatic/Integration.h"

int ipow(in_int_t b, in_int_t e) {
  int r = 1;

  while (e > 0) {
    if ((e & 1) == 1)
      r = r * b;
    b = b * b;
    e = e >> 1;
  }

  return r;
}

int main(void) {
  in_int_t b = 3;
  in_int_t e = 7;
  CALL_KERNEL(ipow, b, e);
  return 0;
}
