//===- collatz.c - Collatz stopping time --------------------------*- C -*-===//
//
// Counts the steps of the Collatz (3n+1) iteration needed to bring n to 1.
//
// WHY THIS KERNEL
//
// It is the cheapest kernel whose *running time* is a wild function of its
// input and not of its size: 1 takes 0 steps, 27 takes 111, and there is no
// arithmetic relationship between the two. A synchronous datapath has to
// budget for the worst case it might ever see; a bundled-data one simply
// finishes when it finishes, so the shape of this kernel is the shape of the
// thing the whole backend exists to exploit.
//
// It also reaches op and control shapes gcd never did: a multiply, a
// two-armed if/else *inside* a loop body (rather than gcd's guarded update
// chains), and an accumulator that is live across the branch and so must be
// merged back at the join.
//
//===----------------------------------------------------------------------===//

#include "collatz.h"
#include "dynamatic/Integration.h"

int collatz(in_int_t n) {
  int steps = 0;

  while (n != 1) {
    if ((n & 1) == 0)
      n = n >> 1;
    else
      n = 3 * n + 1;
    steps = steps + 1;
  }

  return steps;
}

int main(void) {
  in_int_t n = 27;
  CALL_KERNEL(collatz, n);
  return 0;
}
