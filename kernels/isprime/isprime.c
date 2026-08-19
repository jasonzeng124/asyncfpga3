//===- isprime.c - Primality by trial division --------------------*- C -*-===//
//
// WHY THIS KERNEL
//
// This is the control-flow kernel. gcd's loops all have exactly one exit and
// its blocks have at most two predecessors, so every `control_merge` in it is
// two-input and every loop leaves by falling out of its own condition. Here
// the outer loop has *two* exits -- the divisibility test returns early from
// inside a nested loop -- so the function's exit block is reached from three
// different places and the merge tree at the end is genuinely wider than
// anything built so far. If bd_merge's exclusive-input requirement is wrong
// for what handshake.merge actually promises, this is the kernel that finds
// out, because it is the first one where two arms could be live.
//
// The modulo is done by shift-and-subtract -- the long-division algorithm a
// divider circuit actually uses -- and NOT by repeated subtraction. That is
// not a style choice. The obvious `while (r >= d) r = r - d;` gets recognised
// by LLVM's loop-idiom pass and folded straight back into a `divui`, which
// this backend has no cell for: the kernel written to avoid needing a divider
// ends up demanding one. Shifting is non-affine, so the idiom matcher leaves
// it alone, and it costs O(log n) per trial instead of O(n/d).
//
//===----------------------------------------------------------------------===//

#include "isprime.h"
#include "dynamatic/Integration.h"

int isprime(in_int_t n) {
  if (n < 2)
    return 0;

  int d = 2;
  while (d * d <= n) {
    // r = n mod d, by shift-and-subtract long division.
    int r = n;
    int s = d;
    int half = n >> 1;
    while (s <= half)
      s = s << 1;
    while (s >= d) {
      if (r >= s)
        r = r - s;
      s = s >> 1;
    }

    if (r == 0)
      return 0;

    d = d + 1;
  }

  return 1;
}

int main(void) {
  in_int_t n = 97;
  CALL_KERNEL(isprime, n);
  return 0;
}
