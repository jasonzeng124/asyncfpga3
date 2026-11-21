//===- brhash.c - a branch inside a loop that survives if-conversion -*- C -*-===//
//
// SUITE KERNEL (2026-11-17; research/PROGRAM.md "A benchmark suite for the compiler"; kernels/SUITE.md).
// SHAPE: a branch inside a loop that if-conversion cannot remove. Each arm is several dependent operations, more
// than LLVM's simplifycfg will speculate, so the body stays two basic blocks and the handshake graph keeps a cond_br
// per live value in the loop body (checked in comp/handshake_transformed.mlir: no select), not a select.
// EXERCISES: a data-dependent steer inside a ring: per iteration only one arm fires, and the merge after it must
// take whichever arm's token arrives. (kernels/collatz's two arms are cheap enough to be if-converted.)
// INPUT RANGE: x any int32; n <= 256 (any negative n is 0 trips). Unsigned arithmetic: no UB.
// (The range is the routed-GLS budget: the gate simulates ~0.2 us of circuit time per wall second, so the declared
// range keeps trip counts in the hundreds.)
//
//===----------------------------------------------------------------------===//
#include "brhash.h"
#include "dynamatic/Integration.h"

int brhash(in_int_t x, in_int_t n) {
  unsigned h = (unsigned)x;
  for (int i = 0; i < n; i++) {
    if (h & 1u) {
      h = (h >> 1) ^ 0xEDB88320u;
      h = h + (h << 4) + (unsigned)i;
      h = h ^ (h >> 13);
    } else {
      h = h ^ (h << 9);
      h = (h >> 2) + (unsigned)(i << 1);
      h = h ^ (h << 5) ^ 0x2545F491u;
    }
  }
  return (int)h;
}

int main(void) {
  in_int_t x = 12345, n = 64;
  CALL_KERNEL(brhash, x, n);
  return 0;
}
