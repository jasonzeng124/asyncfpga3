//===- lfsrfind.c - an early exit: a search with break ------------*- C -*-===//
//
// SUITE KERNEL (2026-11-17; research/PROGRAM.md "A benchmark suite for the compiler"; kernels/SUITE.md).
// SHAPE: an early exit -- a search loop that leaves by `break` when it finds the key, or by its bound.
// EXERCISES: a loop with two exits whose values meet after it (the exit index from either exit), the found test
// before the step so seed == key leaves with 0 iterations.
// The sequence is a maximal 16-bit Galois LFSR (taps 0xB400): from a nonzero seed it visits every nonzero 16-bit
// value once per 65535 steps; from 0 it stays at 0. Returns the step at which the state equals key, or LIMIT.
// INPUT RANGE: seed, key any int32 (only their low 16 bits are used); trip count <= LIMIT = 256. Unsigned: no UB.
// (The range is the routed-GLS budget: the gate simulates ~0.2 us of circuit time per wall second, so the declared
// range keeps trip counts in the hundreds.)
//
//===----------------------------------------------------------------------===//
#include "lfsrfind.h"
#include "dynamatic/Integration.h"

#define LIMIT 256

int lfsrfind(in_int_t seed, in_int_t key) {
  unsigned x = (unsigned)seed & 0xFFFFu;
  unsigned k = (unsigned)key & 0xFFFFu;
  int i;
  for (i = 0; i < LIMIT; i++) {
    if (x == k)
      break;
    x = (x >> 1) ^ ((0u - (x & 1u)) & 0xB400u);
  }
  return i;
}

int main(void) {
  in_int_t seed = 1, key = 0x8000;
  CALL_KERNEL(lfsrfind, seed, key);
  return 0;
}
