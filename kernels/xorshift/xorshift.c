//===- xorshift.c - Marsaglia's xorshift32 generator --------------*- C -*-===//
//
// WHY THIS KERNEL
//
// Pure unsigned bit-mixing: three xors, two left shifts and one *logical*
// right shift per round, and nothing else. gcd emits no `xori` at all and
// its only right shifts are arithmetic (`shrsi`), so the unsigned shift path
// and the xor path have never been built into a bitstream.
//
// It is also a self-tightening test of the bundled-data delay lines in a way
// arithmetic is not: xorshift is chosen precisely so that every output bit
// depends on many input bits, so a delay line that is short by one LUT
// corrupts the answer visibly instead of surviving on unused high bits.
//
//===----------------------------------------------------------------------===//

#include "xorshift.h"
#include "dynamatic/Integration.h"

int xorshift(in_int_t seed, in_int_t rounds) {
  unsigned x = (unsigned)seed;
  int i = 0;

  while (i < rounds) {
    x = x ^ (x << 13);
    x = x ^ (x >> 17);
    x = x ^ (x << 5);
    i = i + 1;
  }

  return (int)x;
}

int main(void) {
  in_int_t seed = 2463534242;
  in_int_t rounds = 4;
  CALL_KERNEL(xorshift, seed, rounds);
  return 0;
}
