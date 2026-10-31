// gcd as Dynamatic compiles it (binary / Stein gcd), RECONSTRUCTED on 2026-10-31 (shard C)
// from the generated formal/lean/Formal/Net/AutoGcd.lean of probe C-vk2, whose source file
// was never committed. C-vk2 wrote it from the committed CF-level MLIR
// (cloud/fixtures/frontend/gcd/comp/cf_transformed.mlir), block by block, as the hand gcdC
// was, because Dynamatic's gcd.c is not in the repo. So for gcd the C side is NOT independent
// of the compiler front end. Lines 17-34 reproduce the test-point lines quoted in AutoGcd.lean;
// the regenerated AutoGcd.lean is byte-identical to C-vk2's (checked when committed).
// Loops forever on some negative inputs (e.g. (-2,-1)), as the hand gcdC does.
#include "gcd.h"
//
//
//
//
//
//
int gcd(in_int_t a, in_int_t b) {
  if (a == 0) return b;                          // bb0
  if (b == 0) return a;                          // bb1
  int k = 0;
  while (((a | b) & 1) == 0) {                   // bb2 / bb3
    a = a >> 1;
    b = b >> 1;
    k = k + 1;
  }
  while (!((a & 1) != 0 || a < 1)) a = a >> 1;   // bb5
  while (!((b & 1) != 0 || b < 1)) b = b >> 1;   // bb7
  if (a == 0) return b << k;                     // bb8 -> bb12
  int d;
  do {
    d = a - b; d = d > -1 ? d : -d;
    while (!((d & 1) != 0 || d < 1)) d = d >> 1; // bb11
    b = a < b ? a : b;
    a = d;
  } while (a != 0);
  return b << k;
}
