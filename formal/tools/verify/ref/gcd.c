// C reference for gcd_hw (probe C-vk, formal/tools/verify).
//
// WHY THIS FILE EXISTS: there is no kernels/gcd/gcd.c in this repository. gcd_hw is
// compiled from Dynamatic's binary-gcd test (cells/hw/uniform_oracle.py cites
// build/frontend/gcd/comp/gcd.c, which is not committed). verify.sh needs a C
// reference that is NOT derived from the circuit or from the MLIR, so this is the
// textbook Euclid algorithm: a different algorithm from the binary gcd the hardware
// runs, which makes agreement meaningful. It is a reference only on the domain
// verify.sh uses for gcd: 0 <= a, b < 2^31 (where Formal.Net.GcdHwNat proves the
// hardware's C function equals Nat.gcd; Euclid also equals Nat.gcd there).

#include "gcd.h"

int gcd(in_int_t a, in_int_t b) {
  while (b != 0) {
    int t = a % b;
    a = b;
    b = t;
  }
  return a;
}
