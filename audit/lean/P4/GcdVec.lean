import Formal.Net.GcdHwNat
open Formal.Net.GcdHw.Gcd
-- edge vectors of the C model vs Nat.gcd (i32 bit patterns)
def vecs : List (Nat × Nat) :=
  [(0,0),(0,5),(5,0),(0,0x7FFFFFFF),(0x7FFFFFFF,0x7FFFFFFF),(0x7FFFFFFF,1),(0x7FFFFFFE,0x40000000),
   (0x40000000,0x40000000),(0x60000000,0x20000000),(12,18),(1,0x7FFFFFFF),(0x7FFFFFFF,0x7FFFFFFE)]
#eval vecs.map fun (a,b) => (a, b, gcdC 200 a b, Nat.gcd a b, gcdC 200 a b == some (Nat.gcd a b))
-- negative i32 inputs: -1, INT_MIN, -6 with 6
#eval [(0xFFFFFFFF,4),(0x80000000,0x80000000),(0xFFFFFFFA,6),(0x80000000,0),(0,0x80000000),(0xFFFFFFFF,0)].map fun (a,b) => (a,b,gcdC 5000 a b)
-- the headline theorem
#check @gcdC_nonneg31
#print axioms gcdC_nonneg31
