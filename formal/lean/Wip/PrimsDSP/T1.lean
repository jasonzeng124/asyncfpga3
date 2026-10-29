theorem lowmod (r x : Nat) (h : r < 131072) :
    (r + 131072 * x) % 4294967296 = r + 131072 * (x % 32768) := by omega

theorem expand (a0 a1 b0 b1 : Nat) :
    (a0 + 131072 * a1) * (b0 + 131072 * b1)
      = a0 * b0 + 131072 * (a0 * b1 + a1 * b0) + 131072 * (131072 * (a1 * b1)) := by
  grind

example (p : Nat) (x : Int) (h : 0 ≤ x) (h2 : x < 2^47) : (x % 2^48).toNat = x.toNat := by omega
