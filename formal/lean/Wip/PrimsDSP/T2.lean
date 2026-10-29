#check @Nat.testBit_mod_two_pow
#check @Nat.eq_of_testBit_eq
#check @Nat.mul_mod
#check @Nat.mul_le_mul
#check @Nat.testBit_lt_two_pow
example (f : Fin 4 → Bool) : Decidable (∀ i : Fin 4, f i = true) := inferInstance
example (a b : Nat) (h : a < 2^17) (h2 : b < 2^17) : a * b < 2^34 := by
  have := Nat.mul_le_mul (Nat.le_pred_of_lt h) (Nat.le_pred_of_lt h2)
  omega
example (p : Nat) (hp : p < 2^47) : ((if (p % 2^48 : Nat) < 2^47 then ((p % 2^48 : Nat) : Int) else ((p % 2^48 : Nat) : Int) - 2^48) / 2^17) = ((p / 2^17 : Nat) : Int) := by
  split <;> omega
example (x y : Nat) (h : x * y < 5) : ((x : Int) * (y : Int)) % 2^48 = x*y := by
  have : ((x : Int) * y) = ((x * y : Nat) : Int) := by push_cast; rfl
  omega
