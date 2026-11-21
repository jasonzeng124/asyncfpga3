import Formal.Net.GcdHwLib

/-!
# Formal.Rewrite.Eq2 — the arithmetic fact behind research's collatz loop-test rewrite (shard A, 2026-11-15)

**Problem, plainly.** research's `pre_eq2.py` replaces collatz's loop test `n' == 1`, where
`n' = (n & 1) == 0 ? n >> 1 : 3 * n + 1` (arithmetic shift, w-bit two's complement), by `n == 2`, so that the compare
reads the loop value instead of the update. Is `n' == 1 ⇔ n == 2` true for every w-bit `n`, including negative
values and wrap-around?

**Proved** (`collatz_eq2`, in the circuit's own op semantics `GcdHw.Ops`, every natural `n`, i.e. every bit
pattern after reduction mod `2^w`): for every width `w ≥ 3`,
`cmpi eq (cmpi ne n' 1) 0 = cmpi eq n 2`. Even `n`: below `2^(w-1)` the shift is `n / 2`, which is 1 exactly for
`n ∈ {2, 3}`; at or above it (negative) the shift stays at or above `2^(w-1)`. Odd `n`: `3n + 1` is even, and so
is its residue mod `2^w`.

**Width matters:** at `w = 2` the fact is false (`n = 2` is `-2`, `-2 >> 1 = -1 ≠ 1`); `w = 32` and `w = 64` are
the widths of collatz and collatz64.
-/

namespace Formal.Rewrite.Eq2
open Formal.Net.GcdHw

theorem eqne1 (w v : Nat) (hw : 2 ≤ w) :
    Ops.cmpi .eq w (Ops.cmpi .ne w v 1) 0 = Ops.b2n (v % 2 ^ w == 1) := by
  have h4 : 4 ≤ 2 ^ w := by
    have : 2 ^ 2 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
    simpa using this
  have one : 1 % 2 ^ w = 1 := Nat.mod_eq_of_lt (by omega)
  by_cases h : v % 2 ^ w = 1
  · simp [Ops.cmpi, Ops.b2n, h, one]
  · simp [Ops.cmpi, Ops.b2n, h, one]

theorem collatz_eq2 (w n : Nat) (hw : 3 ≤ w) :
    Ops.cmpi .eq w (Ops.cmpi .ne w (Ops.select (Ops.cmpi .eq w (Ops.andi w n 1) 0) (Ops.shrsi w n 1)
      (Ops.addi w (Ops.muli w 3 n) 1)) 1) 0 = Ops.cmpi .eq w n 2 := by
  have hp : 2 ^ w = 2 * 2 ^ (w - 1) := by
    rw [show w = (w - 1) + 1 by omega, Nat.pow_succ]; simp; omega
  obtain ⟨H, hH1⟩ : ∃ H, 2 ^ (w - 1) = H := ⟨_, rfl⟩
  rw [hH1] at hp
  have hH4 : 4 ≤ H := by
    have : 2 ^ 2 ≤ 2 ^ (w - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    simp at this; omega
  have d2 : 2 ∣ 2 ^ w := ⟨H, hp⟩
  have m2 : ∀ a, a % 2 ^ w % 2 = a % 2 := fun a => Nat.mod_mod_of_dvd a d2
  have small : ∀ a, a < 2 ^ w → a % 2 ^ w = a := fun a h => Nat.mod_eq_of_lt h
  have hx : n % 2 ^ w < 2 ^ w := Nat.mod_lt _ (by omega)
  have mx := m2 n
  have two : 2 % 2 ^ w = 2 := small 2 (by omega)
  rw [eqne1 w _ (by omega)]
  have rhs : Ops.cmpi .eq w n 2 = Ops.b2n (n % 2 ^ w == 2) := by simp [Ops.cmpi, two]
  rw [rhs]
  congr 1
  have hand : Ops.andi w n 1 = n % 2 := by
    simp only [Ops.andi, Nat.and_one_is_mod]; exact small _ (by omega)
  rw [hand]
  rcases Nat.mod_two_eq_zero_or_one n with he | ho
  · -- even: the shift
    have hs : Ops.cmpi .eq w (n % 2) 0 % 2 = 1 := by simp [Ops.cmpi, Ops.b2n, he]
    simp only [Ops.select, hs, if_true, Ops.shrsi, hH1]
    by_cases hlt : n % 2 ^ w < H
    · rw [if_pos hlt, Nat.shiftRight_eq_div_pow, Nat.pow_one, small _ (by omega)]
      by_cases h2 : n % 2 ^ w = 2
      · rw [h2]; simp
      · have : n % 2 ^ w / 2 ≠ 1 := by omega
        rw [beq_false_of_ne this, beq_false_of_ne h2]
    · rw [if_neg hlt, Nat.shiftRight_eq_div_pow, Nat.pow_one, small _ (by omega)]
      have h1 : 2 ^ w - 1 - (2 ^ w - 1 - n % 2 ^ w) / 2 ≠ 1 := by omega
      have h2 : n % 2 ^ w ≠ 2 := by omega
      rw [beq_false_of_ne h1, beq_false_of_ne h2]
  · -- odd: 3n + 1 is even
    have hs : Ops.cmpi .eq w (n % 2) 0 % 2 = 0 := by simp [Ops.cmpi, Ops.b2n, ho, small 1 (by omega)]
    simp only [Ops.select, hs, Ops.addi, Ops.muli]
    simp only [show ¬ (0 = 1) from by decide, if_false]
    have hev : ((3 * n) % 2 ^ w + 1) % 2 ^ w % 2 = 0 := by
      rw [m2]; have := m2 (3 * n); omega
    have h1 : ((3 * n) % 2 ^ w + 1) % 2 ^ w % 2 ^ w ≠ 1 := by
      rw [Nat.mod_mod]; intro h; rw [h] at hev; simp at hev
    have h2 : n % 2 ^ w ≠ 2 := by omega
    rw [Nat.mod_mod] at h1
    rw [Nat.mod_mod, beq_false_of_ne h1, beq_false_of_ne h2]

end Formal.Rewrite.Eq2
