import Formal.Net.Compute.BitFn
import Formal.Gen.Compute.Xs.Uxori1
import Formal.Gen.Compute.Xs.Uxori2

/-!
# H_COMPUTE_FN for xorshift's xor-shift units `uxori2`, `uxori1`

Problem statement. xorshift's `bdc_fused_uxori2` (bdc Verilog `z = e0 ^ (e0 << 5)`) and
`bdc_fused_uxori1` (`t = e0 ^ (e0 << 13); z = t ^ (t >> 17)`), as yosys synthesized them, compute
those operations for EVERY input (`xs_uxori2_fn`, `xs_uxori1_fn`), stated with the capstone's
`Ops`. Each output bit depends on at most four input bits; `BitFnOK` checks each exhaustively.

Assumed / not covered: LUT semantics (shard A's model); the placed netlist (11g); timing.
-/

namespace Formal.Net.Compute.Xs
open Formal.Net.Compute Formal.Net.GcdHw Formal.Gen.Compute.Xs

/-! ## uxori2 -/

def need2 (i : Nat) : List Nat := if 5 ≤ i then [i, i - 5] else [i]
def f2 (i : Nat) (g : Nat → Bool) : Bool := g i ^^ (decide (5 ≤ i) && g (i - 5))

set_option maxRecDepth 100000 in
theorem x2_ok : BitFnOK Uxori2.cells Uxori2.outs need2 f2 := by decide +kernel

theorem f2_loc : ∀ i g1 g2, (∀ j ∈ need2 i, g1 j = g2 j) → f2 i g1 = f2 i g2 := by
  intro i g1 g2 h
  unfold f2
  by_cases h5 : 5 ≤ i
  · rw [h i (by simp [need2, h5]), h (i - 5) (by simp [need2, h5])]
  · rw [h i (by simp [need2, h5])]; simp [h5]

/-- **xorshift's uxori2 computes `e0 ^ (e0 << 5)`** for every input. -/
theorem xs_uxori2_fn (a : Nat) :
    unitVal Uxori2.cells Uxori2.outs [a] = Ops.xori 32 a (Ops.shli 32 a 5) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_unitVal, show Uxori2.outs.length = 32 from rfl]
  simp only [Ops.xori, Ops.shli, Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_shiftLeft]
  by_cases hi : i < 32
  · simp only [hi, decide_true, Bool.true_and]
    rw [bitFn_bit x2_ok f2_loc _ i hi]
    simp [f2, inEnv]
  · simp [hi]

/-! ## uxori1 -/

def need1 (i : Nat) : List Nat :=
  [i] ++ (if 13 ≤ i then [i - 13] else []) ++ (if i + 17 < 32 then [i + 17, i + 4] else [])
def f1 (i : Nat) (g : Nat → Bool) : Bool :=
  (g i ^^ (decide (13 ≤ i) && g (i - 13))) ^^ (decide (i + 17 < 32) && (g (i + 17) ^^ g (i + 4)))

set_option maxRecDepth 100000 in
theorem x1_ok : BitFnOK Uxori1.cells Uxori1.outs need1 f1 := by decide +kernel

theorem f1_loc : ∀ i g1 g2, (∀ j ∈ need1 i, g1 j = g2 j) → f1 i g1 = f1 i g2 := by
  intro i g1 g2 h
  unfold f1
  rw [h i (by simp [need1])]
  by_cases h13 : 13 ≤ i
  · rw [h (i - 13) (by simp [need1, h13])]
    by_cases h17 : i + 17 < 32
    · rw [h (i + 17) (by simp [need1, h17]), h (i + 4) (by simp [need1, h17])]
    · simp [h17]
  · by_cases h17 : i + 17 < 32
    · rw [h (i + 17) (by simp [need1, h17]), h (i + 4) (by simp [need1, h17])]
      simp [h13]
    · simp [h13, h17]

/-- **xorshift's uxori1 computes `t = e0 ^ (e0 << 13); t ^ (t >> 17)`** for every input. -/
theorem xs_uxori1_fn (a : Nat) :
    unitVal Uxori1.cells Uxori1.outs [a] =
      Ops.xori 32 (Ops.xori 32 a (Ops.shli 32 a 13)) (Ops.shrui 32 (Ops.xori 32 a (Ops.shli 32 a 13)) 17) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_unitVal, show Uxori1.outs.length = 32 from rfl]
  simp only [Ops.xori, Ops.shli, Ops.shrui, Nat.testBit_mod_two_pow, Nat.testBit_xor,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.mod_mod]
  by_cases hi : i < 32
  · simp only [hi, decide_true, Bool.true_and]
    rw [bitFn_bit x1_ok f1_loc _ i hi]
    simp only [f1, inEnv, List.getD_cons_zero]
    by_cases h17 : i + 17 < 32
    · have h4 : 17 + i - 13 = i + 4 := by omega
      simp [h17, show 17 + i < 32 by omega, show 13 ≤ 17 + i by omega, h4, Nat.add_comm 17 i]
    · simp [h17, show ¬ (17 + i < 32) by omega]
  · simp [hi]

end Formal.Net.Compute.Xs
