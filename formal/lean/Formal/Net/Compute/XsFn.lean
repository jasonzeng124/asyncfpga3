import Formal.Net.Compute.XsUnits

/-!
# H_COMPUTE_FN on xorshift: compositions (certificates in `XsUnits.lean`)
-/

namespace Formal.Net.Compute.Xs
open Formal.Net.Compute Formal.Net.GcdHw Formal.Gen.Compute.Xs

set_option maxRecDepth 100000 in
/-- **xorshift's uaddi0 computes `e0 + 1`** for every input. -/
theorem xs_uaddi0_fn (a : Nat) : unitVal Uaddi0.cells Uaddi0.outs [a] = Ops.addi 32 a 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_unitVal, show Uaddi0.outs.length = 32 from rfl, Ops.addi, Nat.testBit_mod_two_pow]
  by_cases hi : i < 32
  · simp only [hi, decide_true, Bool.true_and]
    have hs := rip_sound xa_ok (inEnv [a]) i hi
    have ha : opVal (cutEnv (inEnv [a]) Uaddi0.cells) (fun i => .inp 0 i) = a % 2 ^ 32 := by
      apply Nat.eq_of_testBit_eq; intro j
      simp only [opVal, testBit_word, Nat.testBit_mod_two_pow]; rfl
    have hw : Uaddi0.outs.getD i .c0 = .net (addRip.outs.getD i 0) := by
      match i, hi with
      | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl | 4, _ => rfl | 5, _ => rfl
      | 6, _ => rfl | 7, _ => rfl | 8, _ => rfl | 9, _ => rfl | 10, _ => rfl | 11, _ => rfl
      | 12, _ => rfl | 13, _ => rfl | 14, _ => rfl | 15, _ => rfl | 16, _ => rfl | 17, _ => rfl
      | 18, _ => rfl | 19, _ => rfl | 20, _ => rfl | 21, _ => rfl | 22, _ => rfl | 23, _ => rfl
      | 24, _ => rfl | 25, _ => rfl | 26, _ => rfl | 27, _ => rfl | 28, _ => rfl | 29, _ => rfl
      | 30, _ => rfl | 31, _ => rfl
      | _ + 32, h => exact absurd h (by omega)
    rw [hw]
    show run (inEnv [a]) [] Uaddi0.cells (fun _ => false) (addRip.outs.getD i 0) = _
    rw [hs]
    simp only [addRip, comp32, ha, Bool.toNat_true, Nat.add_zero, if_false, Bool.false_eq_true]
    have e : (a % 2 ^ 32 + 1) % 2 ^ 32 = (a + 1) % 2 ^ 32 := by omega
    have l1 : (a % 2 ^ 32 + 1).testBit i = ((a % 2 ^ 32 + 1) % 2 ^ 32).testBit i := by
      rw [Nat.testBit_mod_two_pow]; simp [hi]
    have l2 : (a + 1).testBit i = ((a + 1) % 2 ^ 32).testBit i := by
      rw [Nat.testBit_mod_two_pow]; simp [hi]
    rw [l1, l2, e]
  · simp [hi]

/-- **xorshift's ucmpi0 computes `e0 > e1` (signed)** for every input. -/
theorem xs_ucmpi0_fn (a b : Nat) :
    unitVal Ucmpi0.cells Ucmpi0.outs [a, b] = Ops.cmpi .sgt 32 a b := by
  have h := sgt_sound xc0_ok [a, b]
  unfold unitVal
  simp only [show Ucmpi0.outs.length = 1 from rfl, word, Nat.zero_or]
  show (if run (inEnv [a, b]) [] Ucmpi0.cells (fun _ => false) 71 then 2 ^ 0 else 0) = _
  rw [h]
  simp only [Ops.cmpi, Ops.b2n, List.getD_cons_zero, List.getD_cons_succ]
  try (by_cases hc : Ops.flip 32 b < Ops.flip 32 a <;> simp [hc])

/-- **xorshift's ucmpi1 computes `e0 < e1` (signed)** for every input. -/
theorem xs_ucmpi1_fn (a b : Nat) :
    unitVal Ucmpi1.cells Ucmpi1.outs [a, b] = Ops.cmpi .slt 32 a b := by
  have h := slt_sound xc1_ok [a, b]
  unfold unitVal
  simp only [show Ucmpi1.outs.length = 1 from rfl, word, Nat.zero_or]
  show (if run (inEnv [a, b]) [] Ucmpi1.cells (fun _ => false) 71 then 2 ^ 0 else 0) = _
  rw [h]
  simp only [Ops.cmpi, Ops.b2n, List.getD_cons_zero, List.getD_cons_succ]
  try (by_cases hc : Ops.flip 32 a < Ops.flip 32 b <;> simp [hc])

end Formal.Net.Compute.Xs
