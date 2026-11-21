import Formal.Net.Compute.GcdUselect1

/-!
# H_COMPUTE_FN for gcd_hw's `uselect1`: composition (certificates in `GcdUselect1.lean`)
-/

namespace Formal.Net.Compute.GcdD
open Formal.Net.Compute Formal.Net.GcdHw Formal.Gen.Compute.GcdD

theorem word_testBit (x : Nat) : word (fun i => x.testBit i) 32 = x % 2 ^ 32 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_word, Nat.testBit_mod_two_pow]

theorem bit31_lt (y : Nat) (hy : y < 2 ^ 32) : decide (2147483647 < y) = y.testBit 31 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  simp only [decide_eq_decide]
  have : y / 2 ^ 31 < 2 := by apply (Nat.div_lt_iff_lt_mul (by decide)).mpr; omega
  constructor
  · intro h
    have : 1 ≤ y / 2 ^ 31 := (Nat.le_div_iff_mul_le (by decide)).mpr (by omega)
    omega
  · intro h
    have h2 : y / 2 ^ 31 % 2 = y / 2 ^ 31 := Nat.mod_eq_of_lt this
    rw [h2] at h
    have := (Nat.le_div_iff_mul_le (show 0 < 2 ^ 31 by decide)).mp (show 1 ≤ y / 2 ^ 31 by omega)
    omega

/-- The real net values of uselect1 on inputs `a, b`. -/
def R1 (a b : Nat) : Nat → Bool := run (inEnv [a, b]) [] Uselect1.cells (fun _ => false)

/-- The difference word read from the difference nets. -/
def D1 (a b : Nat) : Nat := word (fun i => R1 a b (dN.getD i 0)) 32

theorem hsub (a b i : Nat) (hi : i < 32) :
    R1 a b (dN.getD i 0) = (a % 2 ^ 32 + (2 ^ 32 - 1 - b % 2 ^ 32) + 1).testBit i := by
  have hs := rip_sound sub_ok (inEnv [a, b]) i hi
  have ha : opVal (cutEnv (inEnv [a, b]) Uselect1.cells) (fun i => .inp 0 i) = a % 2 ^ 32 := by
    rw [← word_testBit]; rfl
  have hb : opVal (cutEnv (inEnv [a, b]) Uselect1.cells) (fun i => .inp 1 i) = b % 2 ^ 32 := by
    rw [← word_testBit]; rfl
  exact hs.trans (by simp only [subRip, comp32, ha, hb]; rfl)

set_option maxRecDepth 100000 in
theorem hD (a b : Nat) : D1 a b = Ops.subi 32 a b := by
  apply Nat.eq_of_testBit_eq; intro i
  unfold D1
  rw [testBit_word, Ops.subi, Nat.testBit_mod_two_pow]
  by_cases hi : i < 32
  · simp only [hi, decide_true, Bool.true_and]
    rw [hsub a b i hi]
    have hbl := Nat.mod_lt b (show 0 < 2 ^ 32 by decide)
    rw [show a % 2 ^ 32 + (2 ^ 32 - 1 - b % 2 ^ 32) + 1 = a % 2 ^ 32 + 2 ^ 32 - b % 2 ^ 32 by omega]
  · simp [hi]

theorem hneg (a b i : Nat) (hi : i < 32) :
    R1 a b (nN.getD i 0) = (Ops.subi 32 0 (D1 a b)).testBit i := by
  have hn := rip_sound neg_ok (inEnv [a, b]) i hi
  have hw : opVal (cutEnv (inEnv [a, b]) Uselect1.cells) (fun i => .cut (dN.getD i 0)) = D1 a b := rfl
  have hDl : D1 a b < 2 ^ 32 := word_lt _ 32
  have e : R1 a b (nN.getD i 0) = (2 ^ 32 - 1 - D1 a b + 0 + 1).testBit i :=
    hn.trans (by simp only [negRip, comp32, hw]; rfl)
  rw [e, Ops.subi, Nat.zero_mod, Nat.zero_add, Nat.mod_eq_of_lt hDl,
    show 2 ^ 32 - 1 - D1 a b + 0 + 1 = 2 ^ 32 - D1 a b by omega, Nat.testBit_mod_two_pow]
  simp [hi]

set_option maxRecDepth 100000 in
theorem hd31 (a b : Nat) : R1 a b 138 = (D1 a b).testBit 31 := by
  unfold D1; rw [testBit_word]; rfl

set_option maxRecDepth 100000 in
theorem h174 (a b : Nat) : R1 a b 174 = !((D1 a b).testBit 31) := by
  obtain ⟨c1, c2, c3⟩ := cmp_ok
  obtain ⟨d1, d2, d3⟩ := and140_ok
  have hv : R1 a b 174 = (!(R1 a b 140) && !(R1 a b 138)) := cert_val Uselect1.nodup c1 c2 c3 _
  have hv2 : R1 a b 140 = [R1 a b 134, R1 a b 135, R1 a b 136, R1 a b 137, R1 a b 138,
      R1 a b 139].all id := cert_val Uselect1.nodup d1 d2 d3 _
  rw [hv, hv2, hd31]
  cases (D1 a b).testBit 31 <;> simp

theorem bit31_sgt (y : Nat) (hy : y < 2 ^ 32) :
    Ops.cmpi .sgt 32 y 4294967295 = if y.testBit 31 then 0 else 1 := by
  simp only [Ops.cmpi, Ops.b2n]
  have hf : Ops.flip 32 4294967295 = 2147483647 := by decide
  rw [hf]
  have hy' : Ops.flip 32 y < 2 ^ 32 := Nat.mod_lt _ (by decide)
  rw [bit31_lt _ hy', flip_bit y 31 (by decide)]
  simp only [tog, if_true]
  cases y.testBit 31 <;> rfl

set_option maxRecDepth 100000 in
/-- **uselect1 computes `d = e0 - e1; (d > -1) ? d : 0 - d`** for every `a, b`. -/
theorem uselect1_fn (a b : Nat) :
    unitVal Uselect1.cells Uselect1.outs [a, b] =
      Ops.select (Ops.cmpi .sgt 32 (Ops.subi 32 a b) 4294967295) (Ops.subi 32 a b)
        (Ops.subi 32 0 (Ops.subi 32 a b)) := by
  rw [← hD a b]
  have hDl : D1 a b < 2 ^ 32 := word_lt _ 32
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_unitVal, show Uselect1.outs.length = 32 from rfl, bit31_sgt _ hDl, Ops.select]
  by_cases hi : i < 32
  · simp only [hi, decide_true, Bool.true_and]
    obtain ⟨hw, m1, m2, m3⟩ := mux_ok i hi
    have hv : R1 a b (outNet Uselect1.outs i) =
        (if R1 a b 174 then R1 a b (dN.getD i 0) else R1 a b (nN.getD i 0)) :=
      cert_val Uselect1.nodup m1 m2 m3 _
    rw [hw]
    show R1 a b _ = _
    have hdi : R1 a b (dN.getD i 0) = (D1 a b).testBit i := by
      have := testBit_word (fun i => R1 a b (dN.getD i 0)) 32 i
      simp only [hi, decide_true, Bool.true_and] at this
      exact this.symm
    rw [hv, h174, hdi, hneg a b i hi]
    cases (D1 a b).testBit 31 <;> simp
  · simp only [hi, decide_false, Bool.false_and]
    have hsub : Ops.subi 32 0 (D1 a b) < 2 ^ 32 := Nat.mod_lt _ (by decide)
    have h32 : ∀ v, v < 2 ^ 32 → v.testBit i = false := fun v hv =>
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) (by omega)))
    cases (D1 a b).testBit 31 <;> simp [h32 _ hDl, h32 _ hsub]

end Formal.Net.Compute.GcdD
