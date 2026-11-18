import Formal.Rewrite.IncCmpArith

/-!
# Formal.Rewrite.PlainArith — the value facts behind the plain loop test (shard A, 2026-11-18)

`NotMax v := v mod 2^32 ≠ INT_MAX`, `NotMin v := v mod 2^32 ≠ INT_MIN`.
* `xor_eq_plain`: the corrected test equals the plain `slt(i, m)` when `NotMax i` and `NotMax m`.
* `test_true_inc`: if the corrected test is true then `i + 1` is `NotMax` (what the loop sends back is not INT_MAX).
* `sgt_true`: if `sgt(v, w)` is true then `NotMin v` (the guard `n > 0` lets no INT_MIN into the loop).
* `dec_notmax`: `NotMin n → NotMax (n - 1)`; `extui_notmax`: a zero-extended bit is `NotMax`.
-/

namespace Formal.Rewrite.IncCmp

open Formal.Net.GcdHw

def NotMax (v : Nat) : Prop := v % 4294967296 ≠ 2147483647
def NotMin (v : Nat) : Prop := v % 4294967296 ≠ 2147483648

theorem slt_flip (a b : Nat) : Ops.cmpi .slt 32 a b =
    Ops.b2n (decide ((a % 4294967296 + 2147483648) % 4294967296 < (b % 4294967296 + 2147483648) % 4294967296)) := by
  have h32 : (2:Nat) ^ 32 = 4294967296 := rfl
  have h31 : (2:Nat) ^ (32 - 1) = 2147483648 := rfl
  simp only [Ops.cmpi, Ops.flip, h32, h31]

theorem xor_eq_plain (v w : Nat) (hv : NotMax v) (hw : NotMax w) :
    fSltXor.eval [v, w] = fSlt.eval [v, w] := by
  simp only [fSltXor, fSlt, E.eval, BOp.ev, List.getD_cons_zero, List.getD_cons_succ]
  have hbeq : ∀ x y : Nat, (x == y) = decide (x = y) := fun x y => by
    cases h : decide (x = y) <;> simp_all
  have e1 : Ops.cmpi .eq 32 v 2147483647 = 0 := by
    simp only [Ops.cmpi, hbeq]; unfold NotMax at hv
    have : (2147483647 : Nat) % 2 ^ 32 = 2147483647 := by decide
    simp only [this]; simp [Ops.b2n, show (2:Nat)^32 = 4294967296 from rfl, hv]
  have e2 : Ops.cmpi .eq 32 w 2147483647 = 0 := by
    simp only [Ops.cmpi, hbeq]; unfold NotMax at hw
    have : (2147483647 : Nat) % 2 ^ 32 = 2147483647 := by decide
    simp only [this]; simp [Ops.b2n, show (2:Nat)^32 = 4294967296 from rfl, hw]
  rw [e1, e2]
  have hb : Ops.cmpi .slt 32 v w < 2 := by rw [slt_flip]; unfold Ops.b2n; split <;> omega
  generalize Ops.cmpi .slt 32 v w = z at hb ⊢
  simp only [Ops.xori]
  rcases (show z = 0 ∨ z = 1 by omega) with rfl | rfl <;> decide

theorem test_true_inc (v w : Nat) (h : fSltXor.eval [v, w] % 2 = 1) : NotMax (fInc.eval [v]) := by
  rw [← ring_T1_id] at h
  simp only [fSltInc, fInc, E.eval, BOp.ev, List.getD_cons_zero, List.getD_cons_succ] at h ⊢
  rw [slt_flip] at h
  simp only [Ops.addi, show (2:Nat)^32 = 4294967296 from rfl, Nat.mod_mod] at h ⊢
  unfold NotMax
  have ha : (v + 1) % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
  generalize (v + 1) % 4294967296 = a at h ha ⊢
  generalize (w + 1) % 4294967296 = b at h
  intro heq
  have hb : (b + 2147483648) % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
  simp only [Ops.b2n] at h
  split at h
  · rename_i hlt; simp only [decide_eq_true_eq] at hlt; omega
  · simp at h

theorem sgt_true (v w : Nat) (h : Ops.cmpi .sgt 32 v w % 2 = 1) : NotMin v := by
  have h32 : (2:Nat) ^ 32 = 4294967296 := rfl
  have h31 : (2:Nat) ^ (32 - 1) = 2147483648 := rfl
  simp only [Ops.cmpi, Ops.flip, h32, h31, Ops.b2n, Nat.mod_mod] at h
  unfold NotMin
  generalize v % 4294967296 = a at h ⊢
  intro heq; subst heq
  split at h
  · rename_i hlt; simp only [decide_eq_true_eq] at hlt; omega
  · simp at h

theorem dec_notmax (n : Nat) (h : NotMin n) : NotMax (gDec.eval [n]) := by
  simp only [gDec, E.eval, BOp.ev, List.getD_cons_zero, Ops.addi, show (2:Nat)^32 = 4294967296 from rfl]
  unfold NotMin at h; unfold NotMax; omega

theorem extui_notmax (v : Nat) : NotMax (Ops.extui 1 v) := by
  unfold NotMax Ops.extui; have := Nat.mod_lt v (show 0 < 2 ^ 1 by decide); omega

end Formal.Rewrite.IncCmp
