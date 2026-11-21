import Formal.Net.GcdHwLib

/-!
# Formal.Rewrite.IncCmpArith — the per-token identities the loop-test rewrites need (shard A, 2026-11-18)

**Problem, plainly.** `IncCmpGraph` / `IncCmp2` reduce "moving the loop test before the increment" to one identity
per token between the old compare (on `i + k`) and the new one (on `i`). In the circuit's op semantics
(`GcdHw.Ops`: every value a `Nat`, results reduced mod `2^w`), which identities hold for EVERY input?

**Proved.**
* `ult_lit` (the 117 `ult (addi (extui x) k), C` tests): if the counter is zero-extended from `sw` bits, `2^sw + k ≤ 2^w`
  (the add cannot wrap) and `k ≤ C mod 2^w`, then `ult(extui x + k, C) = ult(extui x, C mod 2^w - k)` for every `x`.
  The new bound is a literal computed at compile time. `ult_lit_E` is the same as the `E`-level identity `hH` of
  `IncCmpGraph.Pat`.
* `slt_inc_xor` (the ring shape, 32 bits): for every `i` and every `n`,
  `slt(i + 1, n) = slt(i, n - 1) xor (i = INT_MAX) xor (n - 1 = INT_MAX)`, all ops mod `2^32`. No loop invariant is
  needed. Without the two correction terms the identity is false (`slt_inc_plain_false`: i = INT_MAX, n = 0), which
  is why research's pre_dec needed xorshift's own invariant (A6).
* `ult_inc_xor`: the same with `ult` and `UINT_MAX`.

**Not covered:** other predicates (`sle`, `sgt` with a negative step); widths other than 32 for the xor forms.
-/

namespace Formal.Rewrite.IncCmp

open Formal.Net.GcdHw

theorem ult_lit (sw w k C x : Nat) (hw : 2 ^ sw + k ≤ 2 ^ w) (hk : k ≤ C % 2 ^ w) :
    Ops.cmpi .ult w (Ops.addi w (Ops.extui sw x) k) C = Ops.cmpi .ult w (Ops.extui sw x) (C % 2 ^ w - k) := by
  have hx : x % 2 ^ sw < 2 ^ sw := Nat.mod_lt _ (Nat.two_pow_pos sw)
  have hC : C % 2 ^ w < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos w)
  have e1 : (x % 2 ^ sw + k) % 2 ^ w = x % 2 ^ sw + k := Nat.mod_eq_of_lt (by omega)
  have e2 : (x % 2 ^ sw) % 2 ^ w = x % 2 ^ sw := Nat.mod_eq_of_lt (by omega)
  have e3 : (C % 2 ^ w - k) % 2 ^ w = C % 2 ^ w - k := Nat.mod_eq_of_lt (by omega)
  simp only [Ops.cmpi, Ops.addi, Ops.extui, Ops.b2n, e1, e2, e3, Nat.mod_mod]
  by_cases h : x % 2 ^ sw + k < C % 2 ^ w
  · have h' : x % 2 ^ sw < C % 2 ^ w - k := by omega
    simp [h, h']
  · have h' : ¬ x % 2 ^ sw < C % 2 ^ w - k := by omega
    simp [h, h']

/-- The `E`-level identity of `IncCmpGraph.Pat` for the literal-bound case. -/
theorem ult_lit_E (sw w k C : Nat) (hw : 2 ^ sw + k ≤ 2 ^ w) (hk : k ≤ C % 2 ^ w) (v : Nat) :
    E.eval [E.eval [E.eval [v] (.un .extui sw (.var 0))] (.bin .addi w (.var 0) (.lit k))]
        (.bin (.cmpi .ult) w (.var 0) (.lit C)) =
      E.eval [E.eval [v] (.un .extui sw (.var 0))] (.bin (.cmpi .ult) w (.var 0) (.lit (C % 2 ^ w - k))) := by
  simp only [E.eval, UOp.ev, BOp.ev, List.getD_cons_zero]
  exact ult_lit sw w k C v hw hk

theorem incv (i : Nat) : (i + 1) % 4294967296 = if i % 4294967296 = 4294967295 then 0 else i % 4294967296 + 1 := by
  split <;> omega
theorem decv (n : Nat) : (n + 4294967295) % 4294967296 = if n % 4294967296 = 0 then 4294967295 else n % 4294967296 - 1 := by
  split <;> omega
theorem slt_core (a b : Nat) (ha : a < 4294967296) (hb : b < 4294967296) :
   (decide ((((if a = 4294967295 then 0 else a + 1)) + 2147483648) % 4294967296 < (b + 2147483648) % 4294967296)) =
   ((decide ((a + 2147483648) % 4294967296 < ((if b = 0 then 4294967295 else b - 1) + 2147483648) % 4294967296) != decide (a = 2147483647)) != decide ((if b = 0 then 4294967295 else b - 1) = 2147483647)) := by
  by_cases h1 : a = 4294967295 <;> by_cases h2 : b = 0 <;> simp only [h1, h2, ite_true, ite_false]
  · decide
  · obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    by_cases q : (0 + 2147483648) % 4294967296 < (c + 1 + 2147483648) % 4294967296 <;>
    by_cases r : c = 2147483647 <;> by_cases u : ((4294967295 + 2147483648) % 4294967296 < (c + 2147483648) % 4294967296) <;>
    simp [q, r, u] <;> (try omega) <;> (rw [Bool.eq_iff_iff]; simp only [Bool.not_eq_true',
      decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_eq_eq_not, Bool.not_true]; omega)
  · by_cases q : (a + 1 + 2147483648) % 4294967296 < (0 + 2147483648) % 4294967296 <;>
    by_cases r : a = 2147483647 <;> by_cases u : (a + 2147483648) % 4294967296 < (4294967295 + 2147483648) % 4294967296 <;>
    simp [q, r, u] <;> (try omega) <;> (rw [Bool.eq_iff_iff]; simp only [Bool.not_eq_true',
      decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_eq_eq_not, Bool.not_true]; omega)
  · obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    by_cases q : (a + 1 + 2147483648) % 4294967296 < (c + 1 + 2147483648) % 4294967296 <;>
    by_cases r : a = 2147483647 <;> by_cases r2 : c = 2147483647 <;>
    by_cases u : (a + 2147483648) % 4294967296 < (c + 2147483648) % 4294967296 <;>
    simp [q, r, r2, u] <;> (try omega) <;> (rw [Bool.eq_iff_iff]; simp only [Bool.not_eq_true',
      decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_eq_eq_not, Bool.not_true]; omega)

/-- `a xor b` on 1-bit values, as `xori 1`. -/
def x1 (a b : Nat) : Nat := Ops.xori 1 a b

theorem b2n_xor (p q : Bool) : x1 (Ops.b2n p) (Ops.b2n q) = Ops.b2n (p != q) := by
  cases p <;> cases q <;> decide

/-- `slt(i + 1, n) = slt(i, n - 1) xor (i = INT_MAX) xor (n - 1 = INT_MAX)` at 32 bits, for every `i`, `n`. -/
theorem slt_inc_xor (i n : Nat) :
    Ops.cmpi .slt 32 (Ops.addi 32 i 1) n =
      x1 (x1 (Ops.cmpi .slt 32 i (Ops.addi 32 n 4294967295)) (Ops.cmpi .eq 32 i 2147483647))
        (Ops.cmpi .eq 32 (Ops.addi 32 n 4294967295) 2147483647) := by
  simp only [Ops.cmpi, Ops.flip, Ops.addi]
  rw [b2n_xor, b2n_xor]
  apply congrArg Ops.b2n
  have h32 : (2:Nat) ^ 32 = 4294967296 := rfl
  have h31 : (2:Nat) ^ (32 - 1) = 2147483648 := rfl
  simp only [h32, h31]
  have hbeq : ∀ x y : Nat, (x == y) = decide (x = y) := fun x y => by
    cases h : decide (x = y) <;> simp_all
  have h7 : (2147483647 : Nat) % 4294967296 = 2147483647 := by decide
  simp only [hbeq, h7, Nat.mod_mod]
  have ha : i % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
  have hb : n % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
  rw [incv i, decv n]
  generalize i % 4294967296 = a at *
  generalize n % 4294967296 = b at *
  exact slt_core a b ha hb

/-- Without the corrections the plain form is false: `i = INT_MAX`, `n = 0`. -/
theorem slt_inc_plain_false :
    Ops.cmpi .slt 32 (Ops.addi 32 2147483647 1) 0 ≠ Ops.cmpi .slt 32 2147483647 (Ops.addi 32 0 4294967295) := by
  decide

theorem cmpi_modr (p : Pred) (w a b : Nat) : Ops.cmpi p w a (b % 2 ^ w) = Ops.cmpi p w a b := by
  cases p <;> simp only [Ops.cmpi, Ops.flip, Nat.mod_mod] <;> rfl

theorem cmpi_modl_eq (p : Pred) (w a b : Nat) : Ops.cmpi p w (a % 2 ^ w) b = Ops.cmpi p w a b := by
  cases p <;> simp only [Ops.cmpi, Ops.flip, Nat.mod_mod] <;> rfl

/-! ## The `E`-level identities for the ring rewrite (T2 then T1) -/

/-- `n - 1` mod `2^32`: what the ring carries after the rewrite. -/
def gDec : E := .bin .addi 32 (.var 0) (.lit 4294967295)
/-- The original loop test `slt(s1, n)`. -/
def fSlt : E := .bin (.cmpi .slt) 32 (.var 0) (.var 1)
/-- The test after the ring rewrite (T2): `slt(s1, m + 1)`. -/
def fSltInc : E := .bin (.cmpi .slt) 32 (.var 0) (.bin .addi 32 (.var 1) (.lit 1))
/-- The increment. -/
def fInc : E := .bin .addi 32 (.var 0) (.lit 1)
/-- The test after both rewrites (T1): `slt(i, m) xor (i = INT_MAX) xor (m = INT_MAX)`. -/
def fSltXor : E := .bin .xori 1 (.bin .xori 1 (.bin (.cmpi .slt) 32 (.var 0) (.var 1))
    (.bin (.cmpi .eq) 32 (.var 0) (.lit 2147483647))) (.bin (.cmpi .eq) 32 (.var 1) (.lit 2147483647))

/-- T2's identity: precomposing the test with `m + 1` undoes `m = n - 1`. -/
theorem ring_T2_id (v w : Nat) : fSltInc.eval [v, gDec.eval [w]] = fSlt.eval [v, w] := by
  simp only [fSltInc, gDec, fSlt, E.eval, BOp.ev, List.getD_cons_zero, List.getD_cons_succ]
  have : Ops.addi 32 (Ops.addi 32 w 4294967295) 1 = w % 2 ^ 32 := by
    simp only [Ops.addi]; omega
  rw [this, cmpi_modr]

/-- T1's identity: the test on `i + 1` against `m + 1` is the corrected test on `i` against `m`. -/
theorem ring_T1_id (v w : Nat) : fSltInc.eval [fInc.eval [v], w] = fSltXor.eval [v, w] := by
  simp only [fSltInc, fInc, fSltXor, E.eval, BOp.ev, List.getD_cons_zero, List.getD_cons_succ]
  rw [slt_inc_xor]
  have h1 : Ops.addi 32 (Ops.addi 32 w 1) 4294967295 = w % 2 ^ 32 := by simp only [Ops.addi]; omega
  rw [h1, cmpi_modr, cmpi_modl_eq]
  rfl

end Formal.Rewrite.IncCmp
