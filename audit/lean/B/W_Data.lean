import Formal.Cells.Latch
import Formal.Cells.Bundling
import Formal.Cells.LinkHandshake
/-! Audit (shard B): non-vacuity witnesses for Latch / Bundling / LinkHandshake. -/
open Formal.Cells

namespace AuditB.Data

/-! ### Latch.holds_value / link_latch_holds -/
section L
open Formal.Cells.Latch

def en : Nat → K3 := fun t => if t < 5 then .t else .f
/-- data changes AFTER the close (released value .f from tick 5) -/
def d : Nat → K3 := fun t => if t < 5 then .t else .f
def q : Nat → K3 := fun _ => .t

def bit : LatchBit 1 where
  d := d
  en := en
  p := fun t => q (t - 1)
  d1 := fun _ => .x
  p1 := fun _ => .x
  q := q
  loop := ⟨fun _ => 1, fun _ => Nat.le_refl _, fun _ => Nat.le_refl _⟩
  hlut := by
    intro t
    rw [pair_o5_kleene]
    by_cases h : t < 5
    · simp [en, d, q, h, K3.mux]
    · simp [en, q, h, K3.mux]
  hloop := by intro t _; rfl

/-- all hypotheses of `holds_value` (s = 0, T = 100, v = .t) and of
`link_latch_holds` (tc = 4, E = 1, A = 1, R = 0) hold at once, with data that
changes to .f right at the close. -/
theorem latch_hyps :
    (∀ t, 0 ≤ t → t ≤ 100 → bit.en t ≠ .t → 0 + 1 ≤ t) ∧
    (∀ t, 0 ≤ t → t ≤ 100 → bit.en t ≠ .f → bit.d t = .t) ∧
    (∀ t, 4 + 1 ≤ t → bit.en t = .f) ∧
    (∀ t, t < 4 + 1 + 0 → 0 ≤ t → bit.d t = .t) ∧
    (1 ≤ 1 + 0) ∧ bit.d 50 = .f := by
  refine ⟨?_, ?_, ?_, ?_, by decide, by decide⟩
  · intro t _ _ h
    show 1 ≤ t
    apply Classical.byContradiction; intro h'
    have : t = 0 := by omega
    subst this; exact h rfl
  · intro t _ _ h
    show d t = .t
    by_cases h5 : t < 5
    · simp [d, h5]
    · exfalso; apply h; show en t = .f; simp [en, h5]
  · intro t h; show en t = .f; simp [en]; omega
  · intro t h _; show d t = .t; simp [d]; omega

end L

/-! ### Bundling.capture -/
section B
open Formal.Cells.Bundling

def cEn : Sig := fun t => decide (t < 10)
def cD : Sig := fun t => decide (3 ≤ t ∧ t < 12)
def cQ : Sig := fun t => decide (4 ≤ t)

theorem cQ_transport : Transport ODD [(cD, 1), (cEn, 1), (cQ, 1),
    (zero, 0), (zero, 0), (zero, 0)] cQ := by
  intro t
  show cQ t = lutB ODD [cD (t - 1), cEn (t - 1), cQ (t - 1), false, false, false]
  rw [odd_bin]
  by_cases ht : t < 14
  · revert t; decide
  · have hen : cEn (t - 1) = false := by simp [cEn]; omega
    rw [hen]
    simp only [cQ, Bool.false_eq_true, ↓reduceIte]
    have a1 : 4 ≤ t := by omega
    have a2 : 4 ≤ t - 1 := by omega
    simp [a1, a2]

theorem capture_rel : LatchRel cD cEn cQ 1 1 1 1 1 1 :=
  odd_latch (transport_gate ODD [(cD, 1, 1, 1), (cEn, 1, 1, 1), (cQ, 1, 1, 1),
      (zero, 0, 0, 0), (zero, 0, 0, 0), (zero, 0, 0, 0)] cQ (by simp) cQ_transport)

/-- every hypothesis of `capture` (Ton 0, Toff 10, Tnext 1000, Td 3, Tnew 12,
v = 1, all windows [1,1]) holds; data is NOT constant (0 before 3, released
at 12) and q is not constant. -/
theorem capture_hyps :
    LatchRel cD cEn cQ 1 1 1 1 1 1 ∧
    (∀ t, 0 ≤ t → t < 10 → cEn t = true) ∧
    (∀ t, 10 ≤ t → t < 1000 → cEn t = false) ∧
    (∀ t, 3 ≤ t → t < 12 → cD t = true) ∧
    max (0 + 1) (3 + 1) + 1 ≤ 10 + 1 ∧ 10 + 1 ≤ 12 + 1 ∧
    cD 0 = false ∧ cD 12 = false ∧ cQ 0 = false := by
  refine ⟨capture_rel, ?_, ?_, ?_, by decide, by decide, by decide, by decide, by decide⟩
  · intro t _ h; simp [cEn]; omega
  · intro t h _; simp [cEn]; omega
  · intro t h1 h2; simp [cD]; omega

end B

/-! ### LinkHandshake.latch_capture -/
section LH
open Formal.Cells.LinkHandshake

def lD : Nat → K3 := fun t => if t < 1 then .f else if t < 7 then .t else .f
def lEn : Nat → K3 := fun t => if t < 5 then .t else if t = 5 then .x else .f
def lQ : Nat → K3 := fun t => if t ≤ 1 then .f else .t

theorem lrec : LatchRec 1 1 lD lEn lQ := by
  intro t ht
  by_cases h : t < 12
  · revert ht; revert h; revert t; decide
  · have e1 : lEn t = .f := by
      simp only [lEn, if_neg (show ¬ t < 5 by omega), if_neg (show ¬ t = 5 by omega)]
    rw [e1, latK_shut]
    simp only [lQ, if_neg (show ¬ t + 1 ≤ 1 by omega), if_neg (show ¬ t - 1 ≤ 1 by omega)]

/-- all hypotheses of `latch_capture` (a = 1, c = 5, h = 1, z = 1000, v = 1),
with D changing back to 0 at 7 and Q initially 0. -/
theorem latch_capture_hyps :
    LatchRec 1 1 lD lEn lQ ∧ 1 ≤ 1 ∧ 1 ≤ 1 ∧
    (∀ τ, 1 ≤ τ → τ < 5 → lEn τ = .t) ∧
    (∀ τ, 5 + 1 ≤ τ → τ < 1000 → lEn τ = .f) ∧
    (∀ τ, 1 ≤ τ → τ < 5 + 1 → lD τ = K3.ofBool true) ∧
    1 + 1 + 1 ≤ 5 ∧ lD 8 = .f ∧ lQ 1 = .f := by
  refine ⟨lrec, by decide, by decide, ?_, ?_, ?_, by decide, by decide, by decide⟩
  · intro τ h1 h2; simp only [lEn, if_pos h2]
  · intro τ h1 h2
    simp only [lEn, if_neg (show ¬ τ < 5 by omega), if_neg (show ¬ τ = 5 by omega)]
  · intro τ h1 h2
    simp only [lD, K3.ofBool, if_neg (show ¬ τ < 1 by omega), if_pos (show τ < 7 by omega)]

/-- token conservation / boundedness are about `Reach`, which is inhabited
beyond the reset state: a reachable state with 3 half tokens (author's
`pipe2_full`), and here one after a full send+gate+recv cycle on N = 1. -/
example : ∃ x, LinkHandshake.Reach 1 x 1 1 :=
  ⟨_, Reach.recv (Reach.gate (Reach.send Reach.init (Step.send _ (by decide)))
      (Step.gate _ 1 (by decide) (by decide) (by decide)))
      (Step.recv _ (by decide))⟩

/-- SETUP of `latch_capture`/`setup_iff` is sufficient but not necessary in
general: with the previous token equal to the new one, every other hypothesis
holds, SETUP fails (a + L + F = 7 > 5 = c), and the conclusion still holds. -/
theorem setup_not_necessary :
    LatchRec 1 1 (fun _ => .t) lEn (fun _ => .t) ∧ 1 ≤ 5 ∧
    (∀ τ, 5 ≤ τ → τ < 5 → lEn τ = .t) ∧
    (∀ τ, 5 + 1 ≤ τ → τ < 100 → lEn τ = .f) ∧
    (∀ τ, 5 ≤ τ → τ < 5 + 1 → (fun _ => K3.t) τ = K3.ofBool true) ∧
    ¬ (5 + 1 + 1 ≤ 5) ∧
    (∀ τ, 5 + 1 ≤ τ → τ < 100 + 1 → (fun _ => K3.t) τ = K3.ofBool true) := by
  refine ⟨fun t _ => (latK_keep true (lEn t)).symm, by decide, fun τ h1 h2 => absurd h2 (by omega),
    ?_, fun _ _ _ => rfl, by decide, fun _ _ _ => rfl⟩
  intro τ h1 h2
  simp only [lEn, if_neg (show ¬ τ < 5 by omega), if_neg (show ¬ τ = 5 by omega)]

end LH
end AuditB.Data
#print axioms AuditB.Data.latch_hyps
#print axioms AuditB.Data.capture_hyps
#print axioms AuditB.Data.latch_capture_hyps
#print axioms AuditB.Data.setup_not_necessary
