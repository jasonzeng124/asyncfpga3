import Formal.Cells.CovUp
import Formal.Net.TimedOccDecX

/-!
# Formal.Cells.CovUpDec — Boolean checker for `CovUp.CovTimeU` (shard B, 2026-11-09)

`covTimeUB Sep Up c w hi lo`: C's `TimedDecX.covTimeB` start test, or the upper-bound start test
(`Up c.A w.A = some u`, `1 ≤ hi + w.a`, `hi + w.a + u ≤ c.a`); end test as C's. `covTimeU_of_B`: sound. Core Lean.
-/

namespace Formal.Cells.CovUpDec
open Formal.Net.OccNet.TimedX Formal.Net.OccNet.TimedDecX Formal.Cells.CovUp

variable {α : Type} [DecidableEq α]

def covTimeUB (Sep : α → Nat → α → Nat → Option Nat) (Up : α × Nat → α × Nat → Option Nat) (c w : Claim α)
    (hiZ loZ : Nat) : Bool :=
  (match w.A with
    | none => true
    | some e' => match c.A with
      | none => false
      | some e => (match Sep e'.1 e'.2 e.1 e.2 with
          | some d => decide ((hiZ : Int) + w.a ≤ c.a + d)
          | none => false) ||
        (match Up e e' with
          | some u => decide (1 ≤ (hiZ : Int) + w.a) && decide ((hiZ : Int) + w.a + u ≤ c.a)
          | none => false)) &&
  (match w.B with
    | none => true
    | some e' => match c.B with
      | none => false
      | some e => match Sep e.1 e.2 e'.1 e'.2 with
        | some d => decide (c.b ≤ loZ + w.b + d)
        | none => false)

theorem covTimeU_of_B (Sep : α → Nat → α → Nat → Option Nat) (Up : α × Nat → α × Nat → Option Nat)
    (c w : Claim α) (hiZ loZ : Nat) (h : covTimeUB Sep Up c w hiZ loZ = true) : CovTimeU Sep Up c w hiZ loZ := by
  unfold covTimeUB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  unfold CovTimeU
  constructor
  · revert h1
    cases w.A with
    | none => intro _; trivial
    | some e' =>
      cases c.A with
      | none => intro h1; simp at h1
      | some e =>
        intro h1
        simp only [Bool.or_eq_true] at h1
        rcases h1 with h1 | h1
        · exact Or.inl ⟨e, rfl, opt_dec h1⟩
        · right
          cases hu : Up e e' with
          | none => rw [hu] at h1; cases h1
          | some u =>
            rw [hu] at h1
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
            exact ⟨e, rfl, u, hu, h1.1, h1.2⟩
  · revert h2
    cases w.B with
    | none => intro _; trivial
    | some e' =>
      cases c.B with
      | none => intro h2; simp at h2
      | some e => intro h2; exact ⟨e, rfl, opt_dec h2⟩

/-- Toy: the claim is anchored at `(0, 0)` with offset 30; a cover starts at `(1, 0)` + 2, at most 20 after the anchor
(`Up`), read through a pin with hi = 5: 5 + 2 + 20 ≤ 30. -/
example : CovTimeU (fun _ _ _ _ => none) (fun e e' => if e = (0, 0) ∧ e' = (1, 0) then some 20 else none)
    (⟨7, true, some (0, 0), 30, none, 0⟩ : Claim Nat) ⟨8, true, some (1, 0), 2, none, 0⟩ 5 1 :=
  covTimeU_of_B _ _ _ _ _ _ (by decide)

end Formal.Cells.CovUpDec
