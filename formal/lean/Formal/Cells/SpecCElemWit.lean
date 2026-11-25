import Formal.Cells.SpecCElemFact
import Formal.Cells.ArbTSpec

/-!
# Formal.Cells.SpecCElemWit — `celem_forced'` is not vacuous: a concrete C-element run meeting every hypothesis

Shard B, THE goal, S3.

## Problem, plainly
Are the hypotheses of `SpecCElem.celem_forced'` (collapsed gate relation, INIT facts, the timed DI environment
`hA`, the loop race, the separation input, the quiet start) satisfiable together by a behaviour in which the
C-element actually switches? A theorem whose hypotheses only hold for a node that never toggles says nothing.

## Result
A 3-pin gate (INIT 0xE8 = majority = C(a, b) with feedback on pin 2), every arc `ArbTSpec.e1` (1 ps, so the
Spec delay parameters `ArbTSpec.p1` at corner 1 force every read delay to 1 ps); `a` is a square wave of period
20 ps, `b` = `a` delayed by 3 ps, `q` = `b` delayed by 1 ps. `wit_gate`: the collapsed relation holds;
`wit_hA`: the environment hypothesis holds with Δ = 6 (input a) and 9 (input b); `wit_forced`: hence (by
`celem_forced'`) every toggle from 5 ps on is forced; `wit_toggles`: q toggles at 14 ps (so the conclusion is
not about an empty set of toggles), and `wit_toggle_14` is its instance. Standard axioms only.

## Not covered
The run is periodic and ideal (unit delays, no skew); it shows consistency of the hypotheses, nothing about the
target.
-/

namespace Formal.Cells.SpecCElemWit

open Formal.Target Formal.Timing.SpecChain Formal.Cells.SpecFbChain Formal.Cells.SpecCElem
  Formal.Cells.SpecCElemFact
open Formal.Cells.ArbTSpec (p1 e1 adm_e1)

def A : Sig := fun t => decide ((t / 10) % 2 = 1)
def Bs : Sig := fun t => A (t - 3)
def Q : Sig := fun t => Bs (t - 1)

def x : Beh := fun n => if n = 0 then A else if n = 1 then Bs else Q

def gC : Gate := ⟨"C", 3, 0xE8, [0, 1, 2], [e1, e1, e1], 2⟩

def arcs : Nat → List Arc := fun _ => [e1]

theorem sumAdm_e1 (D : Nat) : SumAdm p1 1 [e1] D ↔ D = 1 := by
  simp only [SumAdm]
  constructor
  · rintro ⟨d, hd, hdD, h0⟩
    rw [adm_e1] at hd; omega
  · intro h; exact ⟨1, (adm_e1 1).2 rfl, by omega, by omega⟩

theorem bands : CBands p1 1 gC.k arcs (fun _ => 1) (fun _ => 1) := by
  intro i _ D hD
  rw [arcs, sumAdm_e1] at hD; subst hD; exact ⟨le_rfl, le_rfl⟩

theorem maj (a b c : Bool) :
    (0xE8 : Nat).testBit (addr 3 fun i => if i = 0 then a else if i = 1 then b else c) =
      (a && b || a && c || b && c) := by
  cases a <;> cases b <;> cases c <;> decide

theorem A_eq (t : Nat) : A t = decide ((t / 10) % 2 = 1) := rfl

theorem wit_gate : CGateOK p1 1 gC (fun i => i) arcs 1 x := by
  refine ⟨fun _ t => t - 1, fun _ _ _ _ h => Nat.sub_le_sub_right h 1, fun t ht => ⟨fun i _ => ?_, ?_⟩⟩
  · show t - 1 ≤ t ∧ SumAdm p1 1 (arcs i) (t - (t - 1))
    exact ⟨by omega, (sumAdm_e1 _).2 (by omega)⟩
  · have hx : (fun i => x i (t - 1)) = fun i => if i = 0 then A (t - 1) else if i = 1 then Bs (t - 1) else
        Q (t - 1) := by
      funext i; simp only [x]; split <;> [rfl; split <;> rfl]
    show x 2 t = (0xE8 : Nat).testBit (addr 3 fun i => x i (t - 1))
    rw [hx, maj]
    simp only [x, Q, Bs, A_eq, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, ite_false]
    by_cases h1 : ((t - 1 - 3) / 10) % 2 = 1 <;> by_cases h2 : ((t - 1) / 10) % 2 = 1 <;>
      by_cases h3 : ((t - 1 - 1 - 3) / 10) % 2 = 1 <;> simp [h1, h2, h3] <;> omega

theorem wit_hA : ∀ i, i < gC.k → i ≠ 2 → fl [true, true, false] i = true → ∀ τ, 5 ≤ τ + 1 →
    (x i (τ - 1) ^^ fl [false, false, false] i) ≠ (x i τ ^^ fl [false, false, false] i) →
    ∀ s, τ - (fun i => if i = 0 then 6 else 9) i ≤ s → s ≤ τ →
      x 2 s = (x i (τ - 1) ^^ fl [false, false, false] i) := by
  intro i hi hij hci τ _ htog s hs1 hs2
  have hk : gC.k = 3 := rfl
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  · simp only [x, Q, Bs, A_eq, fl, List.getD, ite_true, Bool.xor_false, ne_eq, show (2 : Nat) ≠ 0 by decide,
      show (2 : Nat) ≠ 1 by decide, ite_false, decide_eq_decide] at htog hs1 ⊢
    by_cases h1 : ((τ - 1) / 10) % 2 = 1 <;> by_cases h2 : (τ / 10) % 2 = 1 <;>
      by_cases h3 : ((s - 1 - 3) / 10) % 2 = 1 <;> simp_all <;> omega
  · simp only [x, Q, Bs, A_eq, fl, List.getD, ite_true, Bool.xor_false, ne_eq, show (1 : Nat) ≠ 0 by decide,
      show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, ite_false, decide_eq_decide] at htog hs1 ⊢
    by_cases h1 : ((τ - 1 - 3) / 10) % 2 = 1 <;> by_cases h2 : ((τ - 3) / 10) % 2 = 1 <;>
      by_cases h3 : ((s - 1 - 3) / 10) % 2 = 1 <;> simp_all <;> omega

theorem wit_fact : cfact 3 0xE8 2 (fl [true, true, false]) (fl [false, false, false]) (fl [false, false, false]) =
    true := by decide

/-- **Every toggle of the witness C-element from 5 ps on is forced** (by `celem_forced'`). -/
theorem wit_forced : ∀ t, 5 ≤ t → Tog (x gC.out) t →
    (∀ i, i < gC.k → i ≠ 2 → fl [true, true, false] i = true →
      ∃ r, r + 1 ≤ t ∧ t ≤ r + 1 ∧ (x i r ^^ fl [false, false, false] i) = x gC.out t) ∧
    (∀ u, u < t → t < u + 1 → ¬ Tog (x gC.out) u) :=
  celem_forced' wit_gate bands (j := 2) (by decide) rfl le_rfl (fl [true, true, false]) (fl [false, false, false])
    (fl [false, false, false]) (fun i => if i = 0 then 6 else 9) 1 1 5 (by decide)
    (fun _ _ => le_rfl) le_rfl (fun _ _ _ _ => le_rfl)
    (fun i _ _ _ => by split <;> omega) 0 (by decide) (by decide) (by decide) (by decide)
    (hall_of_cfact wit_fact) (hhold_of_cfact wit_fact (by decide))
    (fun i hi hij hci => by
      have : i = 0 ∨ i = 1 := by have : gC.k = 3 := rfl; omega
      rcases this with rfl | rfl <;> simp [fl] at hci)
    wit_hA
    (fun u h1 h2 => by
      have : u = 5 := by omega
      subst this; unfold Tog; show ¬ (x 2 (5 - 1) ≠ x 2 5); decide)

/-- The witness C-element does switch (at 14 ps), so `wit_forced` is about a real toggle. -/
theorem wit_toggles : Tog (x gC.out) 14 := by unfold Tog; show x 2 (14 - 1) ≠ x 2 14; decide

theorem wit_toggle_14 : (x 0 13 = x 2 14) ∧ (x 1 13 = x 2 14) := by decide

end Formal.Cells.SpecCElemWit
