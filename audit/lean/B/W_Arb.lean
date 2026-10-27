import Formal.Cells.ArbHandover
import Formal.Cells.ArbA0Fork
import Formal.Cells.TernarySound
/-! Audit (shard B): non-vacuity witnesses for the arbiter theorems. -/
set_option linter.deprecated false
open Formal.Cells

namespace AuditB.Arb

/-! ### ArbHandover.header_16ps: the Cell relation is satisfiable with t0 = 0 -/
section H
open Formal.Cells.ArbHandover

def r1 : Sig := fun _ => true
def r2 : Sig := fun t => decide (t < 0)
def q : Sig := fun t => decide (56 ≤ t)
def g1 : Sig := fun t => decide (108 ≤ t)
def g2 : Sig := fun t => decide (t < 124)

theorem cell : Cell (prjArcs 0 (by omega)) r1 r2 q g1 g2 where
  H_state := by
    intro t
    dsimp only [prjArcs, r1, r2, q]; simp only [stateF_eqn, Int.sub_zero]
    by_cases h : 56 ≤ t
    · rw [decide_eq_false (show ¬ (t - 56 < 0) by omega), decide_eq_true h]; rfl
    · rw [decide_eq_true (show t - 56 < 0 by omega), decide_eq_true (show t - 124 < 0 by omega),
        decide_eq_false (show ¬ (56 ≤ t - 56) by omega),
        decide_eq_false (show ¬ (56 ≤ t - 124) by omega), decide_eq_false h]; rfl
  H_g1 := by
    intro t
    simp only [prjArcs, r1, q, g1, g1F_eqn, Bool.true_and]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    simp only [decide_eq_true_eq, decide_eq_false_iff_not, Int.sub_zero]; omega
  H_g2 := by
    intro t
    dsimp only [prjArcs, r2, q, g2]; simp only [g2F_eqn, Int.sub_zero]
    by_cases h : t < 124
    · rw [decide_eq_true (show t - 124 < 0 by omega),
        decide_eq_false (show ¬ (56 ≤ t - 124) by omega), decide_eq_true h]
      cases decide (t - 56 < 0) <;> cases decide (56 ≤ t - 56) <;> rfl
    · rw [decide_eq_false (show ¬ (t - 56 < 0) by omega),
        decide_eq_false (show ¬ (t - 124 < 0) by omega), decide_eq_false h]; rfl

/-- all hypotheses of `header_16ps` hold for t0 = 0. -/
theorem header_16ps_hyps :
    Cell (prjArcs 0 (by omega)) r1 r2 q g1 g2 ∧ (∀ t, r1 t = true) ∧
    (∀ t, r2 t = decide (t < 0)) ∧ (∀ t, t < 0 → q t = false) :=
  ⟨cell, fun _ => rfl, fun _ => rfl, fun t h => by simp [q]; omega⟩

/-- and the 16 ps conclusion is then non-trivially instantiated -/
example : countTrue (fun t => g1 t && g2 t) 0 124 = 16 :=
  (header_16ps 0 r1 r2 q g1 g2 cell (fun _ => rfl) (fun _ => rfl) header_16ps_hyps.2.2.2).2

end H

/-! ### ArbA0Fork: both sides of the iff are inhabited (client 2) -/
section F
open Formal.Cells.ArbA0Fork

/-- a delay record with `late ≤ early` (safe) ... -/
def pSafe : Dl := ⟨10, 100, 50, 124, 300, 50, 200, 50, 124, 300, 50, 400, 50, 124, 300, 50⟩
/-- ... and one with `early < late` (A0 branch to ua2 too slow). -/
def pBad : Dl := { pSafe with wAC := 2000 }

example : pSafe.late ≤ pSafe.early ∧ pBad.early < pBad.late := by decide

theorem safe_run : ∃ a0 q g A, Run F2 G2 true pSafe 1 a0 q g A :=
  run_exists F2 G2 false pSafe 1 F2_hold F2_go G2_vals.1 (by decide) (by decide) (by decide)
theorem bad_run : ∃ a0 q g A, Run F2 G2 true pBad 1 a0 q g A :=
  run_exists F2 G2 false pBad 1 F2_hold F2_go G2_vals.1 (by decide) (by decide) (by decide)

/-- on the bad run the false ack really fires -/
example : ∃ a0 q g A, Run F2 G2 true pBad 1 a0 q g A ∧ ∃ t, A t = true := by
  obtain ⟨a0, q, g, A, R⟩ := bad_run
  exact ⟨a0, q, g, A, R, _, client2_counter R (by decide)⟩

/-- on the safe run it never does -/
example : ∃ a0 q g A, Run F2 G2 true pSafe 1 a0 q g A ∧ ∀ t, A t = false := by
  obtain ⟨a0, q, g, A, R⟩ := safe_run
  exact ⟨a0, q, g, A, R, (client2_iff R).2 (by decide)⟩

end F

/-! ### TernarySound.arb_runt_opposite: hypotheses jointly satisfiable -/
section T
open Formal.Cells.TernarySound

/-- inputs: r2 = 1 from step 1 on, everything else 0 -/
def inp : Nat → Nat → Bool := fun _ n => decide (n = 1)
def c0 : Nat → Bool := fun _ => false
def v := simB arbNet inp c0

theorem v_input (k n : Nat) (hn : n ≤ 4) : v k n = (decide (n = 1) && decide (0 < k)) := by
  cases k with
  | zero => simp [v, simB, c0]
  | succ k =>
    have : arbNet.node n = .input := (arb_input_iff n).2 (Or.inl hn)
    show (match arbNet.node n with
      | .input => inp (k + 1) n
      | .gate init pins => lutB init (pinsB (fun _ i => simB arbNet inp c0 k i) pins 0)) = _
    rw [this]; simp [inp]

theorem idle : IdleServer v where
  a0 k := by rw [v_input k 2 (by decide)]; simp
  a0c k := by rw [v_input k 3 (by decide)]; simp
  rst k := by rw [v_input k 4 (by decide)]; simp
  a1_0 := rfl
  a2_0 := rfl

/-- all hypotheses of `arb_runt_opposite` (D = W = 0, T0 = 1) hold. -/
theorem runt_hyps :
    Bounded arbNet v (unitRun arbNet inp c0) 0 0 ∧ IdleServer v ∧
    (∀ k, 1 ≤ k → v k 0 = false) ∧ (∀ k, 1 ≤ k → v k 1 = true) :=
  ⟨unitDelay_run arbNet inp c0, idle,
   fun k _ => by rw [v_input k 0 (by decide)]; simp,
   fun k hk => by rw [v_input k 1 (by decide)]; simp; omega⟩

end T
end AuditB.Arb
#print axioms AuditB.Arb.header_16ps_hyps
#print axioms AuditB.Arb.safe_run
#print axioms AuditB.Arb.bad_run
#print axioms AuditB.Arb.runt_hyps
