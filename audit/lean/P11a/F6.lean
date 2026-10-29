import Formal.Core.Delay.GLSResolveGen
/-! P11a item 6 (formal c52bb7e, GLSResolveGen.arb_double_ack): non-vacuity at research's
default resolver parameters (TAU = WIN = 150 ps), own instance. -/
open Formal.Core.GLSResolve Formal.Core.GLSResolveGen
open Formal.Core.GLSFid (Res resolve lut6)

#print axioms Formal.Core.GLSResolveGen.arb_double_ack
#print axioms Formal.Core.GLSResolveGen.arb_gap_closed
#print axioms Formal.Core.GLSResolveGen.arb_near_tie
#print axioms Formal.Core.GLSResolveGen.arbF_lut
#check @Formal.Core.GLSResolveGen.arb_double_ack

namespace P11a
set_option maxRecDepth 200000
-- own: the Lean INIT for ustate is research bd_arb.v:254
example : INIT_ARB = 0xFFF0FFB2ACACACAC := by decide

/-- q loop: TLOOP = 10, WIN = 150, noise draw -65 at the decision (1.73 sigma of N(0, 37)),
so delta = 1 - (10 - 75) - 65 = 1 > 0: commit, and fid_core.vh's law gives
trp = rtoi(150 ln(150 / 2)) = 647. Only the value of R at delta = 1 is used. -/
def pq : Prm := ⟨10, 150, fun _ => -65, fun d => if d = 1 then 647 else 0⟩
def pc : Prm := ⟨10, 150, fun _ => 0, fun _ => 0⟩

example : pq.delta 1 2 = 1 := by decide
example : resolve (1 : Int) (pq.L : Int) pq.win (pq.nz (1 + 1)) = .commit := by decide
example : trpS pq 1 1 = 647 := by decide

/-- Own instance: r1 at 1, r2 at 2 (w = 1 < TLOOP), A0 reaches both ua_k at 7 (grant delay 5),
TLOOP of ua2 = 10. For the (unique) resolver runs, at t = 700 both acks are high under one A0 step. -/
theorem double_ack_instance (stq st1 st2 : Nat → St)
    (hq : GRun pq (arbF (stepS 1) (stepS (1 + 1)) rstZero (fun _ => false)) false stq)
    (h1 : GRun pc (c2F (gA1 stq 1 5) (stepS 7) rstZero) false st1)
    (h2 : GRun pc (c2F (gA2 stq 1 1 5) (stepS 7) rstZero) false st2) :
    (st1 700).o = true ∧ (st2 700).o = true := by
  have htr : trpS pq 1 1 = 647 := by decide
  have h := arb_double_ack (pq := pq) (p1 := pc) (p2 := pc) (T0 := 1) (w := 1) (D1 := 5) (D2 := 5)
    (sA1 := 7) (sA2 := 7) (A0q := fun _ => false)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hq (fun _ _ => rfl) (by decide) h1 h2
    (by omega) (by rw [htr]; omega) (by omega) (by rw [htr]; show 7 + 10 ≤ _; omega) 700 (by rw [htr]; omega) (by omega)
  exact ⟨h.1, h.2.1⟩

/-- The runs exist (so the instance is not vacuous). -/
theorem double_ack_runs_exist : ∃ stq st1 st2 : Nat → St,
    GRun pq (arbF (stepS 1) (stepS (1 + 1)) rstZero (fun _ => false)) false stq ∧
    GRun pc (c2F (gA1 stq 1 5) (stepS 7) rstZero) false st1 ∧
    GRun pc (c2F (gA2 stq 1 1 5) (stepS 7) rstZero) false st2 :=
  ⟨_, _, _, grun_exists _ _ _ (by decide), grun_exists _ _ _ (by decide), grun_exists _ _ _ (by decide)⟩

/-- MUTATION: A0 reaching ua2 after the gap (sA2 = 700 >= 1 + 1 + 647 + 5): A2 never rises. -/
theorem gap_closed_instance :
    let stq := cr (GG pq (arbF (stepS 1) (stepS (1 + 1)) rstZero (fun _ => false)) false)
    let st2 := cr (GG pc (c2F (gA2 stq 1 1 5) (stepS 700) rstZero) false)
    ∀ t, (st2 t).o = false := by
  intro stq st2
  exact arb_gap_closed (pq := pq) (p2 := pc) (T0 := 1) (w := 1) (D2 := 5) (sA2 := 700)
    (A0q := fun _ => false) (by decide) (by decide) (by decide) (by decide) (by decide)
    (grun_exists _ _ _ (by decide)) (fun _ _ => rfl) (by decide)
    (grun_exists _ _ _ (by decide)) (by decide)

#print axioms double_ack_instance
#print axioms double_ack_runs_exist
#print axioms gap_closed_instance
end P11a
