import Formal.Cells.ArbCorners

/-!
# Audit P3: ArbCorners (482f624)

1. `cell_slow`, `cell_worst`: the timed 7e `Cell` relation is satisfiable for
   `arcsC slowMax RF.sym 0 0` and for the box worst corner `worstA 0`, with the
   handover scenario hypotheses (r1 = 1, r2 falls at 0, q low before 0). So
   `corner_no_overlap` and `box_overlap_worst` are not vacuous; in the box
   witness the grants really do overlap for exactly 37 ps.
2. `ruleJ_perwire_cex`: guarded rule J's FAST_MIN coverage
   (`ruleJ_guard_covers_fast`) rests on ONE wire ratio for the signed sum
   E - L (H_WIRE_RATIO). With per-wire ratios inside the notes' own measured
   p10..p90 band (0.37 for the early wires, 0.82 for the late wire) the guard
   passes, E is a realistic two-hop 600 ps, the client-2 FAST_MIN arc part is
   90, and the FAST_MIN margin is negative.
3. `ruleJ_E_threshold`: the 114 ps premise is not tight (E = 111 already
   suffices; E = 110 fails); harmless.
-/

namespace Audit.P3.Arb
open Formal.Cells Formal.Cells.ArbCorners Formal.Cells.ArbHandover

def r1W : Sig := fun _ => true
def r2W : Sig := fun t => decide (t < 0)

/-- SLOW_MAX, rise = fall, q routing 0, feedback 0. -/
def qS : Sig := fun t => decide (124 ≤ t)
def g1S : Sig := fun t => decide (274 ≤ t)          -- r1 && q(t - 150)
def g2S : Sig := fun t => decide (t < 124)          -- r2(t-124) && !q(t-124)

theorem cell_slow :
    Cell (arcsC slowMax RF.sym 0 0 (by decide) (by decide)) r1W r2W qS g1S g2S := by
  have e1 : slowMax.o6 = 124 := by decide
  have e2 : slowMax.o5a = 152 := by decide
  have e3 : slowMax.o5q = 150 := by decide
  refine ⟨?_, ?_, ?_⟩ <;> intro t <;>
    simp only [arcsC, RF.sym, e1, e2, e3, r1W, r2W, qS, g1S,
      g2S, stateF_eqn, g1F_eqn, g2F_eqn] <;>
    (rw [Bool.eq_iff_iff]; simp; omega)

theorem slow_nonvacuous :
    (∀ t, (g1S t && g2S t) = false) ∧ g1S 300 = true ∧ g2S 0 = true :=
  ⟨corner_no_overlap slowMax 0 0 (by decide) (by decide) 0 r1W r2W qS g1S g2S cell_slow
      (fun _ => rfl) (fun _ => rfl) (fun t h => by simp [qS]; omega),
   by decide, by decide⟩

/-- Box worst corner: q 45, g1's q-pin 42, g2 124. -/
def qB : Sig := fun t => decide (45 ≤ t)
def g1B : Sig := fun t => decide (87 ≤ t)
def g2B : Sig := fun t => decide (t < 124)

theorem cell_worst : Cell (worstA 0 (by decide)) r1W r2W qB g1B g2B := by
  refine ⟨?_, ?_, ?_⟩ <;> intro t <;>
    simp only [LutOut3, worstA, r1W, r2W, qB, g1B, g2B, stateF_eqn, g1F_eqn, g2F_eqn] <;>
    (rw [Bool.eq_iff_iff]; simp; omega)

theorem worst_nonvacuous :
    (countTrue (fun t => g1B t && g2B t) 0 124 : Int) = 37 := by
  have := box_overlap_worst 0 (by decide) 0 r1W r2W qB g1B g2B cell_worst
    (fun _ => rfl) (fun _ => rfl) (fun t h => by simp [qB]; omega) 124 (by decide)
  rw [this]; decide

/-- Per-wire corner ratios defeat guarded rule J's FAST_MIN coverage.
Scaled by 100: E = 600 ps early routing (fast 0.37), L = 525 ps late
(fast 0.82). Guard passes at SLOW_MAX, premises E >= 114 and Af = 90 hold,
every wire speeds up (k <= 1 per wire), but the FAST_MIN margin
90 + 0.37*600 - 0.82*525 = -118.5 ps < 0. -/
theorem ruleJ_perwire_cex :
    (1155 * ((525 : Int) + 124) < 772 * (600 + 372)) ∧ (114 : Int) ≤ 600 ∧
    (100 * 90 + 37 * 600 - 82 * 525 : Int) < 0 ∧
    -- the single-ratio reading of the same route is safe (k = 0.55 on E - L = 75):
    (0 : Int) ≤ 100 * 90 + 55 * (600 - 525) := by decide

/-- The E premise threshold: E = 111 suffices for every L passing the guard,
E = 110 has a passing L (198) with Af = 87, k = 1 giving margin -1. -/
theorem ruleJ_E_threshold :
    (∀ L : Int, 1155 * (L + 124) < 772 * (111 + 372) → 0 ≤ 87 + (111 - L)) ∧
    (1155 * ((198 : Int) + 124) < 772 * (110 + 372) ∧ 87 + ((110 : Int) - 198) < 0) := by
  refine ⟨fun L h => by omega, by decide⟩

end Audit.P3.Arb

#print axioms Formal.Cells.ArbCorners.corner_no_overlap
#print axioms Formal.Cells.ArbCorners.overlap_C
#print axioms Formal.Cells.ArbCorners.box_overlap_le
#print axioms Formal.Cells.ArbCorners.box_overlap_worst
#print axioms Formal.Cells.ArbCorners.prj_is_mix
#print axioms Formal.Cells.ArbCorners.prjArcs_is_mix
#print axioms Formal.Cells.ArbCorners.simArcs_is_mix
#print axioms Formal.Cells.ArbCorners.decomp
#print axioms Formal.Cells.ArbCorners.box_7h
#print axioms Formal.Cells.ArbCorners.box_7j_worst
#print axioms Formal.Cells.ArbCorners.pulse2_zero_routing
#print axioms Formal.Cells.ArbCorners.flip_iff
#print axioms Formal.Cells.ArbCorners.guard_universal
#print axioms Formal.Cells.ArbCorners.client2_corner_flip
#print axioms Formal.Cells.ArbCorners.ruleJ_guard_covers_fast
#print axioms Formal.Cells.ArbCorners.nonvacuous_corners
#print axioms Audit.P3.Arb.slow_nonvacuous
#print axioms Audit.P3.Arb.worst_nonvacuous
