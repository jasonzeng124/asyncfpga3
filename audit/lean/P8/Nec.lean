import Formal.Cells.Necessity2Arb
import Formal.Cells.Necessity2Latch
import Formal.Cells.Necessity3Pipe

/-! P8 audit, item 1: the Necessity2/3 counter-runs checked against the SHIPPED
theorems' own hypothesis sets (not the probe's restated `Claim`s). -/

namespace Audit.P8.Nec
open Formal.Cells Formal.Cells.ArbHeldTimed Formal.Cells.ArbHeldTimed2
open Formal.Cells.Necessity2Arb

/-- Arbiter row rt2_g1: every hypothesis of `rt2_exclusion_arcs` except RT2.g1
holds on (DG1, SG1); RT2 itself fails; g1 misses by exactly 1; conclusion fails. -/
theorem arb_g1 :
    Run DG1 SG1 ∧ Scn DG1 SG1 0 (-1000) 9 19 100 ∧ A0Fork DG1 ∧
    (DG1.c1f + DG1.wfa1 ≤ DG1.wa0s + DG1.qf + DG1.wfb + DG1.Rrq + DG1.smin) ∧
    (DG1.wa01 + DG1.c1f ≤ DG1.wa0s + DG1.qf + DG1.wfb + DG1.Rrq + DG1.smin + DG1.wa02 + DG1.c2r) ∧
    (DG1.wr1g + DG1.g1f1 + DG1.wg1 + DG1.c1f ≤
      DG1.wr1s + DG1.Rf1 + 2 * DG1.smin + DG1.wa0s + DG1.qf + DG1.wfb + DG1.Rrq + DG1.wa02 + DG1.c2r) ∧
    (DG1.wr1g + DG1.g1f1 + DG1.wg1 + DG1.c1f + DG1.wfa1 =
      DG1.wr1s + DG1.Rf1 + 2 * DG1.smin + DG1.wa0s + DG1.qf + DG1.wfb + DG1.Rrq + DG1.wa01 + 1) ∧
    ¬ RT2 DG1 ∧
    ¬ (∀ t, t < 100 → (SG1.A1 t && SG1.A2 t) = false) := by
  refine ⟨SG1_run, SG1_scn, by unfold A0Fork; decide, by decide, by decide, by decide, by decide,
    fun h => by have := h.g1; revert this; decide, fun h => by have := h 20 (by omega); revert this; decide⟩

/-- Arbiter row rt2_forkA, same shape. -/
theorem arb_forkA :
    Run DFA SFA ∧ Scn DFA SFA 0 (-1000) 9 19 100 ∧ A0Fork DFA ∧
    (DFA.c1f + DFA.wfa1 ≤ DFA.wa0s + DFA.qf + DFA.wfb + DFA.Rrq + DFA.smin) ∧
    (DFA.wr1g + DFA.g1f1 + DFA.wg1 + DFA.c1f + DFA.wfa1 ≤
      DFA.wr1s + DFA.Rf1 + 2 * DFA.smin + DFA.wa0s + DFA.qf + DFA.wfb + DFA.Rrq + DFA.wa01) ∧
    (DFA.wr1g + DFA.g1f1 + DFA.wg1 + DFA.c1f ≤
      DFA.wr1s + DFA.Rf1 + 2 * DFA.smin + DFA.wa0s + DFA.qf + DFA.wfb + DFA.Rrq + DFA.wa02 + DFA.c2r) ∧
    (DFA.wa01 + DFA.c1f = DFA.wa0s + DFA.qf + DFA.wfb + DFA.Rrq + DFA.smin + DFA.wa02 + DFA.c2r + 1) ∧
    ¬ (∀ t, t < 100 → (SFA.A1 t && SFA.A2 t) = false) := by
  refine ⟨SFA_run, SFA_scn, by unfold A0Fork; decide, by decide, by decide, by decide, by decide,
    fun h => by have := h 20 (by omega); revert this; decide⟩

/-- Non-degeneracy of the arbiter run: client 1 really had the ack, A2 really rises,
both requests are live (not a stuck run). -/
theorem arb_g1_nondeg : SG1.A1 0 = true ∧ SG1.A2 0 = false ∧ SG1.A1 19 = false ∧
    SG1.A2 20 = true ∧ SG1.g1 0 = true ∧ SG1.g1 17 = false := by decide

section latch
open Formal.Cells.Bundling Formal.Cells.ConstraintsLatchRst Formal.Cells.Necessity2Latch
/-- bd_latch_rst.setup_pulse with the REAL reset INIT 00B8.. (RST0): every
hypothesis of `capture_rst_from_request` except H_PW holds, H_PW misses by 1,
the conclusion fails at t = 13. -/
theorem latch_pw :
    IsRstLatch RST0 false ∧ RstGate RST0 pD pEn pQ zero 1 1 1 1 3 3 1 1 ∧
    (∀ t, 10 ≤ t → t < 12 → pEn t = true) ∧ (∀ t, 12 ≤ t → t < 1000 → pEn t = false) ∧
    (∀ t, 0 ≤ t → t < 1000 → pD t = true) ∧ (∀ t, 0 ≤ t → zero t = false) ∧
    (0 + 1 ≤ max (10 + 1) (0 + 1)) ∧ (10 + 0 ≤ 10) ∧ (10 + 2 ≤ 12) ∧
    (0 + 1 + 3 ≤ 10 + 0 + 2 + 1) ∧ ¬ (1 + 3 ≤ 2 + 1) ∧ (12 + 1 ≤ 1000 + 1) ∧
    ¬ (∀ t, max (10 + 1) (0 + 1) ≤ t → t < 1000 + 1 → pQ t = true) := by
  refine ⟨rst0_isRst, pGate _ rst0_bin, fun t h1 h2 => by simp [pEn]; omega,
    fun t h1 h2 => by simp [pEn]; omega, fun _ _ _ => rfl, fun _ _ => rfl,
    by decide, by decide, by decide, by decide, by decide, by decide, fun h => ?_⟩
  have := h 13 (by decide) (by decide); revert this; decide
end latch

section pipe
open Formal.Cells.PipeTimed Formal.Cells.PipeTimedN Formal.Cells.Necessity3Pipe
/-- bd_pipe.boundary_I against `PipeTimedN.token`'s own `DataN`: the run RI
satisfies GatesN/EnvN/TimingN and every DataN field except H_I; H_I fails;
token's conclusion fails at stage 1, t = 12. -/
theorem pipe_I :
    let V := V2 (pw 1 6 1) (pw 1 1 1)
    let x := X2 x0I x1I
    (¬ ∀ i b, i + 1 < PP.N → b < 1 →
      PipeTimedN.Dl PP V 0 2 i b + (V (i + 1)).dhi b + (V (i + 1)).fhi b ≤
        ((PP.Won 3 3 i + (PP.Rq (i + 1)).lo + (PP.L (i + 1)).lo + (V (i + 1)).elo b : Nat) : Int)) ∧
    (∀ k, dSI k + 0 ≤ PP.ρ (2 * k) + 2) ∧
    (∀ i b, i + 1 < PP.N → b < 1 →
      (V (i + 1)).ehi b ≤ PP.aslow (i + 1) + (PP.L i).lo + (V i).elo b + (V (i + 1)).dlo b) ∧
    PP.Sx V dSI 0 0 1 ≤ 12 ∧ 12 < PP.τ 1 (2 * 0 + 1 + 1) + (V 1).elo 0 ∧
    x 1 0 12 ≠ Formal.Cells.PipeTimed.Wit.valW 0 0 := by
  intro V x
  have D := dataS_I
  refine ⟨fun h => ?_, fun k => by have := D.H_DATA_LEAD k; omega,
    fun i b h1 h2 => by have := D.H_H i b h1 h2; omega, ?_, ?_, by decide⟩
  · have := h 0 0 (by decide) (by decide)
    revert this; simp [PipeTimedN.Dl, V, V2, pw, Won2, PP, PipeTimedN.Wit.Pw]
    all_goals (first | decide | omega | skip)
  · rw [sx1]; decide
  · rw [τ2]; decide

/-- the other DataN fields (H_LATCH, H_WIN, H_DATA_VALID, H_DATA_REL, H_HOLD0,
H_PW, H_SETUP0) are slack-free in DataS, so dataS_I carries them verbatim. -/
example := dataS_I.H_LATCH
example := dataS_I.H_SETUP0
end pipe

end Audit.P8.Nec

#print axioms Audit.P8.Nec.arb_g1
#print axioms Audit.P8.Nec.arb_forkA
#print axioms Audit.P8.Nec.latch_pw
#print axioms Audit.P8.Nec.pipe_I
-- the real INIT string used by the latch run
example : Formal.Cells.Latch.RST0 = 0x00B800B800B800B8 := rfl
