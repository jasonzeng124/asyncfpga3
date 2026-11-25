import Formal.Cells.Necessity2Arb
import Formal.Cells.AMergeTimedC

/-!
# Necessity2AMerge: `bdc_amerge3` H_RT2_CASCADE fields are tight to 1 ps

Probe Bsx2 (shard B). Rows `bdc_amerge3.rt2_cascade_g1`, `_forkA`, `_forkG`
(`AMergeTimedC.rt2_cascade`) and `_g2`, `_forkA2`, `_forkG2`
(`rt2_cascade2`) were "sufficient". The cascade theorem's hypotheses: a run
of arbiter 1 (`Run D1 s1`, `Scn`/`Scn2`), a run of arbiter 2 (`Run D2 s2`),
the wiring (`s2.r1 = s1.R0`, `s2.A1 = s1.A0`), arbiter 2's side `CSide`
(in2 idle, z_ack phases, H_SETTLED, H_ACK1_PULSE), the fields `RT2C` /
`RT2Cb` with the derived responses `sF D2`, `sR D2`, and the A0 fork.

## Result

`CClaim sp sg sa sG` (`CClaim2` mirror) is `rt2_cascade` with the four
fields weakened by the given slack; `cclaim0`, `cclaim2_0` are the existing
theorems. One tick of slack on g1, forkA, forkG (g2, forkA2, forkG2) alone
is unsound: `cg1_false`, `cforkA_false`, `cforkG_false`, `cg2_false`,
`cforkA2_false`, `cforkG2_false`.

Each counter-run is arbiter 1 = the matching run of `Necessity2Arb`
(`SG1`, `SFA`, ... with its delays `DG1`, ...) and arbiter 2 =
`AMergeTimedC.C2 1 1 1 6` under `AMergeTimedW.dW 1 1 1 6` (one consistent
corner: every arc 1, routes 0, z_ack server answering in exactly 6). Then
`sF = sR = 8`, the cascade realises arbiter 1's server exactly (its acc1_ack
output IS arbiter 1's A0 trace, `hA` holds pointwise), and RT2C with
`sF + sR = 16` is literally 7h's RT2 with `2 smin = 16`. Both arbiters'
gate relations hold for all t; both acks of arbiter 1 are high at 20 (22 for
the 1C g1 run).

The pulse fields too: `cpulse_false`, `cpulse2_false` (arbiter 1 =
`Necessity2Arb.SP` / `SP2`, every arc rise = fall, eternal runt train,
overlap at 30).

So in this model all eight fields are **necessary at the boundary**
(single-field 1-ps weakening refuted, one parameter point each). Not
covered: the in2-handover case (outside the theorem, H_IN2_IDLE).
-/

namespace Formal.Cells.Necessity2AMerge
open Formal.Cells Formal.Cells.ArbHeldTimed Formal.Cells.ArbHeldTimed2
open Formal.Cells.AMergeTimedC Formal.Cells.Necessity2Arb

/-- `RT2C` with per-field slack. -/
structure RT2Cs (D : Dl) (sF sR sp sg sa sG : Int) : Prop where
  pulse : D.c1f + D.wfa1 ≤ D.wa0s + D.qf + D.wfb + D.Rrq + sR + sp
  g1 : D.wr1g + D.g1f1 + D.wg1 + D.c1f + D.wfa1 ≤
    D.wr1s + D.Rf1 + sF + sR + D.wa0s + D.qf + D.wfb + D.Rrq + D.wa01 + sg
  forkA : D.wa01 + D.c1f ≤ D.wa0s + D.qf + D.wfb + D.Rrq + sR + D.wa02 + D.c2r + sa
  forkG : D.wr1g + D.g1f1 + D.wg1 + D.c1f ≤
    D.wr1s + D.Rf1 + sF + sR + D.wa0s + D.qf + D.wfb + D.Rrq + D.wa02 + D.c2r + sG

/-- `RT2Cb` with per-field slack. -/
structure RT2Cbs (D : Dl) (sF sR sp sg sa sG : Int) : Prop where
  pulse : D.c2f + D.wfa2 ≤ D.wa0s + D.qr + D.wfb + D.Rrq + sR + sp
  g2 : D.wr2g + D.g2f + D.wg2 + D.c2f + D.wfa2 ≤
    D.wr2s + D.Rf2 + sF + sR + D.wa0s + D.qr + D.wfb + D.Rrq + D.wa02 + sg
  forkA : D.wa02 + D.c2f ≤ D.wa0s + D.qr + D.wfb + D.Rrq + sR + D.wa01 + D.c1r + sa
  forkG : D.wr2g + D.g2f + D.wg2 + D.c2f ≤
    D.wr2s + D.Rf2 + sF + sR + D.wa0s + D.qr + D.wfb + D.Rrq + D.wa01 + D.c1r + sG

/-- `rt2_cascade` with the fields weakened. -/
def CClaim (sp sg sa sG : Int) : Prop :=
  ∀ (D1 D2 : Dl) (s1 s2 : Sigs) (t0 ta TA TA2 Hz tz TZ TZ2 : Int),
    Run D1 s1 → Scn D1 s1 t0 ta TA TA2 Hz → Run D2 s2 →
    (∀ t, s2.r1 t = s1.R0 t) → (∀ t, s2.A1 t = s1.A0 t) →
    CSide D2 s2 (TR D1 t0) ta TA TA2 tz TZ TZ2 Hz →
    RT2Cs D1 (sF D2) (sR D2) sp sg sa sG → A0Fork D1 →
    ∀ t, t < Hz → (s1.A1 t && s1.A2 t) = false

/-- `rt2_cascade2` with the fields weakened. -/
def CClaim2 (sp sg sa sG : Int) : Prop :=
  ∀ (D1 D2 : Dl) (s1 s2 : Sigs) (t0 ta TA TA2 Hz tz TZ TZ2 : Int),
    Run D1 s1 → Scn2 D1 s1 t0 ta TA TA2 Hz → Run D2 s2 →
    (∀ t, s2.r1 t = s1.R0 t) → (∀ t, s2.A1 t = s1.A0 t) →
    CSide D2 s2 (TRb D1 t0) ta TA TA2 tz TZ TZ2 Hz →
    RT2Cbs D1 (sF D2) (sR D2) sp sg sa sG → A0Fork2 D1 →
    ∀ t, t < Hz → (s1.A1 t && s1.A2 t) = false

theorem cclaim0 : CClaim 0 0 0 0 := by
  intro D1 D2 s1 s2 t0 ta TA TA2 Hz tz TZ TZ2 R1 S1 R2 hr hA K h hf
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact rt2_cascade R1 S1 R2 hr hA K ⟨by omega, by omega, by omega, by omega⟩ hf

theorem cclaim2_0 : CClaim2 0 0 0 0 := by
  intro D1 D2 s1 s2 t0 ta TA TA2 Hz tz TZ TZ2 R1 S1 R2 hr hA K h hf
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact rt2_cascade2 R1 S1 R2 hr hA K ⟨by omega, by omega, by omega, by omega⟩ hf

/-! ## Arbiter 2: `C2 1 1 1 6` at one corner (every arc 1, routes 0, server 6) -/

def D2c : Dl := AMergeTimedW.dW 1 1 1 6 (by omega)
def S2c : Sigs := C2 1 1 1 6

theorem D2c_resp : sF D2c = 8 ∧ sR D2c = 8 := by decide

theorem S2c_run : Run D2c S2c := C2_run 1 1 1 6 (by omega) (by omega)

/-- Arbiter 2's request is arbiter 1's R0 trace of every counter-run. -/
theorem S2c_r1 (s1 : Sigs) (h : s1.R0 = fun t => decide (t < 1) || decide (11 ≤ t)) :
    ∀ t, S2c.r1 t = s1.R0 t := by
  intro t; rw [h, Bool.eq_iff_iff]; simp [S2c, C2, AMergeTimedW.W1g] <;> omega

/-- Arbiter 2's ack (acc1_ack) is arbiter 1's A0 trace `A0w`. -/
theorem S2c_A1 (s1 : Sigs) (h : s1.A0 = A0w) : ∀ t, S2c.A1 t = s1.A0 t := by
  intro t; rw [h, Bool.eq_iff_iff]; simp [S2c, C2, AMergeTimedW.W1g, A0w] <;> omega

theorem S2c_side : CSide D2c S2c 1 (-1000) 9 19 (-1001) 8 18 100 :=
  C2_side 1 1 1 6 (by omega) (by omega) 100 (by omega)

/-! ## The six refutations -/

theorem cg1_false : ¬ CClaim 0 1 0 0 := by
  intro h
  have := h DG1 D2c SG1 S2c 0 (-1000) 9 19 100 (-1001) 8 18 SG1_run SG1_scn S2c_run
    (S2c_r1 SG1 rfl) (S2c_A1 SG1 rfl) S2c_side
    ⟨by decide, by decide, by decide, by decide⟩ G1_viol.2.2 20 (by omega)
  rw [G1_both] at this; exact absurd this (by decide)

theorem cg1_false_1C : ¬ CClaim 0 1 0 0 := by
  intro h
  have := h DG1c D2c SG1c S2c 0 (-1000) 9 19 100 (-1001) 8 18 SG1c_run SG1c_scn S2c_run
    (S2c_r1 SG1c rfl) (S2c_A1 SG1c rfl) S2c_side
    ⟨by decide, by decide, by decide, by decide⟩ G1c_viol.2.2.1 22 (by omega)
  have e : (SG1c.A1 22 && SG1c.A2 22) = true := by decide
  rw [e] at this; exact absurd this (by decide)

theorem cforkA_false : ¬ CClaim 0 0 1 0 := by
  intro h
  have := h DFA D2c SFA S2c 0 (-1000) 9 19 100 (-1001) 8 18 SFA_run SFA_scn S2c_run
    (S2c_r1 SFA rfl) (S2c_A1 SFA rfl) S2c_side
    ⟨by decide, by decide, by decide, by decide⟩ FA_viol.2.2.1 20 (by omega)
  rw [FA_both] at this; exact absurd this (by decide)

theorem cforkG_false : ¬ CClaim 0 0 0 1 := by
  intro h
  have := h DFG D2c SFG S2c 0 (-1000) 9 19 100 (-1001) 8 18 SFG_run SFG_scn S2c_run
    (S2c_r1 SFG rfl) (S2c_A1 SFG rfl) S2c_side
    ⟨by decide, by decide, by decide, by decide⟩ FG_viol.2.2.1 20 (by omega)
  rw [FG_both] at this; exact absurd this (by decide)

theorem cg2_false : ¬ CClaim2 0 1 0 0 := by
  intro h
  have := h DG2 D2c SG2 S2c 0 (-1000) 9 19 100 (-1001) 8 18 SG2_run SG2_scn S2c_run
    (S2c_r1 SG2 rfl) (S2c_A1 SG2 rfl) S2c_side
    ⟨by decide, by decide, by decide, by decide⟩ G2_viol.2.2 20 (by omega)
  rw [G2_both] at this; exact absurd this (by decide)

theorem cforkA2_false : ¬ CClaim2 0 0 1 0 := by
  intro h
  have := h DFA2 D2c SFA2 S2c 0 (-1000) 9 19 100 (-1001) 8 18 SFA2_run SFA2_scn S2c_run
    (S2c_r1 SFA2 rfl) (S2c_A1 SFA2 rfl) S2c_side
    ⟨by decide, by decide, by decide, by decide⟩ FA2_viol.2.2 20 (by omega)
  rw [FA2_both] at this; exact absurd this (by decide)

theorem cforkG2_false : ¬ CClaim2 0 0 0 1 := by
  intro h
  have := h DFG2 D2c SFG2 S2c 0 (-1000) 9 19 100 (-1001) 8 18 SFG2_run SFG2_scn S2c_run
    (S2c_r1 SFG2 rfl) (S2c_A1 SFG2 rfl) S2c_side
    ⟨by decide, by decide, by decide, by decide⟩ FG2_viol.2.2 20 (by omega)
  rw [FG2_both] at this; exact absurd this (by decide)

theorem cpulse_false : ¬ CClaim 1 0 0 0 := by
  intro h
  have := h DP D2c SP S2c 0 (-1000) 9 19 100 (-1001) 8 18 SP_run SP_scn S2c_run
    (S2c_r1 SP rfl) (S2c_A1 SP rfl) S2c_side
    ⟨by decide, by decide, by decide, by decide⟩ P_viol.2.2 30 (by omega)
  have e : (SP.A1 30 && SP.A2 30) = true := by decide
  rw [e] at this; exact absurd this (by decide)

theorem cpulse2_false : ¬ CClaim2 1 0 0 0 := by
  intro h
  have := h DP2 D2c SP2 S2c 0 (-1000) 9 19 100 (-1001) 8 18 SP2_run SP2_scn S2c_run
    (S2c_r1 SP2 rfl) (S2c_A1 SP2 rfl) S2c_side
    ⟨by decide, by decide, by decide, by decide⟩ P2_viol.2.2 30 (by omega)
  have e : (SP2.A1 30 && SP2.A2 30) = true := by decide
  rw [e] at this; exact absurd this (by decide)

end Formal.Cells.Necessity2AMerge
