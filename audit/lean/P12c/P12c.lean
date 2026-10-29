import Formal.Core.Delay.InvolutionExp
import Formal.Core.Delay.CornerCell
import Formal.Core.XAudit.BandCheck
import Formal.Core.XAudit.SoundInertial
import Formal.Core.XAudit.Events9Arb
import Formal.Core.XAudit.Events9ArbBeh
import Formal.Core.XAudit.Events9Prefix
import Formal.Core.XAudit.Events9PrefixSel
import Formal.Core.XAudit.Events9PrefixExt
import Formal.Core.XAudit.Events9SelSplit
import Formal.Core.XAudit.Events9SelC
import Formal.Core.XAudit.Events9SelHold
import Formal.Core.XAudit.Events9Sel

/-! Auditor P12c: axioms, statement identity, non-vacuity. -/

open Formal.Core.DelayInvolution.ExpReal in
section
-- claim 1
#print axioms expR_pulse_cancel_iff
#print axioms expR_stat
#print axioms expR_crit
#print axioms bad_not_involution
#print axioms exp_laps
#print axioms exp_resolution
#print axioms exp_laps_log
#print axioms expR_paper
#print axioms slope_lower
#print axioms slope_upper
end

-- the exact statement of expR_pulse_cancel_iff (for the report)
#check @Formal.Core.DelayInvolution.ExpReal.expR_pulse_cancel_iff
#check @Formal.Core.DelayInvolution.ExpReal.exp_resolution
#check @Formal.Core.DelayInvolution.ExpReal.bad_not_involution

theorem P12c_log2_ge : (1:ℝ)/2 ≤ Real.log 2 := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1/2 by norm_num)
  rw [one_div, Real.log_inv] at h; linarith

theorem P12c_log2_lt : Real.log 2 < 2 := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith

/-- Non-vacuity of `bad_not_involution`: its hypotheses hold at τ = 1, T_p = 1/4. -/
theorem P12c_bad_inst :
    -Formal.Core.DelayInvolution.ExpReal.badDelay 1 (1/4)
      (-Formal.Core.DelayInvolution.ExpReal.badDelay 1 (1/4) 0) ≠ 0 :=
  Formal.Core.DelayInvolution.ExpReal.bad_not_involution one_pos (by norm_num)
    (by have := P12c_log2_ge; linarith)

/-- Concrete: with τ = T_p = 1 a pulse of width 1/4 is cancelled (1/4 ≤ ln 2), width 2 is not. -/
theorem P12c_pulse_inst :
    (Formal.Core.DelayInvolution.ExpReal.expR 1 1 one_pos one_pos).channel [0, 0 + 1/4] = [] ∧
    (Formal.Core.DelayInvolution.ExpReal.expR 1 1 one_pos one_pos).channel [0, 0 + 2] ≠ [] := by
  constructor
  · rw [Formal.Core.DelayInvolution.ExpReal.expR_pulse_cancel_iff one_pos one_pos 0 (1/4) (by norm_num)]
    have := P12c_log2_ge; linarith
  · intro h
    rw [Formal.Core.DelayInvolution.ExpReal.expR_pulse_cancel_iff one_pos one_pos 0 2 (by norm_num)] at h
    have := P12c_log2_lt; linarith

#print axioms P12c_bad_inst
#print axioms P12c_pulse_inst

-- claim 3
#print axioms Formal.Core.CornerCell.cell_band
#print axioms Formal.Core.CornerCell.cell_band_mem
#print axioms Formal.Core.CornerCell.cell_band_int
#print axioms Formal.Core.CornerCell.cell_band_nat
#print axioms Formal.Core.CornerCell.cover_mem
#print axioms Formal.Core.XAudit.BandCheck.readBands_ok_iff
#print axioms Formal.Core.XAudit.BandCheck.readBands_spec
#print axioms Formal.Core.XAudit.BandCheck.readBands_rejects_entry
#print axioms Formal.Core.XAudit.BandCheck.readBands_rejects_field
#print axioms Formal.Core.XAudit.BandCheck.invertedFile_control

open Lean in
#eval
  match Json.parse "{\"arcs\":{\"a\":[5,3],\"b\":[1,2]},\"lut\":[1,2]}" with
  | .ok j => match Formal.Core.XAudit.BandCheck.readBands j with
    | .ok _ => "AUDIT inverted file ACCEPTED (bad)"
    | .error e => s!"AUDIT inverted file rejected: {e}"
  | .error e => e

open Lean in
#eval
  match Json.parse "{\"arcs\":{\"a\":[3,3],\"b\":[1,2]},\"lut\":[1,2]}" with
  | .ok j => match Formal.Core.XAudit.BandCheck.readBands j with
    | .ok _ => "AUDIT well-formed file accepted"
    | .error e => s!"AUDIT well-formed file REJECTED (bad): {e}"
  | .error e => e

-- claim 4
#print axioms Formal.Core.XAudit.SoundInertial.noXF_sound_inertial
#print axioms Formal.Core.XAudit.SoundInertial.valF_sound_inertial
#print axioms Formal.Core.XAudit.SoundInertial.constF_sound_inertial
#print axioms Formal.Core.XAudit.SoundInertial.settledF_inertial
#print axioms Formal.Core.XAudit.SoundInertial.gateOK_verilog
#print axioms Formal.Core.XAudit.SoundInertial.widened_wide
#print axioms Formal.Core.XAudit.SoundInertial.checkedSteps_inverted
#print axioms Formal.Core.XAudit.SoundInertial.widenD_eq_of_window
#check @Formal.Core.DelayInertial.Inertial
#print Formal.Core.DelayInertial.InertialRD

-- claim 2
#print axioms Formal.Core.XAudit.Events9Arb.core_of_settle
#print axioms Formal.Core.XAudit.Events9Arb.core_of_en
#print axioms Formal.Core.XAudit.Events9Arb.settle_not_old
#print axioms Formal.Core.XAudit.Events9Arb.ho3_fix
#print axioms Formal.Core.XAudit.Events9Arb.design_verdict9arb
#print axioms Formal.Core.XAudit.Events8Arb.unc_not_harb
#print axioms Formal.Core.XAudit.Events9Prefix.safe8_upto
#print axioms Formal.Core.XAudit.Events9Prefix.design_verdict9_upto
#print axioms Formal.Core.XAudit.Events9Prefix.design_verdict9'
#print axioms Formal.Core.XAudit.Events9Prefix.causal_close
#print axioms Formal.Core.XAudit.Events9PrefixSel.design_verdict9_selL
#print axioms Formal.Core.XAudit.Events9PrefixSel.design_verdict9_selP
#print axioms Formal.Core.XAudit.Events9PrefixSel.sibling_lag_neg
#print axioms Formal.Core.XAudit.Events9PrefixExt.link_upto_P
#print axioms Formal.Core.XAudit.Events9SelSplit.design_verdict9_selS
#print axioms Formal.Core.XAudit.Events9SelHold.design_verdict9_selH
#print axioms Formal.Core.XAudit.Events9SelC.design_verdict9_selC
#print axioms Formal.Core.XAudit.Events9Sel.design_verdict9_sel

/-- `design_verdict9'` has exactly `Events9.design_verdict9`'s type (claimed "statement identical"). -/
example : type_of% @Formal.Core.XAudit.Events9.design_verdict9 :=
  @Formal.Core.XAudit.Events9Prefix.design_verdict9'

/-- HARB7' adds nothing used: design_verdict9arb follows from design_verdict9 via HARB7' → HARB7. -/
example : ∀ {N : Nat} {d : Formal.Core.XAudit.Design} {net : Formal.Core.XAudit.Events5.Net4 N}
    {b : Formal.Core.XAudit.Events5.Bands4 net} {rn : Fin N → Formal.Core.XAudit.Events6.RNode}
    {x : Fin d.n → Formal.Core.TraceDiscrete.Sig} {cv : Fin N → Formal.Core.TraceDiscrete.Sig},
    Formal.Core.XAudit.Events9Arb.HARB7' net b rn x cv → Formal.Core.XAudit.Events7.HARB7 net b rn x cv :=
  fun h => h.1

-- core_of_settle never mentions ustate's O6 (q) equation: q is an arbitrary signal there.
#check @Formal.Core.XAudit.Events9Arb.core_of_settle
