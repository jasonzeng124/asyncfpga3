import Formal.Core.Prims.SeqXray
import Formal.Cells.ArbInvolution
import Formal.Core.Delay.InvolutionTransfer
open Formal.Core.Prims.Seq
open Formal.Cells Formal.Cells.ArbInvolution Formal.Cells.CElemInvolution
open Formal.Core.DelayInvolution

/-! ### fast_hold_mismatch: a numeric comparison of transcribed constants -/
#check @fast_hold_mismatch
example (res : Nat) : (regFF .fast false res).cqLo = 112 ∧ (regFF .fast false res).dHi = 241 ∧
    (regFF .slow false res).cqLo = 274 ∧ (regFF .slow false res).dHi = 241 := by
  simp [regFF, cs]
-- The D window is corner-independent by construction (H_WINDOW_SLOW_ONLY), so the
-- "mismatch" is a property of that assumption, not of a fast-corner measurement.
example (res : Nat) : (regFF .fast false res).dHi = (regFF .slow false res).dHi ∧
    (regFF .fast false res).dLo = (regFF .slow false res).dLo := by simp [regFF, cs]

/-! ### stF_runt -/
#check @stF_runt
-- The real INIT behind stF is bd_c2n_set's (cells/rtl/bd_ce.v:55).
example : ArbBinary.C2N_SET = 0xFFB2FFB2FFB2FFB2 := rfl
-- Dropping 0 < s breaks it: s = -1, u = -1/2, q = true (r2 already up, r1 not yet).
theorem stF_runt_needs_pos :
    ArbBinary.stF (r1R (-1/2)) (r2R (-1) (-1/2)) true ≠
      CElemTiming.exc CElemTiming.INIT_c2 true (bR (-1) (-1/2)) true false := by
  rw [exc_or, ArbBinary.stF_eq]
  simp only [r1R, r2R, bR]
  norm_num

/-! ### arb_eternal: instantiate the universally quantified channel with a concrete pair -/
#check @arb_eternal
open Formal.Core.DelayInvolutionTransfer in
theorem arb_eternal_ratPair : ∃ s, lft ratPair < s ∧ s < ratPair.infUp ∧
    (∃ x qp : Sig, ALoop ratPair s r1R (r2R s) x qp) ∧
    ∀ r1 r2 x qp : Sig, ALoop ratPair s r1 r2 x qp →
      ∀ B : ℝ, (∃ u, B < u ∧ qp u = true) ∧ (∃ u, B < u ∧ qp u = false) :=
  arb_eternal _
#check @arb_eternal_ratPair
#print axioms arb_eternal_ratPair
