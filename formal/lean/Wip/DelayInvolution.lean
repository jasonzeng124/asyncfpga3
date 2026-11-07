import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Formal.Core.Delay.Involution

/-!
# WIP: the real exp-channel instance, and open goals for involution channels

NOT BUILT, NOT CLAIMED.  Blocked on `Mathlib.Analysis.SpecialFunctions.Log.Basic`
(requested in `Wip/REQUESTS.txt`).  The proofs below are drafts written against
Mathlib names (`Real.exp_pos`, `Real.exp_lt_exp`, `Real.log_exp`, `Real.exp_log`)
and have not been checked.  Once the module is built, move the `realExpLog`
section into `Formal/Core/Delay/Involution.lean` (or a sibling file).

Open goals, marked `sorry`:
* `exists_dmin`: existence of δmin from continuity (IVT; needs
  `Mathlib.Topology.Order.IntermediateValue` or similar).
* `filtered_output_trace`: the full output-trace semantics with chained
  cancellations (the paper's algorithm), and a proof that it agrees with
  `tent`/`cancel_iff` on isolated pulses.
-/

namespace Formal.Core.DelayInvolution

open Real

/-- `E x = e^{x/τ}`, `L y = τ ln y`. -/
noncomputable def realExpLog (τ : ℝ) (hτ : 0 < τ) : ExpLog where
  E := fun x => Real.exp (x / τ)
  L := fun y => τ * Real.log y
  E_pos := fun x => Real.exp_pos _
  E_strictMono := fun a b h => Real.exp_lt_exp.mpr (div_lt_div_of_pos_right h hτ)
  E_zero := by simp
  L_E := fun x => by
    simp only [Real.log_exp]; field_simp
  E_L := fun y hy => by
    simp only
    rw [mul_div_cancel_left₀ _ (ne_of_gt hτ), Real.exp_log hy]

/-- With the real `exp`/`log`, a pulse is cancelled iff `Δ ≤ τ ln 2`. -/
theorem real_exp_pulse_cancel_iff (τ Tp : ℝ) (hτ : 0 < τ) (hTp : 0 < Tp) {Δ : ℝ}
    (hΔ : 0 < Δ) :
    ((realExpLog τ hτ).expPair Tp hTp).pulseWidth Δ ≤ 0 ↔ Δ ≤ τ * Real.log 2 :=
  (realExpLog τ hτ).exp_pulse_cancel_iff Tp hTp hΔ

/-- OPEN (needs IVT): a continuous involution pair has a δmin. -/
theorem exists_dmin (P : InvolutionPair)
    (hcont : Continuous P.down) : ∃ d, P.IsDMin d := by
  sorry

/-- OPEN: the full output-trace semantics with chained cancellation.
Draft statement only; the semantics function is not yet defined. -/
theorem filtered_output_trace : True := by
  sorry

end Formal.Core.DelayInvolution
