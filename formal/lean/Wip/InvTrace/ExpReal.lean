import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Formal.Core.Delay.InvolutionTrace

/-! Real exp-channel instance on traces (needs the Log module; not built yet).
`E x = e^{x/τ}`, `L y = τ ln y`, from Wip/DelayInvolution.lean. -/

namespace Formal.Core.DelayInvolution

noncomputable def realExpLog' (τ : ℝ) (hτ : 0 < τ) : ExpLog where
  E := fun x => Real.exp (x / τ)
  L := fun y => τ * Real.log y
  E_pos := fun x => Real.exp_pos _
  E_strictMono := fun a b h => Real.exp_lt_exp.mpr (div_lt_div_of_pos_right h hτ)
  E_zero := by simp
  L_E := fun x => by simp only [Real.log_exp]; field_simp
  E_L := fun y hy => by
    simp only
    rw [mul_div_cancel_left₀ _ (ne_of_gt hτ), Real.exp_log hy]

/-- With real `exp`/`log`: a pulse `[a, a+Δ]` through the exp-channel is cancelled iff
`Δ ≤ τ ln 2`. -/
theorem real_exp_channel_runt (τ Tp : ℝ) (hτ : 0 < τ) (hTp : 0 < Tp) (a Δ : ℝ) (hΔ : 0 < Δ)
    (hrunt : Δ ≤ τ * Real.log 2) :
    ((realExpLog' τ hτ).expPair Tp hTp).channel [a, a + Δ] = [] := by
  rw [InvolutionPair.exp_channel_pulse _ Tp hTp a Δ hΔ]
  exact if_pos hrunt

end Formal.Core.DelayInvolution
