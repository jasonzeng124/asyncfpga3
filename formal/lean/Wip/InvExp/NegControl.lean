import Formal.Core.Delay.InvolutionExp
/-! Negative controls for InvolutionExp (must FAIL to elaborate; not claimed). -/
open Formal.Core.DelayInvolution.ExpReal
-- (1) slope lower bound with 2κ: false (δ'(0) = κ exactly), must not follow from slope_lower.
example {τ Tp a b : ℝ} (hτ : 0 < τ) (hTp : 0 < Tp) (ha : -(Tp + τ * Real.log 2) < a)
    (hab : a ≤ b) (hb : b ≤ 0) :
    2 * kappaE τ Tp * (b - a) ≤ (expR τ Tp hτ hTp).up b - (expR τ Tp hτ hTp).up a :=
  slope_lower hτ hTp ha hab hb
-- (2) positive control: the threshold pulse Δ = τ ln 2 is cancelled (must elaborate).
example {τ Tp : ℝ} (hτ : 0 < τ) (hTp : 0 < Tp) :
    (expR τ Tp hτ hTp).channel [0, 0 + τ * Real.log 2] = [] :=
  (expR_pulse_cancel_iff hτ hTp 0 _ (mul_pos hτ (Real.log_pos (by norm_num)))).mpr le_rfl
-- (3) negative: a pulse 1% wider than τ ln 2 is NOT cancelled, so the same proof must fail.
example {τ Tp : ℝ} (hτ : 0 < τ) (hTp : 0 < Tp) :
    (expR τ Tp hτ hTp).channel [0, 0 + 101/100 * (τ * Real.log 2)] = [] :=
  (expR_pulse_cancel_iff hτ hTp 0 _ (by positivity)).mpr le_rfl
