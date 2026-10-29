import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Formal.Core.Delay.InvolutionTrace
import Formal.Core.Delay.InvolutionLoopRate

/-!
# The exp-channel with real `exp`/`log`: involution pair, loop train, slope bounds, rate law

Probe InvExp (shard A).  `Involution.lean` defines the exp-channel over an abstract
`ExpLog` (named hypotheses on `E`, `L`) because Mathlib's `Log` module was not built then.
Here `E x = e^{x/τ}`, `L y = τ ln y` with Mathlib's `Real.exp`/`Real.log`, so every
`ExpLog` theorem holds for the real channel with no extra hypothesis.

The channel (`expR τ Tp`, `τ > 0`, `T_p > 0`, symmetric: `δ↑ = δ↓ = δ`):
  `δ(T) = T_p + τ ln(2 - e^{-(T + T_p)/τ})`     (pure delay `T_p`, then a first-order RC
  stage with threshold 1/2 that starts from where the previous opposite ramp has got to),
  `δ∞ = T_p + τ ln 2`, `δmin = T_p`, domain `T > -δ∞`.
* `expR_paper`: the same function is `δ(T) = δ∞ + τ ln(1 - e^{-(T + δ∞)/τ})`.
  `bad_not_involution`: the variant with `T + δ∞ - T_p` in the exponent is NOT an involution
  for `0 < T_p < τ ln 2` (so that form only fits a convention where `T_p` is not the pure
  delay; the papers were not readable from this sandbox, see notes/A-inv-exp.md).
* `expR_dmin`, `expR_pulse`: an isolated pulse is cancelled iff `Δ ≤ τ ln 2` (exact
  threshold), else it comes out `δ∞` later with width `pulseWidth Δ`.
* `expR_stat`: the OR loop's stationary train is high = low = `w* = τ ln x`,
  `x = (√(1 + 8 e^{T_p/τ}) - 1)/2` (closed form), unique; `s* = δ∞ - w* = T_p + τ ln(2/x)`;
  `0 < w* < T_p`.
* `slope_lower`: on `(-δ∞, 0]` the slope is at least `κ = q/(2-q)`, `q = e^{-T_p/τ}`
  (that is `δ'(0)`); `slope_upper`: on `[-M, ∞)`, `M < δ∞`, at most `K = r/(2-r)`,
  `r = e^{(M - T_p)/τ}` (that is `δ'(-M)`).  Elementary (`ln y ≤ y - 1`, `1 + t ≤ e^t`).
* `exp_laps`: `InvolutionLoopRate.laps_two_sided` for this channel, every hypothesis
  discharged: for `0 < s < δ∞`, the first cancellation index `m`, any `0 < g ≤ w*`,
  `K = K(w* + g)`: `(1+K)^(N+1)|s - s*| < g → N < m` and `δ∞ ≤ (1+κ)^(N+1)|s - s*| → m ≤ N`.
  `exp_resolution`: for `s ≠ s*` such an `m` exists, odd (latched) iff `s > s*`.
  `exp_laps_log`: the same in logarithmic form.

Not covered: noise; asymmetric (`δ↑ ≠ δ↓`) exp channels; that a LUT + route is an exp
channel, or which `τ, T_p` it has (reading TLOOP as `δ∞` is a modelling choice); the tight
local rate `1 + δ'(-w*)` (the theorem's bounds use the global slope extremes on the
domains above, so they are loose: notes/A-inv-exp.md has the numbers).
-/

namespace Formal.Core.DelayInvolution.ExpReal
open Formal.Core.DelayInvolution Formal.Core.InvolutionLoop Formal.Core.InvolutionLoop.Rate

/-- Real `exp`/`log`, scaled by `τ`: `E x = e^{x/τ}`, `L y = τ ln y`. -/
noncomputable def realExpLog (τ : ℝ) (hτ : 0 < τ) : ExpLog where
  E := fun x => Real.exp (x / τ)
  L := fun y => τ * Real.log y
  E_pos := fun _ => Real.exp_pos _
  E_strictMono := fun _ _ h => Real.exp_lt_exp.mpr (div_lt_div_of_pos_right h hτ)
  E_zero := by show Real.exp (0 / τ) = 1; rw [zero_div, Real.exp_zero]
  L_E := fun x => by
    show τ * Real.log (Real.exp (x / τ)) = x
    rw [Real.log_exp]; field_simp
  E_L := fun y hy => by
    show Real.exp (τ * Real.log y / τ) = y
    rw [mul_div_cancel_left₀ _ (ne_of_gt hτ), Real.exp_log hy]

/-- The real exp-channel as an involution pair. -/
noncomputable def expR (τ Tp : ℝ) (hτ : 0 < τ) (hTp : 0 < Tp) : InvolutionPair :=
  (realExpLog τ hτ).expPair Tp hTp

section
variable {τ Tp : ℝ} (hτ : 0 < τ) (hTp : 0 < Tp)

/-- `u(T) = e^{-(T + T_p)/τ}`: the distance of the previous ramp from its rail, doubled. -/
noncomputable def uu (τ Tp T : ℝ) : ℝ := Real.exp (-(T + Tp) / τ)

theorem expR_up (T : ℝ) : (expR τ Tp hτ hTp).up T = Tp + τ * Real.log (2 - uu τ Tp T) := rfl
theorem expR_down (T : ℝ) : (expR τ Tp hτ hTp).down T = Tp + τ * Real.log (2 - uu τ Tp T) := rfl
theorem expR_infUp : (expR τ Tp hτ hTp).infUp = Tp + τ * Real.log 2 := rfl
theorem expR_infDown : (expR τ Tp hτ hTp).infDown = Tp + τ * Real.log 2 := rfl

theorem expR_delayAt (n : ℕ) (T : ℝ) :
    (expR τ Tp hτ hTp).delayAt n T = Tp + τ * Real.log (2 - uu τ Tp T) := by
  unfold InvolutionPair.delayAt; split <;> rfl

theorem expR_infAt (n : ℕ) : (expR τ Tp hτ hTp).infAt n = Tp + τ * Real.log 2 := by
  unfold InvolutionPair.infAt; split <;> rfl

theorem uu_lt_two (hτ : 0 < τ) {T : ℝ} (hT : -(Tp + τ * Real.log 2) < T) : uu τ Tp T < 2 := by
  have := (realExpLog τ hτ).exp_dom Tp (T := T) hT
  have e : (realExpLog τ hτ).E (-(T + Tp)) = uu τ Tp T := rfl
  linarith

theorem uu_pos (T : ℝ) : 0 < uu τ Tp T := Real.exp_pos _

/-- `u(a) = u(b) · e^{(b-a)/τ}`. -/
theorem uu_shift (hτ : 0 < τ) (a b : ℝ) : uu τ Tp a = uu τ Tp b * Real.exp ((b - a) / τ) := by
  unfold uu; rw [← Real.exp_add]; congr 1; field_simp; ring

/-! ## The paper-style form, and a form that is not an involution -/

/-- `δ(T) = δ∞ + τ ln(1 - e^{-(T + δ∞)/τ})` on the domain `T > -δ∞`. -/
theorem expR_paper {T : ℝ} (hT : -(Tp + τ * Real.log 2) < T) :
    (expR τ Tp hτ hTp).up T =
      (Tp + τ * Real.log 2) + τ * Real.log (1 - Real.exp (-(T + (Tp + τ * Real.log 2)) / τ)) := by
  rw [expR_up]
  have hu := uu_lt_two hτ hT
  have e : Real.exp (-(T + (Tp + τ * Real.log 2)) / τ) = uu τ Tp T / 2 := by
    unfold uu
    rw [show -(T + (Tp + τ * Real.log 2)) / τ = -(T + Tp) / τ - Real.log 2 by
      field_simp; ring, Real.exp_sub, Real.exp_log (by norm_num)]
  rw [e, show (1 : ℝ) - uu τ Tp T / 2 = (2 - uu τ Tp T) / 2 by ring,
    Real.log_div (by linarith) (by norm_num)]
  ring

/-- The variant `δ(T) = δ∞ + τ ln(1 - e^{-(T + δ∞ - T_p)/τ})` (with `δ∞ = T_p + τ ln 2`). -/
noncomputable def badDelay (τ Tp T : ℝ) : ℝ :=
  (Tp + τ * Real.log 2) + τ * Real.log (1 - Real.exp (-(T + (Tp + τ * Real.log 2) - Tp) / τ))

/-- **Negative result.** For `0 < T_p < τ ln 2` the variant violates the involution law
at `T = 0`: `-δ(-δ(0)) ≠ 0`. -/
theorem bad_not_involution (hτ : 0 < τ) (hTp : 0 < Tp) (hlt : Tp < τ * Real.log 2) :
    -badDelay τ Tp (-badDelay τ Tp 0) ≠ 0 := by
  have h0 : badDelay τ Tp 0 = Tp := by
    unfold badDelay
    rw [show -((0 : ℝ) + (Tp + τ * Real.log 2) - Tp) / τ = -Real.log 2 by field_simp; ring,
      Real.exp_neg, Real.exp_log (by norm_num), show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num,
      Real.log_inv]
    ring
  rw [h0]
  intro hc
  set a := Real.exp (Tp / τ) with ha
  have ha1 : 1 < a := Real.one_lt_exp_iff.mpr (div_pos hTp hτ)
  have ha2 : a < 2 := by
    rw [ha, show (2 : ℝ) = Real.exp (Real.log 2) from (Real.exp_log (by norm_num)).symm]
    exact Real.exp_lt_exp.mpr (by rw [div_lt_iff₀ hτ]; linarith)
  have e1 : Real.exp (-(-Tp + (Tp + τ * Real.log 2) - Tp) / τ) = 2⁻¹ * a := by
    rw [show -(-Tp + (Tp + τ * Real.log 2) - Tp) / τ = Tp / τ + -Real.log 2 by field_simp; ring,
      Real.exp_add, Real.exp_neg, Real.exp_log (by norm_num)]; ring
  unfold badDelay at hc
  rw [e1] at hc
  have hp : 0 < 1 - 2⁻¹ * a := by linarith
  -- `Tp + τ ln 2 + τ ln(1 - a/2) = 0`, i.e. `τ ln(2 - a) = -Tp`
  have e2 : Real.log 2 + Real.log (1 - 2⁻¹ * a) = Real.log (2 - a) := by
    rw [← Real.log_mul (by norm_num) (ne_of_gt hp)]; congr 1; ring
  have hl : Real.log (2 - a) = -(Tp / τ) := by
    have : τ * (Real.log 2 + Real.log (1 - 2⁻¹ * a)) = -Tp := by linarith
    rw [e2] at this; field_simp; linarith
  have h2 : 2 - a = a⁻¹ := by
    rw [← Real.exp_log (show 0 < 2 - a by linarith), hl, Real.exp_neg]
  have : (a - 1) ^ 2 = 0 := by
    have ha0 : a ≠ 0 := by linarith
    field_simp at h2; nlinarith
  have : a - 1 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  linarith

/-! ## δmin and the single-pulse threshold -/

theorem expR_dmin : (expR τ Tp hτ hTp).dmin = Tp :=
  InvolutionPair.exp_dmin_eq (realExpLog τ hτ) Tp hTp

/-- **Single pulse.** `[a, a + Δ]` (`Δ > 0`) is cancelled iff `Δ ≤ τ ln 2`; otherwise it
comes out `δ∞ = T_p + τ ln 2` later with width `pulseWidth Δ`. -/
theorem expR_pulse (a Δ : ℝ) (hΔ : 0 < Δ) :
    (expR τ Tp hτ hTp).channel [a, a + Δ] = if Δ ≤ τ * Real.log 2 then []
      else [a + (Tp + τ * Real.log 2),
        a + (Tp + τ * Real.log 2) + (expR τ Tp hτ hTp).pulseWidth Δ] :=
  InvolutionPair.exp_channel_pulse (realExpLog τ hτ) Tp hTp a Δ hΔ

theorem expR_pulse_cancel_iff (a Δ : ℝ) (hΔ : 0 < Δ) :
    (expR τ Tp hτ hTp).channel [a, a + Δ] = [] ↔ Δ ≤ τ * Real.log 2 := by
  rw [expR_pulse hτ hTp a Δ hΔ]
  split
  · exact ⟨fun _ => by assumption, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by simp), fun h => absurd h (by assumption)⟩

/-! ## The stationary train of the OR loop, in closed form -/

/-- `x = (√(1 + 8 e^{T_p/τ}) - 1)/2`, the positive root of `x² + x = 2 e^{T_p/τ}`. -/
noncomputable def xs (τ Tp : ℝ) : ℝ := (Real.sqrt (1 + 8 * Real.exp (Tp / τ)) - 1) / 2

/-- `w* = τ ln x`. -/
noncomputable def wStar (τ Tp : ℝ) : ℝ := τ * Real.log (xs τ Tp)

theorem xs_quad : xs τ Tp ^ 2 + xs τ Tp = 2 * Real.exp (Tp / τ) := by
  unfold xs
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + 8 * Real.exp (Tp / τ) by
    linarith [Real.exp_pos (Tp / τ)])
  nlinarith

theorem xs_bounds (hτ : 0 < τ) (hTp : 0 < Tp) : 1 < xs τ Tp ∧ xs τ Tp < Real.exp (Tp / τ) := by
  have ha1 : 1 < Real.exp (Tp / τ) := Real.one_lt_exp_iff.mpr (div_pos hTp hτ)
  have hq := xs_quad (τ := τ) (Tp := Tp)
  set a := Real.exp (Tp / τ)
  set x := xs τ Tp
  have hx0 : 0 ≤ x := by
    unfold x xs
    have : (1 : ℝ) ≤ Real.sqrt (1 + 8 * a) := by
      have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + 8 * a by linarith)
      rwa [Real.sqrt_one] at h
    linarith
  constructor <;> nlinarith

theorem wStar_pos (hτ : 0 < τ) (hTp : 0 < Tp) : 0 < wStar τ Tp :=
  mul_pos hτ (Real.log_pos (xs_bounds hτ hTp).1)

theorem wStar_lt_Tp (hτ : 0 < τ) (hTp : 0 < Tp) : wStar τ Tp < Tp := by
  have h := Real.log_lt_log (by linarith [(xs_bounds hτ hTp).1]) (xs_bounds hτ hTp).2
  rw [Real.log_exp] at h
  unfold wStar
  have := (lt_div_iff₀' hτ).mp h
  linarith

theorem exp_wStar (hτ : 0 < τ) (hTp : 0 < Tp) : Real.exp (wStar τ Tp / τ) = xs τ Tp := by
  unfold wStar
  rw [mul_div_cancel_left₀ _ (ne_of_gt hτ), Real.exp_log (by linarith [(xs_bounds hτ hTp).1])]

/-- The train equation `δ(-w*) = 2 w*`. -/
theorem expR_up_wStar : (expR τ Tp hτ hTp).up (-wStar τ Tp) = 2 * wStar τ Tp := by
  rw [expR_up]
  have hx := xs_bounds hτ hTp
  have hq := xs_quad (τ := τ) (Tp := Tp)
  have ea : Real.exp (Tp / τ) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hu : uu τ Tp (-wStar τ Tp) = xs τ Tp / Real.exp (Tp / τ) := by
    unfold uu
    rw [show -(-wStar τ Tp + Tp) / τ = wStar τ Tp / τ - Tp / τ by field_simp; ring,
      Real.exp_sub, exp_wStar hτ hTp]
  have h2 : 2 - xs τ Tp / Real.exp (Tp / τ) = xs τ Tp ^ 2 / Real.exp (Tp / τ) := by
    field_simp; linarith
  rw [hu, h2, Real.log_div (pow_ne_zero 2 (ne_of_gt (by linarith [hx.1]))) ea, Real.log_pow, Real.log_exp]
  unfold wStar
  field_simp
  push_cast
  ring

/-- **Stationary train (closed form).** High = low = `w*`, and it is the only one. -/
theorem expR_stat :
    Stat (expR τ Tp hτ hTp) (wStar τ Tp) (wStar τ Tp) ∧
      ∀ h l, Stat (expR τ Tp hτ hTp) h l → h = wStar τ Tp ∧ l = wStar τ Tp := by
  have hw := wStar_pos hτ hTp
  have hwT := wStar_lt_Tp hτ hTp
  have hl2 : 0 < τ * Real.log 2 := mul_pos hτ (Real.log_pos (by norm_num))
  have S : Stat (expR τ Tp hτ hTp) (wStar τ Tp) (wStar τ Tp) :=
    { h_pos := hw, l_pos := hw
      h_lt := by rw [expR_infDown]; linarith
      l_lt := by rw [expR_infUp]; linarith
      up_eq := by rw [expR_up_wStar]; ring
      down_eq := by
        show (expR τ Tp hτ hTp).up (-wStar τ Tp) = _
        rw [expR_up_wStar]; ring }
  exact ⟨S, fun h l S' => stat_unique S' S⟩

/-- **The critical runt.** `s* = δ∞ - w* = T_p + τ ln(2/x)`. -/
theorem expR_crit :
    crit (expR τ Tp hτ hTp) (wStar τ Tp) = Tp + τ * Real.log (2 / xs τ Tp) := by
  unfold crit wStar
  rw [expR_infUp, Real.log_div (by norm_num) (by linarith [(xs_bounds hτ hTp).1])]
  ring

/-! ## Slope bounds -/

/-- `ln y - ln x ≥ (y - x)/y` and `≤ (y - x)/x`. -/
theorem log_sub_bounds {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (y - x) / y ≤ Real.log y - Real.log x ∧ Real.log y - Real.log x ≤ (y - x) / x := by
  have h1 := Real.log_le_sub_one_of_pos (div_pos hx hy)
  have h2 := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt hy)] at h1
  rw [Real.log_div (ne_of_gt hy) (ne_of_gt hx)] at h2
  constructor
  · have : x / y - 1 = -((y - x) / y) := by field_simp; ring
    linarith
  · have : y / x - 1 = (y - x) / x := by field_simp
    linarith

/-- `κ = q/(2 - q)`, `q = e^{-T_p/τ}`: `δ'(0)`, the smallest slope on `(-δ∞, 0]`. -/
noncomputable def kappaE (τ Tp : ℝ) : ℝ :=
  Real.exp (-Tp / τ) / (2 - Real.exp (-Tp / τ))

/-- `K(M) = r/(2 - r)`, `r = e^{(M - T_p)/τ}`: `δ'(-M)`, the largest slope on `[-M, ∞)`. -/
noncomputable def KE (τ Tp M : ℝ) : ℝ :=
  Real.exp ((M - Tp) / τ) / (2 - Real.exp ((M - Tp) / τ))

theorem q_lt_one (hτ : 0 < τ) (hTp : 0 < Tp) : Real.exp (-Tp / τ) < 1 := by
  rw [Real.exp_lt_one_iff]; exact div_neg_of_neg_of_pos (by linarith) hτ

theorem kappaE_pos (hτ : 0 < τ) (hTp : 0 < Tp) : 0 < kappaE τ Tp := by
  unfold kappaE; have := q_lt_one hτ hTp
  exact div_pos (Real.exp_pos _) (by linarith)

theorem r_lt_two (hτ : 0 < τ) {M : ℝ} (hM : M < Tp + τ * Real.log 2) : Real.exp ((M - Tp) / τ) < 2 := by
  rw [show (2 : ℝ) = Real.exp (Real.log 2) from (Real.exp_log (by norm_num)).symm]
  exact Real.exp_lt_exp.mpr (by rw [div_lt_iff₀ hτ]; linarith)

theorem KE_nonneg (hτ : 0 < τ) {M : ℝ} (hM : M < Tp + τ * Real.log 2) : 0 ≤ KE τ Tp M := by
  unfold KE; have := r_lt_two hτ hM
  exact le_of_lt (div_pos (Real.exp_pos _) (by linarith))

/-- Difference of delays through `u`. -/
theorem up_sub {a b : ℝ} (ha : -(Tp + τ * Real.log 2) < a) (hb : -(Tp + τ * Real.log 2) < b) :
    (expR τ Tp hτ hTp).up b - (expR τ Tp hτ hTp).up a =
      τ * (Real.log (2 - uu τ Tp b) - Real.log (2 - uu τ Tp a)) := by
  rw [expR_up, expR_up]; ring

/-- **Slope lower bound.** For `-δ∞ < a ≤ b ≤ 0`: `κ (b - a) ≤ δ(b) - δ(a)`. -/
theorem slope_lower {a b : ℝ} (ha : -(Tp + τ * Real.log 2) < a) (hab : a ≤ b) (hb : b ≤ 0) :
    kappaE τ Tp * (b - a) ≤ (expR τ Tp hτ hTp).up b - (expR τ Tp hτ hTp).up a := by
  have hb' : -(Tp + τ * Real.log 2) < b := by linarith
  have hua := uu_lt_two hτ ha
  have hub := uu_lt_two hτ hb'
  have hub0 := uu_pos (τ := τ) (Tp := Tp) b
  rw [up_sub hτ hTp ha hb']
  obtain ⟨hl, _⟩ := log_sub_bounds (x := 2 - uu τ Tp a) (y := 2 - uu τ Tp b)
    (by linarith) (by linarith)
  -- `u a - u b ≥ u b (b - a)/τ`
  have hexp := Real.add_one_le_exp ((b - a) / τ)
  have hsh := uu_shift (Tp := Tp) hτ a b
  have hd : uu τ Tp b * ((b - a) / τ) ≤ uu τ Tp a - uu τ Tp b := by
    rw [hsh]; nlinarith
  -- `u b ≥ q`
  have hq : Real.exp (-Tp / τ) ≤ uu τ Tp b := by
    unfold uu; apply Real.exp_le_exp_of_le
    apply div_le_div_of_nonneg_right _ (le_of_lt hτ); linarith
  have hq1 := q_lt_one hτ hTp
  set q := Real.exp (-Tp / τ)
  set ub := uu τ Tp b
  set ua := uu τ Tp a
  have hba : 0 ≤ b - a := by linarith
  -- chain: κ(b-a) ≤ ub/(2-ub)·(b-a) ≤ τ (ua-ub)/(2-ub) ≤ τ(log … )
  have k1 : kappaE τ Tp * (b - a) ≤ ub / (2 - ub) * (b - a) := by
    apply mul_le_mul_of_nonneg_right _ hba
    unfold kappaE
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have k2 : ub / (2 - ub) * (b - a) ≤ τ * ((ua - ub) / (2 - ub)) := by
    rw [show ub / (2 - ub) * (b - a) = τ * ((ub * ((b - a) / τ)) / (2 - ub)) by
      field_simp]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hτ)
    exact div_le_div_of_nonneg_right hd (by linarith)
  have k3 : τ * ((ua - ub) / (2 - ub)) ≤ τ * (Real.log (2 - ub) - Real.log (2 - ua)) := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hτ)
    rw [show ua - ub = (2 - ub) - (2 - ua) by ring]; exact hl
  linarith

/-- **Slope upper bound.** For `-M ≤ a ≤ b` with `M < δ∞`: `δ(b) - δ(a) ≤ K(M) (b - a)`. -/
theorem slope_upper {M a b : ℝ} (hM : M < Tp + τ * Real.log 2) (ha : -M ≤ a) (hab : a ≤ b) :
    (expR τ Tp hτ hTp).up b - (expR τ Tp hτ hTp).up a ≤ KE τ Tp M * (b - a) := by
  have ha' : -(Tp + τ * Real.log 2) < a := by linarith
  have hb' : -(Tp + τ * Real.log 2) < b := by linarith
  have hua := uu_lt_two hτ ha'
  have hub := uu_lt_two hτ hb'
  have hua0 := uu_pos (τ := τ) (Tp := Tp) a
  have hub0 := uu_pos (τ := τ) (Tp := Tp) b
  rw [up_sub hτ hTp ha' hb']
  obtain ⟨_, hu⟩ := log_sub_bounds (x := 2 - uu τ Tp a) (y := 2 - uu τ Tp b)
    (by linarith) (by linarith)
  -- `u a - u b ≤ u a (b - a)/τ`, from `1 - e^{-t} ≤ t`
  have hexp := Real.add_one_le_exp (-((b - a) / τ))
  have hsh := uu_shift (Tp := Tp) hτ b a
  have hd : uu τ Tp a - uu τ Tp b ≤ uu τ Tp a * ((b - a) / τ) := by
    rw [hsh, show (a - b) / τ = -((b - a) / τ) by ring]; nlinarith
  have hr : uu τ Tp a ≤ Real.exp ((M - Tp) / τ) := by
    unfold uu; apply Real.exp_le_exp_of_le
    apply div_le_div_of_nonneg_right _ (le_of_lt hτ); linarith
  have hr2 := r_lt_two hτ hM
  set r := Real.exp ((M - Tp) / τ)
  set ub := uu τ Tp b
  set ua := uu τ Tp a
  have hba : 0 ≤ b - a := by linarith
  have k3 : τ * (Real.log (2 - ub) - Real.log (2 - ua)) ≤ τ * ((ua - ub) / (2 - ua)) := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hτ)
    rw [show ua - ub = (2 - ub) - (2 - ua) by ring]; exact hu
  have k2 : τ * ((ua - ub) / (2 - ua)) ≤ ua / (2 - ua) * (b - a) := by
    rw [show ua / (2 - ua) * (b - a) = τ * ((ua * ((b - a) / τ)) / (2 - ua)) by
      field_simp]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hτ)
    exact div_le_div_of_nonneg_right hd (by linarith)
  have k1 : ua / (2 - ua) * (b - a) ≤ KE τ Tp M * (b - a) := by
    apply mul_le_mul_of_nonneg_right _ hba
    unfold KE
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  linarith

/-- `H_LIP` in `InvolutionLoopRate`'s form. -/
theorem expR_lip {M : ℝ} (hM : M < Tp + τ * Real.log 2) (n : ℕ) (a b : ℝ)
    (ha : -M ≤ a) (hb : -M ≤ b) :
    |(expR τ Tp hτ hTp).delayAt n a - (expR τ Tp hτ hTp).delayAt n b| ≤
      KE τ Tp M * |a - b| := by
  have hd : ∀ T, (expR τ Tp hτ hTp).delayAt n T = (expR τ Tp hτ hTp).up T := fun T => by
    rw [expR_delayAt, expR_up]
  rw [hd, hd]
  have hdom : -(Tp + τ * Real.log 2) < -M := by linarith
  rcases le_total a b with c | c
  · have h1 := slope_upper hτ hTp hM ha c
    have h0 := le_of_lt_or_eq ((lt_or_eq_of_le c).imp
      (fun c' => (expR τ Tp hτ hTp).up_strictMono a b (by
        show -(Tp + τ * Real.log 2) < a; linarith) c') (fun e => by rw [e]))
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
  · have h1 := slope_upper hτ hTp hM hb c
    have h0 := le_of_lt_or_eq ((lt_or_eq_of_le c).imp
      (fun c' => (expR τ Tp hτ hTp).up_strictMono b a (by
        show -(Tp + τ * Real.log 2) < b; linarith) c') (fun e => by rw [e]))
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith

/-- `H_SLOPE` in `InvolutionLoopRate`'s form. -/
theorem expR_slope (n : ℕ) (a b : ℝ) (ha : -(expR τ Tp hτ hTp).infAt (n + 1) < a)
    (hab : a ≤ b) (hb : b ≤ 0) :
    kappaE τ Tp * (b - a) ≤
      (expR τ Tp hτ hTp).delayAt n b - (expR τ Tp hτ hTp).delayAt n a := by
  rw [expR_infAt] at ha
  rw [expR_delayAt, expR_delayAt, ← expR_up hτ hTp, ← expR_up hτ hTp]
  exact slope_lower hτ hTp ha hab hb

/-! ## The rate law for the exp-channel loop -/

theorem two_wStar_lt (hτ : 0 < τ) (hTp : 0 < Tp) : 2 * wStar τ Tp < Tp + τ * Real.log 2 := by
  have h := (expR τ Tp hτ hTp).up_lt (-wStar τ Tp) (by
    rw [expR_infDown]
    have := wStar_lt_Tp hτ hTp
    have : 0 < τ * Real.log 2 := mul_pos hτ (Real.log_pos (by norm_num))
    linarith)
  rw [expR_up_wStar, expR_infUp] at h
  exact h

/-- **Rate law, exp-channel.** Loop of `InvolutionLoop` (runt `[0, s)` ORed into the real
exp-channel `expR τ Tp`, fed back), `0 < s < δ∞`, `m` the first cancellation index,
`0 < g ≤ w*`, `K = K(w* + g)`, `κ = κ(T_p, τ)`.  Then
`(1+K)^(N+1)|s - s*| < g → N < m` and `δ∞ ≤ (1+κ)^(N+1)|s - s*| → m ≤ N`. -/
theorem exp_laps {s g : ℝ} (hs0 : 0 < s) (hsI : s < Tp + τ * Real.log 2)
    (hg0 : 0 < g) (hgw : g ≤ wStar τ Tp)
    {m : ℕ} (hcm : Chain (expR τ Tp hτ hTp) s m) (hm : wd (expR τ Tp hτ hTp) s m ≤ 0)
    (N : ℕ) :
    ((1 + KE τ Tp (wStar τ Tp + g)) ^ (N + 1) *
        |s - crit (expR τ Tp hτ hTp) (wStar τ Tp)| < g → N < m) ∧
    (Tp + τ * Real.log 2 ≤ (1 + kappaE τ Tp) ^ (N + 1) *
        |s - crit (expR τ Tp hτ hTp) (wStar τ Tp)| → m ≤ N) := by
  have hM : wStar τ Tp + g < Tp + τ * Real.log 2 := by
    have := two_wStar_lt hτ hTp; linarith
  have S := (expR_stat hτ hTp).1
  have L := laps_two_sided (P := expR τ Tp hτ hTp) (M := wStar τ Tp + g) (g := g) S
    (KE_nonneg hτ hM) (le_of_lt (kappaE_pos hτ hTp)) (expR_lip hτ hTp hM) (expR_slope hτ hTp)
    hgw hgw (le_refl _) (le_refl _) hs0 (by rw [expR_infUp]; exact hsI) hcm hm N
  rw [expR_infUp, expR_infDown, max_self] at L
  exact L

/-- **Resolution, exp-channel.** For `0 < s < δ∞`, `s ≠ s*`: the run has a first
cancellation `m`, which is odd (q latched at 1) iff `s > s*`, and `m` obeys `exp_laps`. -/
theorem exp_resolution {s : ℝ} (hs0 : 0 < s) (hsI : s < Tp + τ * Real.log 2)
    (hne : s ≠ crit (expR τ Tp hτ hTp) (wStar τ Tp)) :
    ∃ m : ℕ, Chain (expR τ Tp hτ hTp) s m ∧ wd (expR τ Tp hτ hTp) s m ≤ 0 ∧
      (m % 2 = 1 ↔ crit (expR τ Tp hτ hTp) (wStar τ Tp) < s) := by
  have S := (expR_stat hτ hTp).1
  rcases lt_or_gt_of_ne hne with c | c
  · obtain ⟨k, hc, hw⟩ := lost S hs0 c
    exact ⟨2 * k, hc, hw, ⟨fun h => absurd h (by omega), fun h => absurd h (by linarith)⟩⟩
  · obtain ⟨k, hc, hw⟩ := latch S c (by rw [expR_infUp]; exact hsI)
    exact ⟨2 * k + 1, hc, hw, ⟨fun _ => c, fun _ => by omega⟩⟩

/-- **Logarithmic form.** With `d = |s - s*| > 0`: if `(N+1) ln(1+K) < ln(g/d)` then
`N < m`; if `ln(δ∞/d) ≤ (N+1) ln(1+κ)` then `m ≤ N`.  So
`ln(g/d)/ln(1+K) - 1 ≤ m ≤ ⌈ln(δ∞/d)/ln(1+κ)⌉ - 1` (read off for the least such `N`). -/
theorem exp_laps_log {s g : ℝ} (hs0 : 0 < s) (hsI : s < Tp + τ * Real.log 2)
    (hg0 : 0 < g) (hgw : g ≤ wStar τ Tp)
    (hne : s ≠ crit (expR τ Tp hτ hTp) (wStar τ Tp))
    {m : ℕ} (hcm : Chain (expR τ Tp hτ hTp) s m) (hm : wd (expR τ Tp hτ hTp) s m ≤ 0)
    (N : ℕ) :
    (((N : ℝ) + 1) * Real.log (1 + KE τ Tp (wStar τ Tp + g)) <
        Real.log (g / |s - crit (expR τ Tp hτ hTp) (wStar τ Tp)|) → N < m) ∧
    (Real.log ((Tp + τ * Real.log 2) / |s - crit (expR τ Tp hτ hTp) (wStar τ Tp)|) ≤
        ((N : ℝ) + 1) * Real.log (1 + kappaE τ Tp) → m ≤ N) := by
  have hM : wStar τ Tp + g < Tp + τ * Real.log 2 := by
    have := two_wStar_lt hτ hTp; linarith
  set d := |s - crit (expR τ Tp hτ hTp) (wStar τ Tp)|
  have hd : 0 < d := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hK := KE_nonneg hτ hM
  have hk := kappaE_pos hτ hTp
  have hI : 0 < Tp + τ * Real.log 2 := by
    have : 0 < τ * Real.log 2 := mul_pos hτ (Real.log_pos (by norm_num)); linarith
  obtain ⟨L1, L2⟩ := exp_laps hτ hTp hs0 hsI hg0 hgw hcm hm N
  have pw : ∀ b : ℝ, 0 < b → Real.log (b ^ (N + 1)) = ((N : ℝ) + 1) * Real.log b := fun b _ => by
    rw [Real.log_pow]; push_cast; ring
  refine ⟨fun h => L1 ?_, fun h => L2 ?_⟩
  · rw [← pw _ (by linarith), Real.log_div (ne_of_gt hg0) (ne_of_gt hd)] at h
    have h' : Real.log ((1 + KE τ Tp (wStar τ Tp + g)) ^ (N + 1) * d) < Real.log g := by
      rw [Real.log_mul (ne_of_gt (pow_pos (by linarith) _)) (ne_of_gt hd)]; linarith
    exact (Real.log_lt_log_iff (mul_pos (pow_pos (by linarith) _) hd) hg0).mp h'
  · rw [← pw _ (by linarith), Real.log_div (ne_of_gt hI) (ne_of_gt hd)] at h
    have h' : Real.log (Tp + τ * Real.log 2) ≤
        Real.log ((1 + kappaE τ Tp) ^ (N + 1) * d) := by
      rw [Real.log_mul (ne_of_gt (pow_pos (by linarith) _)) (ne_of_gt hd)]; linarith
    exact (Real.log_le_log_iff hI (mul_pos (pow_pos (by linarith) _) hd)).mp h'

end

end Formal.Core.DelayInvolution.ExpReal
