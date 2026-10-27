import Formal.Cells.ArbAnalog

/-!
# Track 7k: closing the analog probe's gaps (non-vacuity, matching rates)

Part 1 (gap (a) of `B-arb-analog.md`): an explicit state-LUT transfer function
`Fx` (6-Lipschitz, equal to the REAL INIT `qNext` at all 8 rail corners), an
explicit request waveform `S0 = rampStim` (r1 high, r2 a unit ramp starting at
the timing `s`), and the closed-form solution family `xsol` (set phase:
`1 - exp(-∫P)`; hold phase: a two-sided logistic `psi`), proved to be a
solution on `[0, ∞)` for every `s` (`xsol_isSol`). Every hypothesis of
`analog_arbiter_not_exclusive`, `metastable_forever` and `aperture_upper_bound`
is then PROVED for it (`inst_H_ENDS`, `inst_hold`, `inst_heq`, `inst_hvs`,
`inst_gain_up/dn`, `inst_spread`), and the three theorems are instantiated
(`inst_not_exclusive`, `inst_metastable`, `inst_aperture_upper`). So the
theorems of `ArbAnalog` are not vacuous. Global existence is obtained from the
closed form, not from a general Picard-Lindelof on `[0, ∞)`.

Part 2 (gap (b)): `sandwich_up/dn`, `undecided_of_close`,
`aperture_lower_bound_local`: with a two-sided local gain bound
`g ≤ gain ≤ gh` near `vs`, the bad-timing window CONTAINS
`s* ± (r/C) exp(-(gh-1)(T-tw)/tau)` (local rate, not the global `(L+1)/tau`),
matching `aperture_upper_bound`'s `s* ± (r/c) exp(-(g-1)(T-tw)/tau)`. For the
instance (`inst_window_lower`, `inst_undecided_exists`): `gh = 2` (the exact
slope at mid-rail), any `g < 2 - 2r`.

Part 3 (gap (c)): H_SPREAD is DERIVED for the instance from the closed form
(`inst_spread`, slope `c = exp(-9/4)`); no general derivation from `F`.
-/

open Set Filter Real
open scoped Topology NNReal

namespace Formal.Cells.ArbAnalog2

open Formal.Cells.ArbAnalog

/-! ## Part 1: an explicit transfer function -/

/-- Clamp to `[0, 1]` (rail-limited voltage). -/
noncomputable def sat (x : ℝ) : ℝ := max 0 (min 1 x)

lemma sat_lip : LipschitzWith 1 sat := (LipschitzWith.id.const_min 1).const_max 0

lemma abs_sat_sub (x y : ℝ) : |sat x - sat y| ≤ |x - y| := by
  have := sat_lip.dist_le_mul x y
  simpa [Real.dist_eq] using this

lemma sat_nonneg (x : ℝ) : 0 ≤ sat x := le_max_left _ _
lemma sat_le_one (x : ℝ) : sat x ≤ 1 := max_le zero_le_one (min_le_left _ _)
lemma sat_of_mem {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : sat x = x := by
  unfold sat; rw [min_eq_right h1, max_eq_right h0]
lemma sat_of_nonpos {x : ℝ} (h : x ≤ 0) : sat x = 0 := by
  unfold sat; rw [min_eq_right (by linarith), max_eq_left h]
lemma sat_of_ge_one {x : ℝ} (h : 1 ≤ x) : sat x = 1 := by
  unfold sat; rw [min_eq_left h, max_eq_right zero_le_one]
lemma abs_sat_le (x : ℝ) : |sat x| ≤ 1 := by
  rw [abs_of_nonneg (sat_nonneg x)]; exact sat_le_one x

/-- Offset of the clamped node voltage from mid-rail. -/
noncomputable def wh (v : ℝ) : ℝ := sat v - 1 / 2

lemma abs_wh (v : ℝ) : |wh v| ≤ 1 / 2 := by
  unfold wh; rw [abs_le]; constructor <;> linarith [sat_nonneg v, sat_le_one v]

/-- Regenerative term of the hold region: `phi v = w (1 - 2|w|)`, `w = v - 1/2`
(clamped). Slope `1` at mid-rail, zero at both rails. -/
noncomputable def phi (v : ℝ) : ℝ := wh v * (1 - 2 * |wh v|)

lemma cubic_lip {a b : ℝ} (ha : |a| ≤ 1 / 2) (hb : |b| ≤ 1 / 2) :
    |a * (1 - 2 * |a|) - b * (1 - 2 * |b|)| ≤ |a - b| := by
  rw [abs_le] at ha hb
  rcases le_total 0 a with h1 | h1 <;> rcases le_total 0 b with h2 | h2 <;>
    rcases le_total a b with h3 | h3 <;>
    simp only [abs_of_nonneg, abs_of_nonpos, h1, h2, sub_nonneg.2, sub_nonpos.2, h3] <;>
    rw [abs_le] <;> constructor <;> nlinarith

lemma abs_phi_sub (v v' : ℝ) : |phi v - phi v'| ≤ |v - v'| := by
  refine (cubic_lip (abs_wh v) (abs_wh v')).trans ?_
  unfold wh
  rw [show sat v - 1 / 2 - (sat v' - 1 / 2) = sat v - sat v' by ring]
  exact abs_sat_sub v v'

lemma abs_phi_le (v : ℝ) : |phi v| ≤ 1 := by
  unfold phi
  have h := abs_wh v
  rw [abs_mul]
  have : abs (1 - 2 * |wh v|) ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [abs_nonneg (wh v)]
  nlinarith [abs_nonneg (wh v), abs_nonneg (1 - 2 * |wh v|)]

/-- Net set (`> 0`) / reset (`< 0`) drive of the requests, thresholded at mid-rail. -/
noncomputable def Pd (a b : ℝ) : ℝ := sat (2 * a) - sat (2 * b)
/-- Hold-region weight: both requests above mid-rail. -/
noncomputable def Hd (a b : ℝ) : ℝ := sat (2 * min a b - 1)

/-- **The concrete state-LUT transfer function.**
`F(a,b,v) = v + H(a,b) phi(v) + max(P,0) (1 - sat v) - max(-P,0) sat v`:
the hold region regenerates around mid-rail (`phi`), a set drive pulls `v` to 1,
a reset drive pulls it to 0. It is 6-Lipschitz and equals the real INIT
(`qNext`, evaluated with `lutB`) at all 8 rail corners. -/
noncomputable def Fx (a b v : ℝ) : ℝ :=
  v + Hd a b * phi v + max (Pd a b) 0 * (1 - sat v) - max (-Pd a b) 0 * sat v

/-- `|x y - x' y'| ≤ |x - x'| + |y - y'|` when `|y| ≤ 1` and `|x'| ≤ 1`. -/
lemma abs_mul_sub_mul_le {x y x' y' : ℝ} (hy : |y| ≤ 1) (hx' : |x'| ≤ 1) :
    |x * y - x' * y'| ≤ |x - x'| + |y - y'| := by
  have e : x * y - x' * y' = (x - x') * y + x' * (y - y') := by ring
  rw [e]
  calc _ ≤ |(x - x') * y| + |x' * (y - y')| := abs_add_le _ _
    _ = |x - x'| * |y| + |x'| * |y - y'| := by rw [abs_mul, abs_mul]
    _ ≤ |x - x'| * 1 + 1 * |y - y'| := by
        gcongr
    _ = _ := by ring

lemma abs_Pd_sub (a b a' b' : ℝ) : |Pd a b - Pd a' b'| ≤ 2 * (|a - a'| + |b - b'|) := by
  unfold Pd
  have h1 := abs_sat_sub (2 * a) (2 * a')
  have h2 := abs_sat_sub (2 * b) (2 * b')
  rw [show 2 * a - 2 * a' = 2 * (a - a') by ring, abs_mul, abs_two] at h1
  rw [show 2 * b - 2 * b' = 2 * (b - b') by ring, abs_mul, abs_two] at h2
  calc _ = |(sat (2 * a) - sat (2 * a')) - (sat (2 * b) - sat (2 * b'))| := by ring_nf
    _ ≤ |sat (2 * a) - sat (2 * a')| + |sat (2 * b) - sat (2 * b')| := abs_sub _ _
    _ ≤ _ := by linarith

lemma abs_Pd_le (a b : ℝ) : |Pd a b| ≤ 1 := by
  unfold Pd; rw [abs_le]
  constructor <;> linarith [sat_nonneg (2 * a), sat_le_one (2 * a),
    sat_nonneg (2 * b), sat_le_one (2 * b)]

lemma abs_Hd_sub (a b a' b' : ℝ) : |Hd a b - Hd a' b'| ≤ 2 * (|a - a'| + |b - b'|) := by
  unfold Hd
  refine (abs_sat_sub _ _).trans ?_
  rw [show 2 * min a b - 1 - (2 * min a' b' - 1) = 2 * (min a b - min a' b') by ring,
    abs_mul, abs_two]
  have := abs_min_sub_min_le_max a b a' b'
  have h3 : max |a - a'| |b - b'| ≤ |a - a'| + |b - b'| :=
    max_le (by linarith [abs_nonneg (b - b')]) (by linarith [abs_nonneg (a - a')])
  linarith

lemma abs_Hd_le (a b : ℝ) : |Hd a b| ≤ 1 := abs_sat_le _

lemma abs_max0_sub (x y : ℝ) : |max x 0 - max y 0| ≤ |x - y| := abs_max_sub_max_le_abs x y 0

lemma abs_max0_le {x : ℝ} (h : |x| ≤ 1) : |max x 0| ≤ 1 := by
  rw [abs_of_nonneg (le_max_right _ _)]
  exact max_le (le_trans (le_abs_self x) h) zero_le_one

/-- **H_LIP for `Fx`**, with `L = 6`. -/
theorem Fx_lip (a b v a' b' v' : ℝ) :
    |Fx a b v - Fx a' b' v'| ≤ 6 * (|a - a'| + |b - b'| + |v - v'|) := by
  unfold Fx
  have hH := abs_mul_sub_mul_le (x := Hd a b) (y := phi v) (x' := Hd a' b') (y' := phi v')
    (abs_phi_le v) (abs_Hd_le a' b')
  have hS := abs_mul_sub_mul_le (x := max (Pd a b) 0) (y := 1 - sat v)
    (x' := max (Pd a' b') 0) (y' := 1 - sat v')
    (by rw [abs_le]; constructor <;> linarith [sat_nonneg v, sat_le_one v])
    (abs_max0_le (abs_Pd_le a' b'))
  have hR := abs_mul_sub_mul_le (x := max (-Pd a b) 0) (y := sat v)
    (x' := max (-Pd a' b') 0) (y' := sat v')
    (abs_sat_le v) (abs_max0_le (by rw [abs_neg]; exact abs_Pd_le a' b'))
  have h1 := abs_Hd_sub a b a' b'
  have h2 := abs_phi_sub v v'
  have h3 : |max (Pd a b) 0 - max (Pd a' b') 0| ≤ 2 * (|a - a'| + |b - b'|) :=
    (abs_max0_sub _ _).trans (abs_Pd_sub a b a' b')
  have h4 : |max (-Pd a b) 0 - max (-Pd a' b') 0| ≤ 2 * (|a - a'| + |b - b'|) := by
    refine (abs_max0_sub _ _).trans ?_
    rw [show -Pd a b - -Pd a' b' = -(Pd a b - Pd a' b') by ring, abs_neg]
    exact abs_Pd_sub a b a' b'
  have h5 : |1 - sat v - (1 - sat v')| ≤ |v - v'| := by
    rw [show 1 - sat v - (1 - sat v') = -(sat v - sat v') by ring, abs_neg]
    exact abs_sat_sub v v'
  have h6 := abs_sat_sub v v'
  have e : v + Hd a b * phi v + max (Pd a b) 0 * (1 - sat v) - max (-Pd a b) 0 * sat v -
      (v' + Hd a' b' * phi v' + max (Pd a' b') 0 * (1 - sat v') - max (-Pd a' b') 0 * sat v')
      = (v - v') + (Hd a b * phi v - Hd a' b' * phi v')
        + (max (Pd a b) 0 * (1 - sat v) - max (Pd a' b') 0 * (1 - sat v'))
        - (max (-Pd a b) 0 * sat v - max (-Pd a' b') 0 * sat v') := by ring
  rw [e]
  have t1 := abs_add_le ((v - v') + (Hd a b * phi v - Hd a' b' * phi v'))
    (max (Pd a b) 0 * (1 - sat v) - max (Pd a' b') 0 * (1 - sat v'))
  have t2 := abs_add_le (v - v') (Hd a b * phi v - Hd a' b' * phi v')
  have t3 := abs_sub ((v - v') + (Hd a b * phi v - Hd a' b' * phi v')
    + (max (Pd a b) 0 * (1 - sat v) - max (Pd a' b') 0 * (1 - sat v')))
    (max (-Pd a b) 0 * sat v - max (-Pd a' b') 0 * sat v')
  have ha := abs_nonneg (a - a')
  have hb := abs_nonneg (b - b')
  have hv := abs_nonneg (v - v')
  linarith

/-- **H_INIT for `Fx`**: at the 8 rail corners `Fx` is the real INIT. -/
theorem Fx_init (r1 r2 q : Bool) :
    Fx (rail r1) (rail r2) (rail q) = rail (qNext r1 r2 q) := by
  cases r1 <;> cases r2 <;> cases q <;>
    simp only [rail, show qNext false false false = false by decide,
      show qNext false false true = true by decide,
      show qNext false true false = false by decide,
      show qNext false true true = false by decide,
      show qNext true false false = true by decide,
      show qNext true false true = true by decide,
      show qNext true true false = false by decide,
      show qNext true true true = true by decide] <;>
    norm_num [Fx, Pd, Hd, phi, wh, sat]

/-! ## The loop and the stimulus -/

/-- The concrete loop: `tau = 1`, `F = Fx`, `L = 6`. -/
noncomputable def m0 : Loop where
  tau := 1
  F := Fx
  L := 6
  H_TAU := one_pos
  H_LIP a b v a' b' v' := by
    have := Fx_lip a b v a' b' v'
    simpa using this
  H_INIT := Fx_init

/-- The concrete request waveforms: `r1 = 1` (already high), `r2(t) = sat(t - s)`,
a unit-time ramp starting at the timing parameter `s` (slew `M = 1`). -/
noncomputable def S0 : Stim := rampStim (fun _ => 1) sat 1 sat_lip

lemma S0_u1 (s t : ℝ) : S0.u1 s t = 1 := rfl
lemma S0_u2 (s t : ℝ) : S0.u2 s t = sat (t - s) := rfl
lemma S0_M : S0.M = 1 := by simp [S0, rampStim]

lemma m0_field (a b v : ℝ) : m0.field a b v = Fx a b v - v := by
  simp [Loop.field, m0]

lemma Fx_one_low {b : ℝ} (hb0 : 0 ≤ b) (hb : b ≤ 1 / 2) (v : ℝ) :
    Fx 1 b v - v = (1 - 2 * b) * (1 - sat v) := by
  have hP : Pd 1 b = 1 - 2 * b := by
    unfold Pd; rw [sat_of_ge_one (by norm_num), sat_of_mem (by linarith) (by linarith)]
  have hH : Hd 1 b = 0 := by
    unfold Hd; rw [min_eq_right (by linarith), sat_of_nonpos (by linarith)]
  unfold Fx; rw [hP, hH, max_eq_left (by linarith), max_eq_right (by linarith)]; ring

lemma Fx_one_high {b : ℝ} (hb0 : 1 / 2 ≤ b) (hb : b ≤ 1) (v : ℝ) :
    Fx 1 b v - v = (2 * b - 1) * phi v := by
  have hP : Pd 1 b = 0 := by
    unfold Pd; rw [sat_of_ge_one (by norm_num), sat_of_ge_one (by linarith)]; ring
  have hH : Hd 1 b = 2 * b - 1 := by
    unfold Hd; rw [min_eq_right hb, sat_of_mem (by linarith) (by linarith)]
  unfold Fx; rw [hP, hH]; simp

/-! ## The closed-form solution -/

/-- Antiderivative of the set drive `P(1, sat θ) = 1 - sat(2 sat θ)`. -/
noncomputable def Bf (θ : ℝ) : ℝ := min θ (1 / 2) - (max 0 (min (1 / 2) θ)) ^ 2
/-- Antiderivative of the hold weight `H(1, sat θ) = sat(2 sat θ - 1)`. -/
noncomputable def Af (θ : ℝ) : ℝ := (max (1 / 2) (min 1 θ) - 1 / 2) ^ 2 + max (θ - 1) 0

lemma Bf_neg {θ : ℝ} (h : θ ≤ 0) : Bf θ = θ := by
  unfold Bf; rw [min_eq_left (by linarith), min_eq_right (by linarith), max_eq_left h]; ring
lemma Bf_mid {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1 / 2) : Bf θ = θ - θ ^ 2 := by
  unfold Bf; rw [min_eq_left h1, min_eq_right h1, max_eq_right h0]
lemma Bf_hi {θ : ℝ} (h : 1 / 2 ≤ θ) : Bf θ = 1 / 4 := by
  unfold Bf; rw [min_eq_right h, min_eq_left h, max_eq_right (by norm_num)]; norm_num

lemma Bf_mono : Monotone Bf := by
  intro a b hab
  rcases le_total a 0 with ha | ha
  · rw [Bf_neg ha]
    rcases le_total b 0 with hb | hb
    · rw [Bf_neg hb]; exact hab
    rcases le_total b (1 / 2) with hb' | hb'
    · rw [Bf_mid hb hb']; nlinarith
    · rw [Bf_hi hb']; linarith
  rcases le_total a (1 / 2) with ha' | ha'
  · rw [Bf_mid ha ha']
    rcases le_total b (1 / 2) with hb' | hb'
    · rw [Bf_mid (by linarith) hb']; nlinarith
    · rw [Bf_hi hb']; nlinarith
  · rw [Bf_hi ha', Bf_hi (by linarith)]

lemma Bf_le (θ : ℝ) : Bf θ ≤ 1 / 4 := by
  rcases le_total θ (1 / 2) with h | h
  · have := Bf_mono h; rwa [Bf_hi le_rfl] at this
  · rw [Bf_hi h]

lemma Af_lo {θ : ℝ} (h : θ ≤ 1 / 2) : Af θ = 0 := by
  unfold Af; rw [min_eq_right (by linarith), max_eq_left h, max_eq_right (by linarith)]; ring
lemma Af_mid {θ : ℝ} (h0 : 1 / 2 ≤ θ) (h1 : θ ≤ 1) : Af θ = (θ - 1 / 2) ^ 2 := by
  unfold Af; rw [min_eq_right h1, max_eq_right h0, max_eq_right (by linarith)]; ring
lemma Af_hi {θ : ℝ} (h : 1 ≤ θ) : Af θ = θ - 3 / 4 := by
  unfold Af; rw [min_eq_left h, max_eq_right (by norm_num), max_eq_left (by linarith)]; ring

lemma Bf_cont : Continuous Bf := by unfold Bf; fun_prop
lemma Af_cont : Continuous Af := by unfold Af; fun_prop

/-- Denominator of the hold flow. -/
noncomputable def Dn (A y : ℝ) : ℝ := 2 * |wh y| + (1 - 2 * |wh y|) * exp (-A)

lemma Dn_pos (A y : ℝ) : 0 < Dn A y := by
  unfold Dn
  have h := abs_wh y
  have he := exp_pos (-A)
  rcases eq_or_lt_of_le (abs_nonneg (wh y)) with h0 | h0
  · rw [← h0]; simpa using he
  · nlinarith

lemma Dn_le_one {A : ℝ} (hA : 0 ≤ A) (y : ℝ) : Dn A y ≤ 1 := by
  unfold Dn
  have h := abs_wh y
  have he : exp (-A) ≤ 1 := exp_le_one_iff.2 (by linarith)
  nlinarith [abs_nonneg (wh y)]

/-- Closed-form flow of the hold region `v' = phi v` (a two-sided logistic): after
hold-time `A` from `y`, the node is at `psi A y`. -/
noncomputable def psi (A y : ℝ) : ℝ := 1 / 2 + wh y / Dn A y

lemma psi_sub (A y : ℝ) : psi A y - 1 / 2 = wh y / Dn A y := by unfold psi; ring

lemma abs_psi_sub (A y : ℝ) : |psi A y - 1 / 2| ≤ 1 / 2 := by
  rw [psi_sub, abs_div, abs_of_pos (Dn_pos A y), div_le_iff₀ (Dn_pos A y)]
  unfold Dn
  have h := abs_wh y
  have he := exp_pos (-A)
  nlinarith [abs_nonneg (wh y)]

lemma psi_mem (A y : ℝ) : 0 ≤ psi A y ∧ psi A y ≤ 1 := by
  have := abs_psi_sub A y
  rw [abs_le] at this
  constructor <;> linarith

lemma psi_zero (y : ℝ) : psi 0 y = sat y := by
  unfold psi Dn wh; simp

lemma psi_hasDerivAt (A y : ℝ) : HasDerivAt (fun A => psi A y) (phi (psi A y)) A := by
  have hD : HasDerivAt (fun A => Dn A y) ((1 - 2 * |wh y|) * (exp (-A) * (-1))) A := by
    have := ((hasDerivAt_neg A).exp.const_mul (1 - 2 * |wh y|)).const_add (2 * |wh y|)
    exact this
  have hpos := Dn_pos A y
  have h2 := ((hD.inv hpos.ne').const_mul (wh y)).const_add (1 / 2)
  have hfun : (fun A => psi A y) = fun A => 1 / 2 + wh y * (Dn A y)⁻¹ := by
    funext A; simp [psi, div_eq_mul_inv]
  rw [hfun]
  convert h2 using 1
  have hw : wh (psi A y) = wh y / Dn A y := by
    obtain ⟨h0, h1⟩ := psi_mem A y
    rw [wh, sat_of_mem h0 h1, psi_sub]
  rw [phi, hw, abs_div, abs_of_pos hpos]
  have e : Dn A y - 2 * |wh y| = (1 - 2 * |wh y|) * exp (-A) := by unfold Dn; ring
  field_simp
  rw [e]; ring

lemma psi_cont {α β : ℝ → ℝ} (hα : Continuous α) (hβ : Continuous β) :
    Continuous fun t => psi (α t) (β t) := by
  have hw : Continuous fun t => wh (β t) := (sat_lip.continuous.comp hβ).sub continuous_const
  have hD : Continuous fun t => Dn (α t) (β t) := by
    unfold Dn
    exact (continuous_const.mul hw.abs).add
      ((continuous_const.sub (continuous_const.mul hw.abs)).mul
        (Real.continuous_exp.comp hα.neg))
  exact continuous_const.add (hw.div hD fun t => (Dn_pos _ _).ne')

/-- Node voltage during the set phase. -/
noncomputable def Yc (s u : ℝ) : ℝ := 1 - exp (-(Bf (u - s) - Bf (-s)))

/-- **The solution family**: set phase (`Yc`) followed by the hold flow (`psi`). -/
noncomputable def xsol (s t : ℝ) : ℝ := psi (Af (t - s) - Af (-s)) (Yc s t)

lemma Yc_mem {s u : ℝ} (hu : 0 ≤ u) : 0 ≤ Yc s u ∧ Yc s u ≤ 1 := by
  have hB : Bf (-s) ≤ Bf (u - s) := Bf_mono (by linarith)
  have h1 : exp (-(Bf (u - s) - Bf (-s))) ≤ 1 := exp_le_one_iff.2 (by linarith)
  have h2 := exp_pos (-(Bf (u - s) - Bf (-s)))
  unfold Yc; constructor <;> linarith

lemma xsol_eq_Yc {s u : ℝ} (hu : 0 ≤ u) (h : u - s ≤ 1 / 2) : xsol s u = Yc s u := by
  unfold xsol
  rw [Af_lo h, Af_lo (by linarith), sub_self, psi_zero]
  exact sat_of_mem (Yc_mem hu).1 (Yc_mem hu).2

lemma xsol_hold {s u : ℝ} (h : 1 / 2 ≤ u - s) :
    xsol s u = psi (Af (u - s) - Af (-s)) (1 - exp (-(1 / 4 - Bf (-s)))) := by
  unfold xsol Yc; rw [Bf_hi h]

lemma xsol_cont (s : ℝ) : Continuous (xsol s) := by
  unfold xsol Yc
  exact psi_cont ((Af_cont.comp (continuous_id.sub continuous_const)).sub continuous_const)
    (continuous_const.sub (Real.continuous_exp.comp
      ((Bf_cont.comp (continuous_id.sub continuous_const)).sub continuous_const).neg))

lemma ys_wh (s : ℝ) : |wh (1 - exp (-(1 / 4 - Bf (-s))))| ≤ 1 / 2 := abs_wh _

/-- The ODE holds (right derivative) at every `t ≥ 0`, for every timing `s`. -/
theorem xsol_deriv (s t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (xsol s) (m0.field (S0.u1 s t) (S0.u2 s t) (xsol s t)) (Ici t) t := by
  rw [S0_u1, S0_u2, m0_field]
  rcases lt_or_ge (t - s) (1 / 2) with hA | hB
  · -- set phase
    have hYmem := Yc_mem (s := s) ht
    rcases lt_or_ge (t - s) 0 with hA1 | hA2
    · set c := Bf (-s)
      have hg : HasDerivAt (fun u => 1 - exp (-((u - s) - c)))
          (exp (-((t - s) - c))) t := by
        have h := ((((hasDerivAt_id' t).sub_const s).sub_const c).neg.exp).const_sub 1
        convert h using 1; simp only [Pi.neg_apply]; ring
      have hev : xsol s =ᶠ[𝓝[≥] t] fun u => 1 - exp (-((u - s) - c)) := by
        filter_upwards [Ico_mem_nhdsGE (show t < s by linarith)] with u hu
        rw [xsol_eq_Yc (ht.trans hu.1) (by linarith [hu.2]), Yc, Bf_neg (by linarith [hu.2])]
      refine (hg.hasDerivWithinAt.congr_of_eventuallyEq_of_mem hev self_mem_Ici).congr_deriv ?_
      rw [sat_of_nonpos hA1.le, Fx_one_low le_rfl (by norm_num), xsol_eq_Yc ht hA.le,
        sat_of_mem hYmem.1 hYmem.2, Yc, Bf_neg hA1.le]
      ring
    · set c := Bf (-s)
      have hg : HasDerivAt (fun u => 1 - exp (-((u - s) - (u - s) ^ 2 - c)))
          (exp (-((t - s) - (t - s) ^ 2 - c)) * (1 - 2 * (t - s))) t := by
        have h1 := (hasDerivAt_id' t).sub_const s
        have h2 := (h1.sub (h1.pow 2)).sub_const c
        convert (h2.neg.exp).const_sub 1 using 1
        simp only [Pi.neg_apply, Pi.sub_apply, Pi.pow_apply]; push_cast; ring
      have hev : xsol s =ᶠ[𝓝[≥] t] fun u => 1 - exp (-((u - s) - (u - s) ^ 2 - c)) := by
        filter_upwards [Ico_mem_nhdsGE (show t < s + 1 / 2 by linarith)] with u hu
        rw [xsol_eq_Yc (ht.trans hu.1) (by linarith [hu.2]), Yc,
          Bf_mid (by linarith [hu.1]) (by linarith [hu.2])]
      refine (hg.hasDerivWithinAt.congr_of_eventuallyEq_of_mem hev self_mem_Ici).congr_deriv ?_
      rw [sat_of_mem hA2 (by linarith), Fx_one_low hA2 hA.le, xsol_eq_Yc ht hA.le,
        sat_of_mem hYmem.1 hYmem.2, Yc, Bf_mid hA2 hA.le]
      ring
  · -- hold phase
    set ys := 1 - exp (-(1 / 4 - Bf (-s)))
    set c := Af (-s)
    rcases lt_or_ge (t - s) 1 with hB1 | hB2
    · have hα : HasDerivAt (fun u => (u - s - 1 / 2) ^ 2 - c)
          (2 * (t - s - 1 / 2)) t := by
        convert ((((hasDerivAt_id' t).sub_const s).sub_const (1 / 2)).pow 2).sub_const c
          using 1; push_cast; ring
      have hg := (psi_hasDerivAt ((t - s - 1 / 2) ^ 2 - c) ys).comp t hα
      have hev : xsol s =ᶠ[𝓝[≥] t] (fun A => psi A ys) ∘ fun u => (u - s - 1 / 2) ^ 2 - c := by
        filter_upwards [Ico_mem_nhdsGE (show t < s + 1 by linarith)] with u hu
        rw [Function.comp_apply, xsol_hold (by linarith [hu.1]),
          Af_mid (by linarith [hu.1]) (by linarith [hu.2])]
      refine (hg.hasDerivWithinAt.congr_of_eventuallyEq_of_mem hev self_mem_Ici).congr_deriv ?_
      rw [sat_of_mem (by linarith) hB1.le, Fx_one_high hB hB1.le,
        xsol_hold hB, Af_mid hB hB1.le]
      ring
    · have hα : HasDerivAt (fun u => (u - s - 3 / 4) - c) 1 t :=
        (((hasDerivAt_id' t).sub_const s).sub_const (3 / 4)).sub_const c
      have hg := (psi_hasDerivAt ((t - s - 3 / 4) - c) ys).comp t hα
      have hev : xsol s =ᶠ[𝓝[≥] t] (fun A => psi A ys) ∘ fun u => (u - s - 3 / 4) - c := by
        filter_upwards [self_mem_nhdsWithin] with u (hu : t ≤ u)
        rw [Function.comp_apply, xsol_hold (by linarith), Af_hi (by linarith)]
      refine (hg.hasDerivWithinAt.congr_of_eventuallyEq_of_mem hev self_mem_Ici).congr_deriv ?_
      rw [sat_of_ge_one hB2, Fx_one_high (by norm_num) le_rfl, xsol_hold hB, Af_hi hB2]
      ring

/-- **Existence, for the concrete loop**: `xsol` is a solution family of `m0` driven
by `S0` from `q(0) = 0`, on `[0, ∞)`, for every timing `s`. -/
theorem xsol_isSol : IsSolFamily m0 S0 0 xsol where
  init s := by
    unfold xsol Yc
    simp only [zero_sub, sub_self, neg_zero, exp_zero]
    rw [psi_zero]; exact sat_of_nonpos le_rfl
  cont s := (xsol_cont s).continuousOn
  deriv s t ht := xsol_deriv s t ht

/-! ## The hypotheses of the three theorems, for the concrete instance -/

/-- From `tw = 3` on, in the sweep `s ∈ [0, 2]`, the node follows the hold flow
from the state the set phase left: `1 - exp (-(1/4 + s))`. -/
lemma xsol_late {s t : ℝ} (hs : 0 ≤ s) (h : 1 ≤ t - s) :
    xsol s t = psi (t - s - 3 / 4) (1 - exp (-(1 / 4 + s))) := by
  rw [xsol_hold (by linarith), Af_hi h, Af_lo (by linarith), Bf_neg (by linarith)]
  congr 1 <;> ring_nf

lemma wh_y (s : ℝ) (hs : 0 ≤ s) : wh (1 - exp (-(1 / 4 + s))) = 1 / 2 - exp (-(1 / 4 + s)) := by
  have h1 : exp (-(1 / 4 + s)) ≤ 1 := exp_le_one_iff.2 (by linarith)
  have h2 := exp_pos (-(1 / 4 + s))
  unfold wh; rw [sat_of_mem (by linarith) (by linarith)]; ring

lemma psi_ge {A y : ℝ} (hA : 0 ≤ A) (hw : 0 ≤ wh y) : 1 / 2 + wh y ≤ psi A y := by
  have := psi_sub A y
  have hD := Dn_pos A y
  have h1 := Dn_le_one hA y
  have : wh y ≤ wh y / Dn A y := by rw [le_div_iff₀ hD]; nlinarith
  linarith

lemma psi_le {A y : ℝ} (hA : 0 ≤ A) (hw : wh y ≤ 0) : psi A y ≤ 1 / 2 + wh y := by
  have := psi_sub A y
  have hD := Dn_pos A y
  have h1 := Dn_le_one hA y
  have : wh y / Dn A y ≤ wh y := by rw [div_le_iff₀ hD]; nlinarith
  linarith

lemma abs_psi_ge {A y : ℝ} (hA : 0 ≤ A) : |wh y| ≤ |psi A y - 1 / 2| := by
  rw [psi_sub, abs_div, abs_of_pos (Dn_pos A y), le_div_iff₀ (Dn_pos A y)]
  have := Dn_le_one hA y
  nlinarith [abs_nonneg (wh y)]

lemma exp_quarter : 3 / 4 ≤ exp (-(1 / 4 : ℝ)) := by
  have := add_one_le_exp (-(1 / 4 : ℝ)); linarith

lemma exp_nine_quarters : exp (-(9 / 4 : ℝ)) ≤ 1 / 4 := by
  have h := add_one_le_exp (9 / 8 : ℝ)
  have h2 : exp (9 / 4 : ℝ) = exp (9 / 8) * exp (9 / 8) := by rw [← exp_add]; norm_num
  have h3 : 4 ≤ exp (9 / 4 : ℝ) := by rw [h2]; nlinarith
  rw [exp_neg]
  rw [inv_le_comm₀ (exp_pos _) (by norm_num)]
  linarith

/-- **H_ENDS for the instance** (VIL = 1/4, VIH = 3/4): with r2 at the same time as
r1 (`s = 0`) the node falls to a valid 0; with r2 two time units late (`s = 2`) it
rises to a valid 1; at every observation time `T ≥ 3`. -/
theorem inst_H_ENDS {T : ℝ} (hT : 3 ≤ T) : xsol 0 T ≤ 1 / 4 ∧ 3 / 4 ≤ xsol 2 T := by
  constructor
  · rw [xsol_late le_rfl (by linarith)]
    have hw := wh_y 0 le_rfl
    rw [add_zero] at hw ⊢
    refine (psi_le (by linarith) (by rw [hw]; linarith [exp_quarter])).trans ?_
    rw [hw]; linarith [exp_quarter]
  · rw [xsol_late (by norm_num) (by linarith)]
    have hw := wh_y 2 (by norm_num)
    have e : (1 / 4 + 2 : ℝ) = 9 / 4 := by norm_num
    rw [e] at hw ⊢
    refine le_trans ?_ (psi_ge (by linarith) (by rw [hw]; linarith [exp_nine_quarters]))
    rw [hw]; linarith [exp_nine_quarters]

/-- **H_HOLD_INPUTS for the instance**: from `tw = 3`, both requests are at 1 for
every timing in the sweep `[0, 2]`. -/
theorem inst_hold : HoldInputs S0 0 2 3 := by
  intro s hs t ht
  rw [S0_u1, S0_u2, sat_of_ge_one (by linarith [hs.2])]
  exact ⟨rfl, rfl⟩

/-- The hold equilibrium of the instance is mid-rail. -/
theorem inst_heq : m0.F 1 1 (1 / 2) = 1 / 2 := by
  show Fx 1 1 (1 / 2) = 1 / 2
  have := Fx_one_high (b := 1) (by norm_num) le_rfl (1 / 2)
  rw [show phi (1 / 2) = 0 by norm_num [phi, wh, sat]] at this
  linarith

/-- The metastable point lies between the states the two ends reach at `tw = 3`. -/
theorem inst_hvs : (1 / 2 : ℝ) ∈ uIcc (xsol 0 3) (xsol 2 3) := by
  obtain ⟨h1, h2⟩ := inst_H_ENDS (T := 3) le_rfl
  rw [mem_uIcc]; left; constructor <;> linarith

lemma Fx_hold_eq (v : ℝ) : m0.F 1 1 v - v = phi v := by
  show Fx 1 1 v - v = phi v
  rw [Fx_one_high (by norm_num) le_rfl]; ring

/-- **H_LOCAL_GAIN_UP for the instance**, for every `g ∈ [1, 2)` on a band
`r` with `2 r < 2 - g` (the loop gain at mid-rail is exactly 2). -/
theorem inst_gain_up {g r : ℝ} (hg : 1 ≤ g) (hgr : 2 * r < 2 - g) :
    ∀ v ∈ Ioc (1 / 2 : ℝ) (1 / 2 + r), (g - 1) * (v - 1 / 2) < m0.F 1 1 v - v := by
  intro v hv
  rw [Fx_hold_eq, phi, wh, sat_of_mem (by linarith [hv.1]) (by linarith [hv.2]),
    abs_of_pos (by linarith [hv.1])]
  have h1 : 0 < v - 1 / 2 := by linarith [hv.1]
  nlinarith [hv.2]

theorem inst_gain_dn {g r : ℝ} (hg : 1 ≤ g) (hgr : 2 * r < 2 - g) :
    ∀ v ∈ Ico (1 / 2 - r : ℝ) (1 / 2), m0.F 1 1 v - v < (g - 1) * (v - 1 / 2) := by
  intro v hv
  rw [Fx_hold_eq, phi, wh, sat_of_mem (by linarith [hv.1]) (by linarith [hv.2]),
    abs_of_neg (by linarith [hv.2])]
  have h1 : v - 1 / 2 < 0 := by linarith [hv.2]
  nlinarith [hv.1]

/-- Upper local gain, `gh = 2` (the exact slope at mid-rail), used by Part 2. -/
theorem inst_gain_hi_up : ∀ v ∈ Ioc (1 / 2 : ℝ) 1, m0.F 1 1 v - v < (2 - 1) * (v - 1 / 2) := by
  intro v hv
  rw [Fx_hold_eq, phi, wh, sat_of_mem (by linarith [hv.1]) hv.2,
    abs_of_pos (by linarith [hv.1])]
  have h1 : 0 < v - 1 / 2 := by linarith [hv.1]
  nlinarith

theorem inst_gain_hi_dn : ∀ v ∈ Ico (0 : ℝ) (1 / 2), (2 - 1) * (v - 1 / 2) < m0.F 1 1 v - v := by
  intro v hv
  rw [Fx_hold_eq, phi, wh, sat_of_mem hv.1 (by linarith [hv.2]),
    abs_of_neg (by linarith [hv.2])]
  have h1 : v - 1 / 2 < 0 := by linarith [hv.2]
  nlinarith

/-- `exp(-K) |a - b| ≤ |exp(-a) - exp(-b)|` for `a, b ≤ K`. -/
lemma exp_spread {a b K : ℝ} (ha : a ≤ K) (hb : b ≤ K) :
    exp (-K) * |a - b| ≤ |exp (-a) - exp (-b)| := by
  wlog hab : a ≤ b generalizing a b
  · have := this hb ha (by linarith)
    rwa [abs_sub_comm, abs_sub_comm (exp (-b))] at this
  rw [abs_of_nonpos (by linarith), abs_of_nonneg (by
    have := exp_le_exp.2 (show -b ≤ -a by linarith); linarith)]
  have e : exp (-a) = exp (-b) * exp (b - a) := by rw [← exp_add]; ring_nf
  have h1 := add_one_le_exp (b - a)
  have h2 : exp (-K) ≤ exp (-b) := exp_le_exp.2 (by linarith)
  rw [e]
  nlinarith [exp_pos (-b), exp_pos (-K)]

/-- The exact metastable timing of the instance: `s* = log 2 - 1/4`. -/
noncomputable def sstar : ℝ := Real.log 2 - 1 / 4

lemma sstar_mem : sstar ∈ Icc (0 : ℝ) 2 := by
  have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  have h2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  unfold sstar
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

/-- At `s*` the node sits on mid-rail forever after `tw = 3` (checked directly from
the closed form, independently of `metastable_forever`). -/
theorem inst_sstar_meta {t : ℝ} (ht : 3 ≤ t) : xsol sstar t = 1 / 2 := by
  have h := sstar_mem
  rw [xsol_late h.1 (by linarith [h.2])]
  have e : exp (-(1 / 4 + sstar)) = 1 / 2 := by
    unfold sstar; rw [show -(1 / 4 + (Real.log 2 - 1 / 4)) = -Real.log 2 by ring, exp_neg,
      exp_log (by norm_num)]; norm_num
  have hw : wh (1 - exp (-(1 / 4 + sstar))) = 0 := by rw [wh_y _ h.1, e]; ring
  rw [psi, hw, zero_div, add_zero]

/-- **H_SPREAD for the instance**, with `c = exp(-9/4)` and `s* = log 2 - 1/4`. -/
theorem inst_spread {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 2) :
    exp (-(9 / 4)) * |s - sstar| ≤ |xsol s 3 - 1 / 2| := by
  rw [xsol_late hs.1 (by linarith [hs.2])]
  refine le_trans ?_ (abs_psi_ge (by linarith [hs.2]))
  rw [wh_y s hs.1]
  have e : (1 / 2 : ℝ) = exp (-(1 / 4 + sstar)) := by
    unfold sstar; rw [show -(1 / 4 + (Real.log 2 - 1 / 4)) = -Real.log 2 by ring, exp_neg,
      exp_log (by norm_num)]; norm_num
  rw [e]
  have := exp_spread (a := 1 / 4 + sstar) (b := 1 / 4 + s) (K := 9 / 4)
    (by linarith [sstar_mem.2]) (by linarith [hs.2])
  rw [show 1 / 4 + sstar - (1 / 4 + s) = -(s - sstar) by ring, abs_neg] at this
  exact this

/-! ## Non-vacuity: the three theorems, instantiated -/

/-- `analog_arbiter_not_exclusive`, instantiated: for every `T ≥ 3` some timing in
`[0, 2]` leaves `q(T)` strictly inside `(1/4, 3/4)`. -/
theorem inst_not_exclusive {T : ℝ} (hT : 3 ≤ T) :
    ∃ s ∈ Icc (0 : ℝ) 2, 1 / 4 < xsol s T ∧ xsol s T < 3 / 4 :=
  analog_arbiter_not_exclusive m0 S0 xsol_isSol (by linarith) (by norm_num) (by norm_num)
    (Or.inl (inst_H_ENDS hT))

/-- `metastable_forever`, instantiated. -/
theorem inst_metastable :
    ∃ s ∈ Icc (0 : ℝ) 2, ∀ t, 3 ≤ t → xsol s t = 1 / 2 :=
  metastable_forever xsol_isSol (by norm_num) (by norm_num) inst_hold inst_heq inst_hvs

/-- `aperture_upper_bound`, instantiated: for `g ∈ [1, 2)` and `2 r < 2 - g`, any timing
undecided (within `r` of mid-rail) on all of `[3, T]` is within
`(r / exp(-9/4)) exp(-(g - 1)(T - 3))` of `s*`. -/
theorem inst_aperture_upper {g r : ℝ} (hg : 1 ≤ g) (hgr : 2 * r < 2 - g)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 2) {T : ℝ} (hT : 3 ≤ T)
    (hund : ∀ t ∈ Icc 3 T, |xsol s t - 1 / 2| ≤ r) :
    |s - sstar| ≤ r / exp (-(9 / 4)) * exp (-((g - 1) / m0.tau * (T - 3))) :=
  aperture_upper_bound xsol_isSol (by norm_num) inst_hold hs (inst_gain_up hg hgr)
    (inst_gain_dn hg hgr) (exp_pos _) (inst_spread hs) hT hund

/-! ## Part 2: the matching lower bound, from a two-sided local gain bound -/

section Local
variable {m : Loop} {S : Stim} {v0 : ℝ} {x : ℝ → ℝ → ℝ}

/-- **Two-sided escape bound above `vs`.** In the hold region, with local loop gain
between `g` and `gh` on `(vs, vs + r]` (**H_LOCAL_GAIN_UP**, and
**H_LOCAL_GAIN_HI_UP**: `G v - v < (gh - 1)(v - vs)`; physical fact: the loop's
small-signal gain near the metastable point is at most `gh`; test: same SPICE/GLS
closed-loop sweep around `vs` as H_LOCAL_GAIN_UP), a node that starts above `vs`
close enough that the FAST rate cannot carry it out of the band by `T` satisfies
`d e^{(g-1)(t-tw)/tau} ≤ q(t) - vs ≤ d e^{(gh-1)(t-tw)/tau}` on `[tw, T]`. -/
theorem sandwich_up (hx : IsSolFamily m S v0 x) {sA sB tw vs r g gh : ℝ}
    (htw : 0 ≤ tw) (hH : HoldInputs S sA sB tw) {s : ℝ} (hs : s ∈ Icc sA sB)
    (H_LOCAL_GAIN_UP : ∀ v ∈ Ioc vs (vs + r), (g - 1) * (v - vs) < m.F 1 1 v - v)
    (H_LOCAL_GAIN_HI_UP : ∀ v ∈ Ioc vs (vs + r), m.F 1 1 v - v < (gh - 1) * (v - vs))
    (hg : 1 ≤ g) (habove : vs < x s tw) {T : ℝ} (_hT : tw ≤ T)
    (hstart : (x s tw - vs) * exp ((gh - 1) / m.tau * (T - tw)) ≤ r) :
    ∀ t ∈ Icc tw T, vs + (x s tw - vs) * exp ((g - 1) / m.tau * (t - tw)) ≤ x s t ∧
      x s t ≤ vs + (x s tw - vs) * exp ((gh - 1) / m.tau * (t - tw)) := by
  set d := x s tw - vs with hd
  set lh := (gh - 1) / m.tau with hlh_def
  have hd0 : 0 < d := by linarith
  have hr : 0 < r := lt_of_lt_of_le (mul_pos hd0 (exp_pos _)) hstart
  have hgh : 1 ≤ gh := by
    have h1 := H_LOCAL_GAIN_UP (vs + r) ⟨by linarith, le_rfl⟩
    have h2 := H_LOCAL_GAIN_HI_UP (vs + r) ⟨by linarith, le_rfl⟩
    rw [add_sub_cancel_left] at h1 h2
    nlinarith
  have hlh : 0 ≤ lh := div_nonneg (by linarith) m.H_TAU.le
  have hcont : ContinuousOn (x s) (Icc tw T) := (hx.cont s).mono fun y hy => htw.trans hy.1
  have hder : ∀ t ∈ Ico tw T, HasDerivWithinAt (x s) (m.field 1 1 (x s t)) (Ici t) t :=
    fun t ht => hold_deriv hx htw hH hs ht.1
  have hBle : ∀ t ∈ Icc tw T, d * exp (lh * (t - tw)) ≤ r := fun t ht =>
    le_trans (mul_le_mul_of_nonneg_left
      (exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hlh)) hd0.le) hstart
  have hB : ∀ t, HasDerivAt (fun u => vs + d * exp (lh * (u - tw)))
      (d * (exp (lh * (t - tw)) * lh)) t := by
    intro t
    have h1 : HasDerivAt (fun u => lh * (u - tw)) lh t := by
      simpa using ((hasDerivAt_id t).sub_const tw).const_mul lh
    exact (h1.exp.const_mul d).const_add vs
  have upper := image_le_of_deriv_right_lt_deriv_boundary hcont hder
    (B := fun u => vs + d * exp (lh * (u - tw)))
    (by simp only [sub_self, mul_zero, exp_zero, mul_one]; linarith) hB
    (fun t ht heq => by
      have hpos : 0 < d * exp (lh * (t - tw)) := mul_pos hd0 (exp_pos _)
      have hin : x s t ∈ Ioc vs (vs + r) :=
        ⟨by rw [heq]; linarith, by rw [heq]; linarith [hBle t (Ico_subset_Icc_self ht)]⟩
      have h := H_LOCAL_GAIN_HI_UP _ hin
      simp only [Loop.field]
      rw [div_lt_iff₀ m.H_TAU]
      have htau := m.H_TAU.ne'
      have e : (gh - 1) * (x s t - vs) = d * (exp (lh * (t - tw)) * lh) * m.tau := by
        rw [heq, hlh_def]; field_simp; ring
      linarith)
  have lower := grow_lower (y := x s) (y' := fun t => m.field 1 1 (x s t))
    (a := tw) (b := T) (c := vs) (d := d) (r := r) (lam := (g - 1) / m.tau)
    hcont hder hd0 (by linarith)
    (fun t _ h1 h2 => by
      have := H_LOCAL_GAIN_UP (x s t) ⟨h1, h2⟩
      simp only [Loop.field, div_mul_eq_mul_div]
      exact (div_lt_div_iff_of_pos_right m.H_TAU).mpr this)
    (fun t ht => by have := upper ht; have := hBle t ht; linarith)
  exact fun t ht => ⟨lower t ht, upper ht⟩

/-- Mirror image of `sandwich_up`, below `vs`. **H_LOCAL_GAIN_HI_DN**:
`(gh - 1)(v - vs) < G v - v` on `[vs - r, vs)`. -/
theorem sandwich_dn (hx : IsSolFamily m S v0 x) {sA sB tw vs r g gh : ℝ}
    (htw : 0 ≤ tw) (hH : HoldInputs S sA sB tw) {s : ℝ} (hs : s ∈ Icc sA sB)
    (H_LOCAL_GAIN_DN : ∀ v ∈ Ico (vs - r) vs, m.F 1 1 v - v < (g - 1) * (v - vs))
    (H_LOCAL_GAIN_HI_DN : ∀ v ∈ Ico (vs - r) vs, (gh - 1) * (v - vs) < m.F 1 1 v - v)
    (hg : 1 ≤ g) (hbelow : x s tw < vs) {T : ℝ} (_hT : tw ≤ T)
    (hstart : (vs - x s tw) * exp ((gh - 1) / m.tau * (T - tw)) ≤ r) :
    ∀ t ∈ Icc tw T, vs - (vs - x s tw) * exp ((gh - 1) / m.tau * (t - tw)) ≤ x s t ∧
      x s t ≤ vs - (vs - x s tw) * exp ((g - 1) / m.tau * (t - tw)) := by
  set d := vs - x s tw with hd
  set lh := (gh - 1) / m.tau with hlh_def
  have hd0 : 0 < d := by linarith
  have hr : 0 < r := lt_of_lt_of_le (mul_pos hd0 (exp_pos _)) hstart
  have hgh : 1 ≤ gh := by
    have h1 := H_LOCAL_GAIN_DN (vs - r) ⟨le_rfl, by linarith⟩
    have h2 := H_LOCAL_GAIN_HI_DN (vs - r) ⟨le_rfl, by linarith⟩
    rw [sub_sub_cancel_left] at h1 h2
    nlinarith
  have hlh : 0 ≤ lh := div_nonneg (by linarith) m.H_TAU.le
  have hcont : ContinuousOn (fun t => -x s t) (Icc tw T) :=
    ((hx.cont s).mono fun y hy => (htw.trans hy.1 : (0 : ℝ) ≤ y)).neg
  have hder : ∀ t ∈ Ico tw T,
      HasDerivWithinAt (fun t => -x s t) (-m.field 1 1 (x s t)) (Ici t) t :=
    fun t ht => (hold_deriv hx htw hH hs ht.1).neg
  have hBle : ∀ t ∈ Icc tw T, d * exp (lh * (t - tw)) ≤ r := fun t ht =>
    le_trans (mul_le_mul_of_nonneg_left
      (exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hlh)) hd0.le) hstart
  have hB : ∀ t, HasDerivAt (fun u => -vs + d * exp (lh * (u - tw)))
      (d * (exp (lh * (t - tw)) * lh)) t := by
    intro t
    have h1 : HasDerivAt (fun u => lh * (u - tw)) lh t := by
      simpa using ((hasDerivAt_id t).sub_const tw).const_mul lh
    exact (h1.exp.const_mul d).const_add (-vs)
  have upper := image_le_of_deriv_right_lt_deriv_boundary hcont hder
    (B := fun u => -vs + d * exp (lh * (u - tw)))
    (by simp only [sub_self, mul_zero, exp_zero, mul_one]; linarith) hB
    (fun t ht heq => by
      have hpos : 0 < d * exp (lh * (t - tw)) := mul_pos hd0 (exp_pos _)
      have heq' : x s t = vs - d * exp (lh * (t - tw)) := by linarith
      have hin : x s t ∈ Ico (vs - r) vs :=
        ⟨by rw [heq']; linarith [hBle t (Ico_subset_Icc_self ht)], by rw [heq']; linarith⟩
      have h := H_LOCAL_GAIN_HI_DN _ hin
      simp only [Loop.field]
      rw [neg_lt, lt_div_iff₀ m.H_TAU]
      have htau := m.H_TAU.ne'
      have e : (gh - 1) * (x s t - vs) = -(d * (exp (lh * (t - tw)) * lh)) * m.tau := by
        rw [heq', hlh_def]; field_simp; ring
      linarith)
  have lower := grow_lower (y := fun t => -x s t) (y' := fun t => -m.field 1 1 (x s t))
    (a := tw) (b := T) (c := -vs) (d := d) (r := r) (lam := (g - 1) / m.tau)
    hcont hder hd0 (by linarith)
    (fun t _ h1 h2 => by
      have := H_LOCAL_GAIN_DN (x s t) ⟨by linarith, by linarith⟩
      have h3 : (m.F 1 1 (x s t) - x s t) / m.tau < (g - 1) * (x s t - vs) / m.tau :=
        (div_lt_div_iff_of_pos_right m.H_TAU).mpr this
      simp only [Loop.field]
      rw [div_mul_eq_mul_div]
      have e : (g - 1) * (-x s t - -vs) / m.tau = -((g - 1) * (x s t - vs) / m.tau) := by ring
      rw [e]; linarith)
    (fun t ht => by have := upper ht; have := hBle t ht; linarith)
  refine fun t ht => ⟨?_, ?_⟩
  · have := upper ht; linarith
  · have := lower t ht; linarith

/-- Started exactly on the equilibrium, the node stays there (ODE uniqueness). -/
theorem stays_at (hx : IsSolFamily m S v0 x) {sA sB tw vs : ℝ} (htw : 0 ≤ tw)
    (hH : HoldInputs S sA sB tw) {s : ℝ} (hs : s ∈ Icc sA sB)
    (heq : m.F 1 1 vs = vs) (h0 : x s tw = vs) : ∀ t, tw ≤ t → x s t = vs := by
  intro t ht
  have hf0 : m.field 1 1 vs = 0 := by simp [Loop.field, heq]
  exact ODE_solution_unique (v := fun _ => m.field 1 1) (K := m.K)
    (f := x s) (g := fun _ => vs) (a := tw) (b := t)
    (fun _ => m.field_lipschitz 1 1)
    ((hx.cont s).mono fun y hy => (htw.trans hy.1 : (0 : ℝ) ≤ y))
    (fun y hy => hold_deriv hx htw hH hs hy.1)
    continuousOn_const
    (fun y _ => by rw [hf0]; exact hasDerivWithinAt_const _ _ _)
    h0 ⟨ht, le_rfl⟩

/-- **Close to `vs` at `tw` ⇒ undecided on all of `[tw, T]`**, under the two-sided
local gain bound `g ≤ gain ≤ gh` on `[vs - r, vs + r]`. -/
theorem undecided_of_close (hx : IsSolFamily m S v0 x) {sA sB tw vs r g gh : ℝ}
    (htw : 0 ≤ tw) (hH : HoldInputs S sA sB tw) {s : ℝ} (hs : s ∈ Icc sA sB)
    (heq : m.F 1 1 vs = vs)
    (H_LOCAL_GAIN_UP : ∀ v ∈ Ioc vs (vs + r), (g - 1) * (v - vs) < m.F 1 1 v - v)
    (H_LOCAL_GAIN_DN : ∀ v ∈ Ico (vs - r) vs, m.F 1 1 v - v < (g - 1) * (v - vs))
    (H_LOCAL_GAIN_HI_UP : ∀ v ∈ Ioc vs (vs + r), m.F 1 1 v - v < (gh - 1) * (v - vs))
    (H_LOCAL_GAIN_HI_DN : ∀ v ∈ Ico (vs - r) vs, (gh - 1) * (v - vs) < m.F 1 1 v - v)
    (hg : 1 ≤ g) {T : ℝ} (hT : tw ≤ T)
    (hstart : |x s tw - vs| * exp ((gh - 1) / m.tau * (T - tw)) ≤ r) :
    ∀ t ∈ Icc tw T, |x s t - vs| ≤ r := by
  intro t ht
  rcases lt_trichotomy (x s tw) vs with h | h | h
  · rw [abs_of_neg (by linarith), neg_sub] at hstart
    obtain ⟨h1, h2⟩ := sandwich_dn hx htw hH hs H_LOCAL_GAIN_DN H_LOCAL_GAIN_HI_DN hg h hT
      (by linarith) t ht
    have hlh : 0 ≤ (gh - 1) / m.tau := by
      have hr : 0 < r := lt_of_lt_of_le (mul_pos (by linarith) (exp_pos _)) hstart
      have a1 := H_LOCAL_GAIN_DN (vs - r) ⟨le_rfl, by linarith⟩
      have a2 := H_LOCAL_GAIN_HI_DN (vs - r) ⟨le_rfl, by linarith⟩
      rw [sub_sub_cancel_left] at a1 a2
      exact div_nonneg (by nlinarith) m.H_TAU.le
    have hE : exp ((gh - 1) / m.tau * (t - tw)) ≤ exp ((gh - 1) / m.tau * (T - tw)) :=
      exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hlh)
    have hg0 : 0 ≤ exp ((g - 1) / m.tau * (t - tw)) := (exp_pos _).le
    rw [abs_le]; constructor
    · nlinarith
    · nlinarith
  · rw [stays_at hx htw hH hs heq h t ht.1, sub_self, abs_zero]
    exact le_trans (mul_nonneg (abs_nonneg _) (exp_pos _).le) hstart
  · rw [abs_of_pos (by linarith)] at hstart
    obtain ⟨h1, h2⟩ := sandwich_up hx htw hH hs H_LOCAL_GAIN_UP H_LOCAL_GAIN_HI_UP hg h hT
      hstart t ht
    have hlh : 0 ≤ (gh - 1) / m.tau := by
      have hr : 0 < r := lt_of_lt_of_le (mul_pos (by linarith) (exp_pos _)) hstart
      have a1 := H_LOCAL_GAIN_UP (vs + r) ⟨by linarith, le_rfl⟩
      have a2 := H_LOCAL_GAIN_HI_UP (vs + r) ⟨by linarith, le_rfl⟩
      rw [add_sub_cancel_left] at a1 a2
      exact div_nonneg (by nlinarith) m.H_TAU.le
    have hE : exp ((gh - 1) / m.tau * (t - tw)) ≤ exp ((gh - 1) / m.tau * (T - tw)) :=
      exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hlh)
    have hg0 : 0 ≤ exp ((g - 1) / m.tau * (t - tw)) := (exp_pos _).le
    rw [abs_le]; constructor
    · nlinarith
    · nlinarith

/-- **Aperture lower bound at the local rate (matching `aperture_upper_bound`).**
With `C(tw) = 2 L M / tau · gronwallBound 0 K 1 tw` (the Groenwall spread of
`sol_dist_le`), every timing with `C |s - s*| e^{(gh-1)(T-tw)/tau} ≤ r` stays
undecided on all of `[tw, T]`. So the bad-timing window contains
`s* ± (r/C) e^{-(gh-1)(T-tw)/tau}`, while `aperture_upper_bound` puts it inside
`s* ± (r/c) e^{-(g-1)(T-tw)/tau}`: both rates are LOCAL, `(g-1)/tau ≤ rate ≤ (gh-1)/tau`,
and they coincide as the band `r` shrinks around a point where `G` is differentiable. -/
theorem aperture_lower_bound_local (hx : IsSolFamily m S v0 x) {sA sB tw vs r g gh sstar : ℝ}
    (htw : 0 ≤ tw) (hH : HoldInputs S sA sB tw) {s : ℝ} (hs : s ∈ Icc sA sB)
    (heq : m.F 1 1 vs = vs) (hstar : x sstar tw = vs)
    (H_LOCAL_GAIN_UP : ∀ v ∈ Ioc vs (vs + r), (g - 1) * (v - vs) < m.F 1 1 v - v)
    (H_LOCAL_GAIN_DN : ∀ v ∈ Ico (vs - r) vs, m.F 1 1 v - v < (g - 1) * (v - vs))
    (H_LOCAL_GAIN_HI_UP : ∀ v ∈ Ioc vs (vs + r), m.F 1 1 v - v < (gh - 1) * (v - vs))
    (H_LOCAL_GAIN_HI_DN : ∀ v ∈ Ico (vs - r) vs, (gh - 1) * (v - vs) < m.F 1 1 v - v)
    (hg : 1 ≤ g) {T : ℝ} (hT : tw ≤ T)
    (hwin : 2 * m.L * S.M / m.tau * gronwallBound 0 m.K 1 tw * |s - sstar|
      * exp ((gh - 1) / m.tau * (T - tw)) ≤ r) :
    ∀ t ∈ Icc tw T, |x s t - vs| ≤ r := by
  refine undecided_of_close hx htw hH hs heq H_LOCAL_GAIN_UP H_LOCAL_GAIN_DN
    H_LOCAL_GAIN_HI_UP H_LOCAL_GAIN_HI_DN hg hT (le_trans ?_ hwin)
  gcongr
  rw [← hstar]
  exact sol_dist_le hx s sstar tw htw

end Local

/-! ## Part 2 for the instance: the window is pinned between two local rates -/

/-- The Groenwall spread constant of the instance. -/
noncomputable def Cinst : ℝ := 2 * m0.L * S0.M / m0.tau * gronwallBound 0 m0.K 1 3

/-- **Lower half for the instance**, at the exact linearized rate `(2 - 1)/tau = 1`:
for `0 < r < 1/2`, every timing in the sweep with `Cinst |s - s*| e^{T-3} ≤ r` is still
undecided on all of `[3, T]`. -/
theorem inst_window_lower {r : ℝ} (hr1 : r < 1 / 2) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 2)
    {T : ℝ} (hT : 3 ≤ T) (hwin : Cinst * |s - sstar| * exp ((2 - 1) / m0.tau * (T - 3)) ≤ r) :
    ∀ t ∈ Icc 3 T, |xsol s t - 1 / 2| ≤ r := by
  have hstar : xsol sstar 3 = 1 / 2 := inst_sstar_meta le_rfl
  refine aperture_lower_bound_local xsol_isSol (by norm_num) inst_hold hs inst_heq hstar
    (inst_gain_up (g := 1) le_rfl (by linarith)) (inst_gain_dn (g := 1) le_rfl (by linarith))
    (fun v hv => inst_gain_hi_up v ⟨hv.1, by linarith [hv.2]⟩)
    (fun v hv => inst_gain_hi_dn v ⟨by linarith [hv.1], hv.2⟩) le_rfl hT hwin

/-- **Non-vacuity of `hund`**: for every `T ≥ 3` and `0 < r < 1/2` there IS a timing
`s ≠ s*` in the sweep that is undecided on all of `[3, T]`, so `inst_aperture_upper`
constrains a nonempty set of timings. -/
theorem inst_undecided_exists {r : ℝ} (hr : 0 < r) (hr1 : r < 1 / 2) {T : ℝ} (hT : 3 ≤ T) :
    ∃ s ∈ Icc (0 : ℝ) 2, s ≠ sstar ∧ ∀ t ∈ Icc 3 T, |xsol s t - 1 / 2| ≤ r := by
  set E := exp ((2 - 1) / m0.tau * (T - 3))
  have hE := exp_pos ((2 - 1) / m0.tau * (T - 3))
  set δ := min 1 (r / (|Cinst| * E + 1)) with hδ
  have hden : 0 < |Cinst| * E + 1 := by positivity
  have hδ0 : 0 < δ := lt_min one_pos (div_pos hr hden)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ r / (|Cinst| * E + 1) := min_le_right _ _
  have hs := sstar_mem
  have hs1 : sstar ≤ 1 := by
    have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    unfold sstar; norm_num at h1 ⊢; linarith
  refine ⟨sstar + δ, ⟨by linarith [hs.1], by linarith⟩, by linarith, ?_⟩
  refine inst_window_lower hr1 ⟨by linarith [hs.1], by linarith⟩ hT ?_
  rw [show sstar + δ - sstar = δ by ring, abs_of_pos hδ0]
  have h1 : Cinst * δ * E ≤ |Cinst| * δ * E := by
    gcongr; exact le_abs_self _
  have h2 : |Cinst| * δ * E ≤ r := by
    rw [le_div_iff₀ hden] at hδ2
    nlinarith [abs_nonneg Cinst]
  have h3 : Cinst * δ * E ≤ r := by linarith
  exact h3

end Formal.Cells.ArbAnalog2
