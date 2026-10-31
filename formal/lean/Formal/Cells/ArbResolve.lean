import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Track 7d: linearized resolution of the arbiter loop

`bd_arbcell`'s state node `q = C(r1, ~r2)` is one LUT6 whose output is routed
back to its own input pin.  Treated as an analog storage loop (PROGRAM.md
layer 4), the node voltage obeys a first-order ODE `tau * v' = f(v) - v`, where
`f` is the LUT's static transfer from its fed-back input pin to its output with
`r1`, `r2` held in the runt (set/reset) condition.  If `f` has a fixed point
`vs` with slope `g = f'(vs) > 1` that point is a saddle (here: a repeller of the
1-D loop) and linearizing gives

    tau * v' = (g - 1) * (v - vs),   tau_r := tau / (g - 1),
    v(t) - vs = (v0 - vs) * exp (t / tau_r).

This file proves, with every modelling step a named hypothesis:

1. `LinLoop.sol_hasDerivAt`, `LinLoop.sol_ode`: the explicit solution satisfies
   the ODE; `LinLoop.sol_unique`: it is the only solution on `[0, T]`
   (direct exp-integrating-factor argument, no Gronwall needed).
2. `LinLoop.inBand_iff`: `|v(t) - vs| < delta  ↔  t < tau_r * log (delta/|v0-vs|)`,
   i.e. the exit time from the band is exactly `tau_r * ln(delta/|v0 - vs|)`;
   `LinLoop.dev_at_escTime`.
3. `LinLoop.prob_unresolved`: if the law `μ` of `v0` has density `≤ p` on the
   band, the probability of being still within `delta` of `vs` at time `T` is
   `≤ 2 * p * delta * exp (-T / tau_r)`; `LinLoop.prob_unresolved_dt`: the same
   stated for the request-edge timing offset `Δt` with `v0 - vs = k * Δt`,
   which identifies the MTBF aperture `T0 = 2 * delta / |k|`.
4. `nonlinear_growth`, `nonlinear_prob_unresolved`, `gain_prob_unresolved`:
   the same exponential bound for the true nonlinear `f`, from a lower bound
   `g_min` on the loop gain in the band (comparison argument).
5. `LinLoop.no_deadline`: for every `T` there is an initial offset `v0 ≠ vs`
   still unresolved at `T` (so exclusion at a fixed read time is not provable
   deterministically: only the probabilistic bound holds).
6. `mtbf_lower`: the algebra from a per-event bound to
   `MTBF ≥ exp (T / tau_r) / (T0 * f1 * f2)`.
-/

noncomputable section

open Real Set MeasureTheory
open scoped ENNReal

namespace Formal.Cells.ArbResolve

/-- The linearized arbiter loop around its saddle.

Every field after the data is a named physical hypothesis. -/
structure LinLoop where
  /-- Node time constant of the fed-back LUT output (the `tau` in
  `tau * v' = f(v) - v`).  Physically: the RC of the LUT output stage driving
  the routed feedback wire plus the input buffer of the pin it lands on. -/
  tau : ℝ
  /-- Small-signal gain `f'(vs)` of the loop at its metastable point. -/
  g : ℝ
  /-- The metastable (saddle) voltage `vs`, a fixed point `f vs = vs`. -/
  vs : ℝ
  /-- H_TAU_POS: the node has a positive time constant (a real RC, not a
  zero-delay wire).  Testable: ring-oscillator period of the feedback loop on
  GLS / board is nonzero. -/
  H_tau_pos : 0 < tau
  /-- H_GAIN_GT_ONE: the loop gain at the crossing exceeds one, so `vs` is
  repelling.  This is what makes the LUT feedback loop a latch at all (a gain
  below one would have a single stable intermediate point and no memory).
  Testable: the cell holds state on the board (`serv` set in `arb_prot`), and
  on a transistor-level model of the mux tree + buffers (not available in this
  repo) as the slope of the DC transfer at its crossing. -/
  H_gain_gt_one : 1 < g

namespace LinLoop

variable (L : LinLoop)

/-- Resolution time constant `tau_r = tau / (g - 1)`. -/
def taur : ℝ := L.tau / (L.g - 1)

/-- Escape rate `1 / tau_r = (g - 1) / tau`. -/
def rate : ℝ := (L.g - 1) / L.tau

theorem gm1_pos : 0 < L.g - 1 := by linarith [L.H_gain_gt_one]

theorem taur_pos : 0 < L.taur := div_pos L.H_tau_pos L.gm1_pos

theorem rate_pos : 0 < L.rate := div_pos L.gm1_pos L.H_tau_pos

theorem rate_eq_inv_taur : L.rate = 1 / L.taur := by
  unfold rate taur
  rw [one_div_div]

/-- The explicit solution `v(t) = vs + (v0 - vs) * exp (t / tau_r)`. -/
def sol (v0 t : ℝ) : ℝ := L.vs + (v0 - L.vs) * exp (t / L.taur)

theorem sol_zero (v0 : ℝ) : L.sol v0 0 = v0 := by
  simp [sol]

/-- (1a) The explicit solution satisfies `v' = (g-1)/tau * (v - vs)`. -/
theorem sol_hasDerivAt (v0 t : ℝ) :
    HasDerivAt (L.sol v0) (L.rate * (L.sol v0 t - L.vs)) t := by
  have h1 : HasDerivAt (fun t : ℝ => t / L.taur) (1 / L.taur) t :=
    (hasDerivAt_id' (x := t)).div_const L.taur
  have h2 : HasDerivAt (fun x => L.vs + (v0 - L.vs) * exp (x / L.taur))
      ((v0 - L.vs) * (exp (t / L.taur) * (1 / L.taur))) t :=
    (h1.exp.const_mul (v0 - L.vs)).const_add L.vs
  refine h2.congr_deriv ?_
  simp only [sol, rate_eq_inv_taur]
  ring

/-- (1a') The same in the physical form `tau * v' = (g - 1) * (v - vs)`. -/
theorem sol_ode (v0 t : ℝ) :
    L.tau * deriv (L.sol v0) t = (L.g - 1) * (L.sol v0 t - L.vs) := by
  rw [(L.sol_hasDerivAt v0 t).deriv]
  have h := L.H_tau_pos.ne'
  unfold rate
  field_simp

/-- (1b) Uniqueness: any `v` satisfying the linearized ODE on `[0, T]` is the
explicit solution with `v0 = v 0`. -/
theorem sol_unique {v : ℝ → ℝ} {T : ℝ}
    (hode : ∀ t ∈ Icc 0 T, HasDerivAt v (L.rate * (v t - L.vs)) t) :
    ∀ t ∈ Icc 0 T, v t = L.sol (v 0) t := by
  have hwd : ∀ t ∈ Icc 0 T,
      HasDerivAt (fun t => (v t - L.vs) * exp (-(t / L.taur))) 0 t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => -(t / L.taur)) (-(1 / L.taur)) t :=
      ((hasDerivAt_id' (x := t)).div_const L.taur).neg
    have h2 := ((hode t ht).sub_const L.vs).mul h1.exp
    refine h2.congr_deriv ?_
    rw [rate_eq_inv_taur]
    ring
  have hcont : ContinuousOn (fun t => (v t - L.vs) * exp (-(t / L.taur))) (Icc 0 T) :=
    fun t ht => (hwd t ht).continuousAt.continuousWithinAt
  have hconst := constant_of_has_deriv_right_zero hcont
    (fun t ht => (hwd t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
  intro t ht
  have h := hconst t ht
  simp only [zero_div, neg_zero, exp_zero, mul_one] at h
  have he : exp (-(t / L.taur)) * exp (t / L.taur) = 1 := by
    rw [← exp_add]; simp
  have hx : v t - L.vs = (v 0 - L.vs) * exp (t / L.taur) := by
    rw [← h, mul_assoc, he, mul_one]
  unfold sol
  linarith

/-- (1b') Uniqueness for all `t ≥ 0`. -/
theorem sol_unique_Ici {v : ℝ → ℝ}
    (hode : ∀ t, 0 ≤ t → HasDerivAt v (L.rate * (v t - L.vs)) t) :
    ∀ t, 0 ≤ t → v t = L.sol (v 0) t := by
  intro t ht
  exact L.sol_unique (T := t) (fun s hs => hode s hs.1) t ⟨ht, le_rfl⟩

/-- Deviation from the saddle grows exactly exponentially. -/
theorem sol_dev (v0 t : ℝ) :
    |L.sol v0 t - L.vs| = |v0 - L.vs| * exp (t / L.taur) := by
  unfold sol
  rw [add_sub_cancel_left, abs_mul, abs_of_pos (exp_pos _)]

/-- The metastable point itself is an equilibrium: started exactly at `vs`,
the loop never resolves. -/
theorem sol_vs (t : ℝ) : L.sol L.vs t = L.vs := by
  simp [sol]

/-- Exit time from the band `|v - vs| < delta`. -/
def escTime (v0 δ : ℝ) : ℝ := L.taur * log (δ / |v0 - L.vs|)

/-- (2) The node is in the band at time `t` iff `t < tau_r * ln(delta/|v0-vs|)`.
So the first time it leaves the band is exactly `escTime`. -/
theorem inBand_iff {v0 δ : ℝ} (hv : v0 ≠ L.vs) (hδ : 0 < δ) (t : ℝ) :
    |L.sol v0 t - L.vs| < δ ↔ t < L.escTime v0 δ := by
  have ha : 0 < |v0 - L.vs| := abs_pos.mpr (sub_ne_zero.mpr hv)
  rw [L.sol_dev, escTime, mul_comm (|v0 - L.vs|), ← lt_div_iff₀ ha,
    ← lt_log_iff_exp_lt (div_pos hδ ha), div_lt_iff₀ L.taur_pos, mul_comm]

/-- (2') At `escTime` the deviation is exactly `delta`. -/
theorem dev_at_escTime {v0 δ : ℝ} (hv : v0 ≠ L.vs) (hδ : 0 < δ) :
    |L.sol v0 (L.escTime v0 δ) - L.vs| = δ := by
  have ha : 0 < |v0 - L.vs| := abs_pos.mpr (sub_ne_zero.mpr hv)
  have h1 : L.escTime v0 δ / L.taur = log (δ / |v0 - L.vs|) := by
    unfold escTime
    exact mul_div_cancel_left₀ _ L.taur_pos.ne'
  rw [L.sol_dev, h1, exp_log (div_pos hδ ha)]
  exact mul_div_cancel₀ δ ha.ne'

/-- (2'') Started inside the band, the exit time is positive. -/
theorem escTime_pos {v0 δ : ℝ} (hv : v0 ≠ L.vs) (hin : |v0 - L.vs| < δ) :
    0 < L.escTime v0 δ := by
  have ha : 0 < |v0 - L.vs| := abs_pos.mpr (sub_ne_zero.mpr hv)
  unfold escTime
  apply mul_pos L.taur_pos
  apply log_pos
  rw [lt_div_iff₀ ha, one_mul]
  exact hin

/-- (5) No deterministic deadline: for every read time `T` and band `delta`
some offset `v0 ≠ vs` is still unresolved at `T`. -/
theorem no_deadline {δ : ℝ} (hδ : 0 < δ) (T : ℝ) :
    ∃ v0, v0 ≠ L.vs ∧ |L.sol v0 T - L.vs| < δ := by
  have hE := exp_pos (T / L.taur)
  have hpos : 0 < δ / (2 * exp (T / L.taur)) := by positivity
  refine ⟨L.vs + δ / (2 * exp (T / L.taur)), ?_, ?_⟩
  · intro h; linarith
  · rw [L.sol_dev, add_sub_cancel_left, abs_of_pos hpos]
    have : δ / (2 * exp (T / L.taur)) * exp (T / L.taur) = δ / 2 := by
      field_simp
    rw [this]; linarith

end LinLoop

/-! ## Interval and measure lemmas -/

/-- The set of offsets that, amplified by `c > 0`, stay below `delta`. -/
theorem band_set_eq (a c δ : ℝ) (hc : 0 < c) :
    {x : ℝ | |x - a| * c < δ} = Ioo (a - δ / c) (a + δ / c) := by
  ext x
  simp only [mem_ofPred_eq, mem_Ioo]
  rw [← lt_div_iff₀ hc, abs_lt]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- (3, interval-length form) its Lebesgue measure is `2 * delta / c`. -/
theorem band_set_volume (a c δ : ℝ) (hc : 0 < c) :
    volume {x : ℝ | |x - a| * c < δ} = ENNReal.ofReal (2 * δ / c) := by
  rw [band_set_eq a c δ hc, Real.volume_Ioo]
  congr 1
  ring

/-- H_DENSITY_BOUND (as a predicate): the law `μ` of the initial offset has
density at most `p` w.r.t. Lebesgue measure on the neighbourhood `N`.
Physically: the relative timing of the two request edges is spread smoothly
(no atom, no lock) over the decision window.  In `arb_prot` this is what the
CLEN1 = 3 / CLEN2 = 5 drift is designed to provide; it is testable on the
routed GLS by histogramming `Δt` over many arbitrations. -/
def DensityBound (μ : Measure ℝ) (N : Set ℝ) (p : ℝ) : Prop :=
  ∀ s, MeasurableSet s → s ⊆ N → μ s ≤ ENNReal.ofReal p * volume s

/-- Generic probabilistic band bound. -/
theorem prob_band (μ : Measure ℝ) {N : Set ℝ} {a c δ p : ℝ} (hc : 0 < c)
    (hp : 0 ≤ p) (hN : Ioo (a - δ / c) (a + δ / c) ⊆ N)
    (H_density : DensityBound μ N p) :
    μ {x : ℝ | |x - a| * c < δ} ≤ ENNReal.ofReal (2 * p * δ / c) := by
  have h := H_density _ measurableSet_Ioo hN
  rw [← band_set_eq a c δ hc, band_set_volume a c δ hc, ← ENNReal.ofReal_mul hp] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  ring

/-- `Ioo (a - δ/c) (a + δ/c) ⊆ Ioo (a - δ) (a + δ)` when `c ≥ 1`. -/
theorem Ioo_shrink {a c δ : ℝ} (hδ : 0 ≤ δ) (hc : 1 ≤ c) :
    Ioo (a - δ / c) (a + δ / c) ⊆ Ioo (a - δ) (a + δ) := by
  have h := div_le_self hδ hc
  intro x hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

namespace LinLoop

variable (L : LinLoop)

/-- The unresolved set at read time `T` is the interval of half-width
`delta * exp (-T / tau_r)` around `vs`. -/
theorem unresolved_eq (T δ : ℝ) :
    {v0 : ℝ | |L.sol v0 T - L.vs| < δ}
      = Ioo (L.vs - δ * exp (-(T / L.taur))) (L.vs + δ * exp (-(T / L.taur))) := by
  have hE := exp_pos (T / L.taur)
  have : {v0 : ℝ | |L.sol v0 T - L.vs| < δ} = {x : ℝ | |x - L.vs| * exp (T / L.taur) < δ} := by
    ext x; simp only [mem_ofPred_eq, L.sol_dev]
  rw [this, band_set_eq _ _ _ hE]
  simp only [exp_neg, div_eq_mul_inv]

/-- (3, length) its length is `2 * delta * exp (-T / tau_r)`. -/
theorem unresolved_volume (T δ : ℝ) :
    volume {v0 : ℝ | |L.sol v0 T - L.vs| < δ}
      = ENNReal.ofReal (2 * δ * exp (-(T / L.taur))) := by
  rw [L.unresolved_eq, Real.volume_Ioo]
  congr 1
  ring

/-- (3) Probabilistic bound.  If the law `μ` of the initial offset has density
`≤ p` on the band `|v0 - vs| < delta` (H_density) and the read happens at
`T ≥ 0`, then `P(|v(T) - vs| < delta) ≤ 2 p delta exp(-T/tau_r)`. -/
theorem prob_unresolved (μ : Measure ℝ) {N : Set ℝ} {T δ p : ℝ}
    (hT : 0 ≤ T) (hδ : 0 < δ) (hp : 0 ≤ p)
    (hN : Ioo (L.vs - δ) (L.vs + δ) ⊆ N)
    (H_density : DensityBound μ N p) :
    μ {v0 : ℝ | |L.sol v0 T - L.vs| < δ}
      ≤ ENNReal.ofReal (2 * p * δ * exp (-(T / L.taur))) := by
  have hE := exp_pos (T / L.taur)
  have hE1 : 1 ≤ exp (T / L.taur) := one_le_exp (div_nonneg hT L.taur_pos.le)
  have hset : {v0 : ℝ | |L.sol v0 T - L.vs| < δ}
      = {x : ℝ | |x - L.vs| * exp (T / L.taur) < δ} := by
    ext x; simp only [mem_ofPred_eq, L.sol_dev]
  rw [hset]
  refine (prob_band μ hE hp ((Ioo_shrink hδ.le hE1).trans hN) H_density).trans (le_of_eq ?_)
  simp only [exp_neg, div_eq_mul_inv]

/-- (3, timing form) The initial offset is set by the request-edge timing
difference: `v0 = vs + k * Δt` (H_affine_offset, `k ≠ 0`; physically the
slew of the set/reset drive into the node times the overlap time; testable by
sweeping `Δt` in a transistor-level or GLS-with-analog-node model).  If the law
`ν` of `Δt` has density `≤ q` on `|Δt| < δ/|k|`, then

    P(unresolved at T) ≤ q * (2 δ / |k|) * exp (-T / tau_r)

i.e. `q * T0 * exp(-T/tau_r)` with aperture `T0 = 2 δ / |k|`. -/
theorem prob_unresolved_dt (ν : Measure ℝ) {N : Set ℝ} {T δ q k : ℝ}
    (hT : 0 ≤ T) (hδ : 0 < δ) (hq : 0 ≤ q) (hk : k ≠ 0)
    (hN : Ioo (-(δ / |k|)) (δ / |k|) ⊆ N)
    (H_density : DensityBound ν N q) :
    ν {dt : ℝ | |L.sol (L.vs + k * dt) T - L.vs| < δ}
      ≤ ENNReal.ofReal (q * (2 * δ / |k|) * exp (-(T / L.taur))) := by
  have hk' : 0 < |k| := abs_pos.mpr hk
  have hE := exp_pos (T / L.taur)
  have hE1 : 1 ≤ exp (T / L.taur) := one_le_exp (div_nonneg hT L.taur_pos.le)
  have hc : 0 < |k| * exp (T / L.taur) := mul_pos hk' hE
  have hset : {dt : ℝ | |L.sol (L.vs + k * dt) T - L.vs| < δ}
      = {x : ℝ | |x - 0| * (|k| * exp (T / L.taur)) < δ} := by
    ext x
    simp only [mem_ofPred_eq, L.sol_dev, add_sub_cancel_left, sub_zero, abs_mul]
    rw [mul_comm |k| |x|, mul_assoc]
  have hsub : Ioo (0 - δ / (|k| * exp (T / L.taur))) (0 + δ / (|k| * exp (T / L.taur)))
      ⊆ N := by
    refine Subset.trans ?_ hN
    have h1 : δ / (|k| * exp (T / L.taur)) ≤ δ / |k| := by
      rw [← div_div]
      exact div_le_self (div_pos hδ hk').le hE1
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [hset]
  refine (prob_band ν hc hq hsub H_density).trans (le_of_eq ?_)
  congr 1
  rw [exp_neg]
  field_simp

end LinLoop

/-! ## Nonlinear loop: comparison with a minimum escape rate -/

/-- (4a) Nonlinear growth.  `v' = F v` on `[0, T]`; inside the band the escape
rate is at least `γ` (H_escape: `F x * (x - vs) ≥ γ (x - vs)^2`).  If the
trajectory stays in the band on `[0, T]` then its squared deviation grew at
least like `exp (2 γ t)`. -/
theorem nonlinear_growth {F v : ℝ → ℝ} {vs γ δ T : ℝ} (hT : 0 ≤ T)
    (hode : ∀ t ∈ Icc 0 T, HasDerivAt v (F (v t)) t)
    (H_escape : ∀ x, |x - vs| < δ → γ * ((x - vs) * (x - vs)) ≤ F x * (x - vs))
    (hband : ∀ t ∈ Icc 0 T, |v t - vs| < δ) :
    ∀ t ∈ Icc 0 T, (v 0 - vs) * (v 0 - vs) * exp (2 * γ * t)
      ≤ (v t - vs) * (v t - vs) := by
  set w : ℝ → ℝ := fun t => (v t - vs) * (v t - vs) * exp (-(2 * γ * t)) with hw
  have hwd : ∀ t ∈ Icc 0 T, HasDerivAt w
      ((F (v t) * (v t - vs) + (v t - vs) * F (v t)) * exp (-(2 * γ * t))
        + (v t - vs) * (v t - vs) * (exp (-(2 * γ * t)) * -(2 * γ * 1))) t := by
    intro t ht
    have hs := (hode t ht).sub_const vs
    have h1 : HasDerivAt (fun t : ℝ => -(2 * γ * t)) (-(2 * γ * 1)) t :=
      ((hasDerivAt_id' (x := t)).const_mul (2 * γ)).neg
    exact (hs.mul hs).mul h1.exp
  have hnn : ∀ t ∈ Icc 0 T, 0 ≤
      (F (v t) * (v t - vs) + (v t - vs) * F (v t)) * exp (-(2 * γ * t))
        + (v t - vs) * (v t - vs) * (exp (-(2 * γ * t)) * -(2 * γ * 1)) := by
    intro t ht
    have hk := H_escape (v t) (hband t ht)
    have hE := exp_pos (-(2 * γ * t))
    have heq : (F (v t) * (v t - vs) + (v t - vs) * F (v t)) * exp (-(2 * γ * t))
        + (v t - vs) * (v t - vs) * (exp (-(2 * γ * t)) * -(2 * γ * 1))
        = 2 * exp (-(2 * γ * t)) * (F (v t) * (v t - vs) - γ * ((v t - vs) * (v t - vs))) := by
      ring
    rw [heq]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr hk)
  have hmono : MonotoneOn w (Icc 0 T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 T)
    · exact fun t ht => (hwd t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hwd t (Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hwd t (Ioo_subset_Icc_self ht)).deriv]
      exact hnn t (Ioo_subset_Icc_self ht)
  intro t ht
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have h := hmono h0 ht ht.1
  simp only [hw, mul_zero, neg_zero, exp_zero, mul_one] at h
  have he : exp (-(2 * γ * t)) * exp (2 * γ * t) = 1 := by
    rw [← exp_add]; simp
  have h2 := mul_le_mul_of_nonneg_right h (exp_pos (2 * γ * t)).le
  rw [mul_assoc ((v t - vs) * (v t - vs)), he, mul_one] at h2
  exact h2

/-- (4b) Absolute-value form: `|v t - vs| ≥ |v 0 - vs| * exp (γ t)`. -/
theorem nonlinear_growth_abs {F v : ℝ → ℝ} {vs γ δ T : ℝ} (hT : 0 ≤ T)
    (hode : ∀ t ∈ Icc 0 T, HasDerivAt v (F (v t)) t)
    (H_escape : ∀ x, |x - vs| < δ → γ * ((x - vs) * (x - vs)) ≤ F x * (x - vs))
    (hband : ∀ t ∈ Icc 0 T, |v t - vs| < δ) :
    ∀ t ∈ Icc 0 T, |v 0 - vs| * exp (γ * t) ≤ |v t - vs| := by
  intro t ht
  have h := nonlinear_growth hT hode H_escape hband t ht
  have hsq : (|v 0 - vs| * exp (γ * t)) ^ 2 ≤ (v t - vs) ^ 2 := by
    have he : exp (γ * t) ^ 2 = exp (2 * γ * t) := by
      rw [sq, ← exp_add]; congr 1; ring
    rw [mul_pow, sq_abs, he, sq, sq]
    exact h
  have h3 := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (mul_nonneg (abs_nonneg _) (exp_pos _).le)] at h3

/-- (4c) Nonlinear probabilistic bound.  `traj v0` is the trajectory started
at `v0` (`traj v0 0 = v0`), each obeying `v' = F v` on `[0, T]`, with escape
rate `≥ γ > 0` in the band.  The set of `v0` still unresolved on all of
`[0, T]` has `μ`-measure `≤ 2 p δ exp (-γ T)`. -/
theorem nonlinear_prob_unresolved (μ : Measure ℝ) {N : Set ℝ}
    {F : ℝ → ℝ} {traj : ℝ → ℝ → ℝ} {vs γ δ p T : ℝ}
    (hT : 0 ≤ T) (hγ : 0 ≤ γ) (hδ : 0 < δ) (hp : 0 ≤ p)
    (hinit : ∀ v0, traj v0 0 = v0)
    (hode : ∀ v0, ∀ t ∈ Icc 0 T, HasDerivAt (traj v0) (F (traj v0 t)) t)
    (H_escape : ∀ x, |x - vs| < δ → γ * ((x - vs) * (x - vs)) ≤ F x * (x - vs))
    (hN : Ioo (vs - δ) (vs + δ) ⊆ N)
    (H_density : DensityBound μ N p) :
    μ {v0 : ℝ | ∀ t ∈ Icc 0 T, |traj v0 t - vs| < δ}
      ≤ ENNReal.ofReal (2 * p * δ * exp (-(γ * T))) := by
  have hE := exp_pos (γ * T)
  have hE1 : 1 ≤ exp (γ * T) := one_le_exp (mul_nonneg hγ hT)
  have hsub : {v0 : ℝ | ∀ t ∈ Icc 0 T, |traj v0 t - vs| < δ}
      ⊆ {x : ℝ | |x - vs| * exp (γ * T) < δ} := by
    intro v0 hv0
    have hTmem : T ∈ Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
    have h := nonlinear_growth_abs hT (hode v0) H_escape hv0 T hTmem
    rw [hinit] at h
    exact lt_of_le_of_lt h (hv0 T hTmem)
  refine (measure_mono hsub).trans
    ((prob_band μ hE hp ((Ioo_shrink hδ.le hE1).trans hN) H_density).trans (le_of_eq ?_))
  simp only [exp_neg, div_eq_mul_inv]

/-- (4d) The same in the circuit's own terms: `tau * v' = f(v) - v` and a
lower bound `g_min > 1` on the loop gain in the band, in the form
H_GAIN_BAND: `(f x - x) * (x - vs) ≥ (g_min - 1) * (x - vs)^2` for
`|x - vs| < δ` (for a linear `f x = vs + g (x - vs)` this is equality with
`g_min = g`).  Then `P(unresolved on [0,T]) ≤ 2 p δ exp(-T/tau_r,max)` with
`tau_r,max = tau / (g_min - 1)`. -/
theorem gain_prob_unresolved (μ : Measure ℝ) {N : Set ℝ}
    {f : ℝ → ℝ} {traj : ℝ → ℝ → ℝ} {tau gmin vs δ p T : ℝ}
    (H_tau_pos : 0 < tau) (H_gmin : 1 ≤ gmin)
    (hT : 0 ≤ T) (hδ : 0 < δ) (hp : 0 ≤ p)
    (hinit : ∀ v0, traj v0 0 = v0)
    (hode : ∀ v0, ∀ t ∈ Icc 0 T,
      HasDerivAt (traj v0) ((f (traj v0 t) - traj v0 t) / tau) t)
    (H_gain_band : ∀ x, |x - vs| < δ →
      (gmin - 1) * ((x - vs) * (x - vs)) ≤ (f x - x) * (x - vs))
    (hN : Ioo (vs - δ) (vs + δ) ⊆ N)
    (H_density : DensityBound μ N p) :
    μ {v0 : ℝ | ∀ t ∈ Icc 0 T, |traj v0 t - vs| < δ}
      ≤ ENNReal.ofReal (2 * p * δ * exp (-(T / (tau / (gmin - 1))))) := by
  have hγ : 0 ≤ (gmin - 1) / tau := div_nonneg (by linarith) H_tau_pos.le
  have hesc : ∀ x, |x - vs| < δ →
      (gmin - 1) / tau * ((x - vs) * (x - vs)) ≤ (fun y => (f y - y) / tau) x * (x - vs) := by
    intro x hx
    have h := H_gain_band x hx
    have e1 : (gmin - 1) / tau * ((x - vs) * (x - vs))
        = (gmin - 1) * ((x - vs) * (x - vs)) / tau := by ring
    have e2 : (fun y => (f y - y) / tau) x * (x - vs) = (f x - x) * (x - vs) / tau := by
      show (f x - x) / tau * (x - vs) = _
      ring
    rw [e1, e2]
    exact (div_le_div_iff_of_pos_right H_tau_pos).mpr h
  have hrate : T / (tau / (gmin - 1)) = (gmin - 1) / tau * T := by
    rw [div_div_eq_mul_div]; ring
  rw [hrate]
  exact nonlinear_prob_unresolved (F := fun y => (f y - y) / tau) μ hT hγ hδ hp hinit hode hesc hN H_density

/-! ## MTBF -/

/-- (6) MTBF algebra.  If arbitration events arrive at rate `f1`, the timing
offset of the other request has density `≤ f2` (uniform phase of a stream of
rate `f2`), and each event fails with probability
`≤ f2 * T0 * exp (-T / tau_r)` (`LinLoop.prob_unresolved_dt`), then the failure
rate `λ ≤ f1 * f2 * T0 * exp (-T/tau_r)` and
`MTBF = 1/λ ≥ exp (T / tau_r) / (T0 * f1 * f2)`. -/
theorem mtbf_lower {lam f1 f2 T0 T taur : ℝ}
    (hlam : 0 < lam) (hf1 : 0 < f1) (hf2 : 0 < f2) (hT0 : 0 < T0)
    (hbound : lam ≤ f1 * f2 * T0 * exp (-(T / taur))) :
    exp (T / taur) / (T0 * f1 * f2) ≤ 1 / lam := by
  have hE := exp_pos (T / taur)
  have h := one_div_le_one_div_of_le hlam hbound
  refine Eq.trans_le ?_ h
  rw [exp_neg]
  field_simp

end Formal.Cells.ArbResolve
