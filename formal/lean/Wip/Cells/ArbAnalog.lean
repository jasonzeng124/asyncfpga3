import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Order.IntermediateValue
import Formal.Cells.Prelim

/-!
# Track 7c: the arbiter's state node as an analog loop

PROGRAM.md track 7 / layer 4: one first-order gate per storage loop,

    tau * v' = F(r1(t), r2(t), v) - v,

where `v` is the (normalized, 0 = GND, 1 = VCCINT) voltage of the state node `q`
of `bd_arbcell` / `bd_arbiter` (`cells/rtl/bd_arb.v`), and `F` is the continuous
transfer function of the state LUT seen from its three live pins (r1, r2, q).

Results (all for EVERY transfer function satisfying the named hypotheses):

* `rail_hold`, `qNext_*`: the real INIT constants evaluated with `lutB`; at the
  rails `F` must agree with them (`H_INIT`), in particular `F(1,1,0)=0`,
  `F(1,1,1)=1` (the hold region of the C-element).
* `sol_dist_le`, `H_CONT_of_lipschitz`: Groenwall. The state at a fixed time is
  Lipschitz in the timing parameter `s` of the inputs (this DISCHARGES the
  continuity hypothesis H_CONT from Lipschitz `F` and finite input slew).
* `buridan`, `no_valid_level`, `analog_arbiter_not_exclusive`: Marino (1981) /
  Buridan. For every fixed observation time `T` there is an input timing `s`
  for which `q(T)` is strictly between `VIL` and `VIH`. So "for every input
  timing, q is a valid logic level by time T" is FALSE for every T.
* `exists_equilibrium`, `unstable_equilibrium`: in the hold region a loop with
  gain > 1 at the midpoint has an interior equilibrium `vs` and it is unstable
  (field derivative `(g-1)/tau > 0`).
* `metastable_forever`: one timing `s*` puts the node exactly on `vs` when the
  hold region starts, and then (ODE uniqueness) it stays there for ALL later
  times: no resolution-time bound holds for every input timing.
* `aperture_lower_bound`: for timings `s` near `s*`, `|q(t) - vs|` is at most
  `C * |s - s*| * exp(K (t - tw))`: the set of bad timings at resolution time
  `t` contains an interval of width proportional to `exp(-K (t - tw))`. This is
  the lower-bound half of the e^(-t/tau) law (the failure probability cannot
  decay faster than exponentially).
-/

open Set Filter Real
open scoped Topology NNReal

namespace Formal.Cells.ArbAnalog

/-! ## The binary INIT, from the real constants -/

/-- `bd_arbcell`'s state node: `bd_c2n_set`, `LUT6 INIT 64'hFFB2_FFB2_FFB2_FFB2`,
pins `[I0..I5] = [r1, r2, q, rst, 0, 0]` (`cells/rtl/bd_ce.v`). -/
def ARBCELL_INIT : Nat := 0xFFB2FFB2FFB2FFB2

/-- `bd_arbiter`'s state node `ustate`: `LUT6_2 INIT 64'hFFF0_FFB2_ACAC_ACAC`,
pins `[r1, r2, q, rst, A0, 1]`, `q` on O6 (`cells/rtl/bd_arb.v`). -/
def ARBITER_INIT : Nat := 0xFFF0FFB2ACACACAC

/-- Next value of `q` with `rst = 0`, read from the bd_arbcell INIT with `lutB`. -/
def qNext (r1 r2 q : Bool) : Bool := lutB ARBCELL_INIT [r1, r2, q, false, false, false]

/-- The shipped arbiter's state node agrees with bd_arbcell's while `rst = 0`
and `A0 = 0` (the window in which `q` is live). -/
theorem qNext_eq_arbiter (r1 r2 q : Bool) :
    qNext r1 r2 q = o6B ARBITER_INIT [r1, r2, q, false, false, true] := by
  cases r1 <;> cases r2 <;> cases q <;> decide

/-- The INIT is `C(r1, ~r2)`: set on `r1 ~r2`, reset on `~r1 r2`, else hold. -/
theorem qNext_eq_C (r1 r2 q : Bool) :
    qNext r1 r2 q = ((r1 && !r2) || (q && !(!r1 && r2))) := by
  cases r1 <;> cases r2 <;> cases q <;> decide

/-- With `A0 = 1` the shipped node holds `q` whatever the requests do. -/
theorem arbiter_holds_on_A0 (r1 r2 q : Bool) :
    o6B ARBITER_INIT [r1, r2, q, false, true, true] = q := by
  cases r1 <;> cases r2 <;> cases q <;> decide

/-- Normalized rail voltage of a logic value. -/
def rail : Bool → ℝ
  | true => 1
  | false => 0

/-! ## The analog loop -/

/-- One first-order gate closing the state loop. Every field is a named hypothesis. -/
structure Loop where
  /-- Loop time constant (LUT + feedback wire), seconds. -/
  tau : ℝ
  /-- Continuous transfer function of the state LUT, inputs `(r1, r2, q)`. -/
  F : ℝ → ℝ → ℝ → ℝ
  /-- Lipschitz constant of `F`. -/
  L : ℝ≥0
  /-- **H_TAU**: the loop has a positive time constant. -/
  H_TAU : 0 < tau
  /-- **H_LIP**: `F` is Lipschitz in all three pins (finite gain everywhere).
  Physical fact: a CMOS mux tree with input buffers has bounded small-signal
  gain. Test: DC sweep of one LUT pin in SPICE/board (slow ramp, scope the output). -/
  H_LIP : ∀ a b v a' b' v', |F a b v - F a' b' v'| ≤ L * (|a - a'| + |b - b'| + |v - v'|)
  /-- **H_INIT**: at the rails the LUT outputs the rail its INIT says
  (static logic levels are restored). Test: any binary GLS / board run. -/
  H_INIT : ∀ r1 r2 q : Bool, F (rail r1) (rail r2) (rail q) = rail (qNext r1 r2 q)

namespace Loop

variable (m : Loop)

/-- Right-hand side of `v' = (F(r1, r2, v) - v) / tau`. -/
noncomputable def field (a b v : ℝ) : ℝ := (m.F a b v - v) / m.tau

/-- Lipschitz constant of the field in `v`: `(L + 1) / tau`. -/
noncomputable def K : ℝ≥0 := Real.toNNReal ((m.L + 1) / m.tau)

lemma K_coe : (m.K : ℝ) = (m.L + 1) / m.tau :=
  Real.coe_toNNReal _ (div_nonneg (by positivity) m.H_TAU.le)

/-- The hold region of the INIT, at the rails: `F(1,1,0) = 0`, `F(1,1,1) = 1`. -/
theorem rail_hold : m.F 1 1 0 = 0 ∧ m.F 1 1 1 = 1 := by
  have h0 := m.H_INIT true true false
  have h1 := m.H_INIT true true true
  have e0 : qNext true true false = false := by decide
  have e1 : qNext true true true = true := by decide
  rw [e0] at h0
  rw [e1] at h1
  exact ⟨h0, h1⟩

lemma field_sub (a b v a' b' v' : ℝ) :
    m.field a b v - m.field a' b' v' = ((m.F a b v - m.F a' b' v') - (v - v')) / m.tau := by
  unfold field; ring

lemma abs_field_sub_le (a b v a' b' v' : ℝ) :
    |m.field a b v - m.field a' b' v'|
      ≤ (m.L * (|a - a'| + |b - b'| + |v - v'|) + |v - v'|) / m.tau := by
  have htau := m.H_TAU.le
  rw [field_sub, abs_div, abs_of_pos m.H_TAU]
  gcongr
  calc |(m.F a b v - m.F a' b' v') - (v - v')|
      ≤ |m.F a b v - m.F a' b' v'| + |v - v'| := abs_sub _ _
    _ ≤ _ := by gcongr; exact m.H_LIP _ _ _ _ _ _

lemma field_lipschitz (a b : ℝ) : LipschitzWith m.K (m.field a b) := by
  refine LipschitzWith.of_dist_le_mul fun v v' => ?_
  rw [Real.dist_eq, Real.dist_eq, m.K_coe]
  have h := m.abs_field_sub_le a b v a b v'
  simp only [sub_self, abs_zero, zero_add] at h
  calc _ ≤ _ := h
    _ = (m.L + 1) / m.tau * |v - v'| := by ring

end Loop

/-- A family of input waveforms indexed by the timing parameter `s`
(e.g. r1 rising at 0 and r2 rising at `s`). -/
structure Stim where
  u1 : ℝ → ℝ → ℝ
  u2 : ℝ → ℝ → ℝ
  M : ℝ
  /-- **H_STIM_LIP**: shifting the timing by `ds` moves each input by at most
  `M * |ds|` at every instant (finite slew rate `M`, volts/s normalized).
  Physical fact: every real edge has a nonzero rise time. -/
  H_STIM_LIP : ∀ s s' t, |u1 s t - u1 s' t| ≤ M * |s - s'| ∧ |u2 s t - u2 s' t| ≤ M * |s - s'|

/-- The canonical stimulus: `r1 = ρ1(t)` fixed, `r2 = ρ2(t - s)` shifted by `s`,
with `ρ2` an edge of finite slew (Lipschitz with constant `M`). -/
def rampStim (ρ1 ρ2 : ℝ → ℝ) (M : ℝ≥0) (h2 : LipschitzWith M ρ2) : Stim where
  u1 _ t := ρ1 t
  u2 s t := ρ2 (t - s)
  M := M
  H_STIM_LIP s s' t := by
    refine ⟨by simp only [sub_self, abs_zero]; positivity, ?_⟩
    have := h2.dist_le_mul (t - s) (t - s')
    rw [Real.dist_eq, Real.dist_eq] at this
    calc _ ≤ _ := this
      _ = (M : ℝ) * |s - s'| := by
        rw [show (t - s) - (t - s') = -(s - s') by ring, abs_neg]

/-- `x s` is a solution on `[0, ∞)` from `v0`, for each timing `s`.
(Existence: Picard-Lindelof; uniqueness: `ODE_solution_unique`. We quantify over
every solution family, so existence is not needed for soundness, only for
non-vacuity; see the notes.) -/
structure IsSolFamily (m : Loop) (S : Stim) (v0 : ℝ) (x : ℝ → ℝ → ℝ) : Prop where
  init : ∀ s, x s 0 = v0
  cont : ∀ s, ContinuousOn (x s) (Ici 0)
  deriv : ∀ s t, 0 ≤ t →
    HasDerivWithinAt (x s) (m.field (S.u1 s t) (S.u2 s t) (x s t)) (Ici t) t

lemma gronwallBound_zero_left (K ε T : ℝ) :
    gronwallBound 0 K ε T = ε * gronwallBound 0 K 1 T := by
  unfold gronwallBound; split_ifs <;> ring

/-! ## H_CONT, discharged by Groenwall -/

section Cont
variable {m : Loop} {S : Stim} {v0 : ℝ} {x : ℝ → ℝ → ℝ}

/-- Continuous dependence on the input timing (Groenwall): the solutions for two
timings `s, s'` differ at time `T` by at most `C(T) * |s - s'|`, where
`C(T) = 2 L M / tau * gronwallBound 0 K 1 T`. -/
theorem sol_dist_le (hx : IsSolFamily m S v0 x) (s s' T : ℝ) (hT : 0 ≤ T) :
    |x s T - x s' T|
      ≤ 2 * m.L * S.M / m.tau * gronwallBound 0 m.K 1 T * |s - s'| := by
  have key := dist_le_of_approx_trajectories_ODE
    (v := fun t => m.field (S.u1 s t) (S.u2 s t)) (K := m.K)
    (f := x s) (g := x s')
    (f' := fun t => m.field (S.u1 s t) (S.u2 s t) (x s t))
    (g' := fun t => m.field (S.u1 s' t) (S.u2 s' t) (x s' t))
    (a := 0) (b := T) (εf := 0) (εg := 2 * m.L * S.M * |s - s'| / m.tau) (δ := 0)
    (fun t => m.field_lipschitz _ _)
    ((hx.cont s).mono Icc_subset_Ici_self)
    (fun t ht => hx.deriv s t ht.1)
    (fun t _ => by simp)
    ((hx.cont s').mono Icc_subset_Ici_self)
    (fun t ht => hx.deriv s' t ht.1)
    (fun t _ => by
      rw [Real.dist_eq]
      have htau := m.H_TAU.le
      have h := m.abs_field_sub_le (S.u1 s' t) (S.u2 s' t) (x s' t)
        (S.u1 s t) (S.u2 s t) (x s' t)
      obtain ⟨h1, h2⟩ := S.H_STIM_LIP s' s t
      rw [abs_sub_comm s' s] at h1 h2
      simp only [sub_self, abs_zero, add_zero] at h
      calc _ ≤ _ := h
        _ ≤ m.L * (S.M * |s - s'| + S.M * |s - s'|) / m.tau := by
          gcongr <;> assumption
        _ = _ := by ring)
    (by simp [hx.init])
    T ⟨hT, le_rfl⟩
  rw [Real.dist_eq, zero_add, sub_zero, gronwallBound_zero_left] at key
  calc _ ≤ _ := key
    _ = _ := by ring

/-- **H_CONT, proved**: the state at any fixed time `T ≥ 0` is a continuous
(indeed Lipschitz) function of the timing parameter. -/
theorem H_CONT_of_lipschitz (hx : IsSolFamily m S v0 x) (T : ℝ) (hT : 0 ≤ T) :
    Continuous fun s => x s T := by
  refine (LipschitzWith.of_dist_le_mul
    (K := (2 * m.L * S.M / m.tau * gronwallBound 0 m.K 1 T).toNNReal)
    fun s s' => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq]
  exact (sol_dist_le hx s s' T hT).trans
    (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (abs_nonneg _))

end Cont

/-! ## Buridan / Marino: no unconditional valid level -/

/-- Abstract Buridan principle: a continuous map from timings to states that
takes both values `f sA`, `f sB` takes every value between them. -/
theorem buridan {f : ℝ → ℝ} {sA sB c : ℝ} (hab : sA ≤ sB)
    (H_CONT : ContinuousOn f (Icc sA sB)) (hc : c ∈ uIcc (f sA) (f sB)) :
    ∃ s ∈ Icc sA sB, f s = c := by
  have hc' : ContinuousOn f (uIcc sA sB) := by rwa [uIcc_of_le hab]
  obtain ⟨s, hs, hfs⟩ := intermediate_value_uIcc hc' hc
  rw [uIcc_of_le hab] at hs
  exact ⟨s, hs, hfs⟩

/-- If one timing gives a valid 0 (`≤ VIL`) and another a valid 1 (`≥ VIH`),
some timing in between gives an invalid level, strictly inside `(VIL, VIH)`. -/
theorem no_valid_level {f : ℝ → ℝ} {sA sB VIL VIH : ℝ} (hab : sA ≤ sB) (hV : VIL < VIH)
    (H_CONT : ContinuousOn f (Icc sA sB))
    (H_ENDS : (f sA ≤ VIL ∧ VIH ≤ f sB) ∨ (f sB ≤ VIL ∧ VIH ≤ f sA)) :
    ∃ s ∈ Icc sA sB, VIL < f s ∧ f s < VIH := by
  have hc : (VIL + VIH) / 2 ∈ uIcc (f sA) (f sB) := by
    rw [mem_uIcc]
    rcases H_ENDS with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; constructor <;> linarith
    · right; constructor <;> linarith
  obtain ⟨s, hs, h⟩ := buridan hab H_CONT hc
  exact ⟨s, hs, by linarith, by linarith⟩

/-- **Main impossibility theorem (track 7c, goal 1).** For the analog state loop
of the arbiter, under H_TAU, H_LIP, H_INIT, H_STIM_LIP, and for ANY observation
time `T ≥ 0`: if the uncontested ends of the timing sweep give valid levels of
opposite value at `T` (**H_ENDS**: the cell works when the requests are far
apart), then some timing in between leaves `q(T)` strictly between `VIL` and
`VIH`. Mutual exclusion by time `T` is therefore not provable for all input
timings, for any `T`. -/
theorem analog_arbiter_not_exclusive (m : Loop) (S : Stim) {v0 : ℝ} {x : ℝ → ℝ → ℝ}
    (hx : IsSolFamily m S v0 x) {T sA sB VIL VIH : ℝ} (hT : 0 ≤ T) (hab : sA ≤ sB)
    (hV : VIL < VIH)
    (H_ENDS : (x sA T ≤ VIL ∧ VIH ≤ x sB T) ∨ (x sB T ≤ VIL ∧ VIH ≤ x sA T)) :
    ∃ s ∈ Icc sA sB, VIL < x s T ∧ x s T < VIH :=
  no_valid_level hab hV (H_CONT_of_lipschitz hx T hT).continuousOn H_ENDS

/-- The same, as the negation of the claim one would like to prove. -/
theorem not_forall_valid (m : Loop) (S : Stim) {v0 : ℝ} {x : ℝ → ℝ → ℝ}
    (hx : IsSolFamily m S v0 x) {T sA sB VIL VIH : ℝ} (hT : 0 ≤ T) (hab : sA ≤ sB)
    (hV : VIL < VIH)
    (H_ENDS : (x sA T ≤ VIL ∧ VIH ≤ x sB T) ∨ (x sB T ≤ VIL ∧ VIH ≤ x sA T)) :
    ¬ ∀ s, x s T ≤ VIL ∨ VIH ≤ x s T := by
  intro hall
  obtain ⟨s, _, h1, h2⟩ := analog_arbiter_not_exclusive m S hx hT hab hV H_ENDS
  rcases hall s with h | h <;> linarith

/-! ## The hold region: equilibrium, instability, metastability forever -/

namespace Loop
variable (m : Loop)

lemma hold_continuous : Continuous fun v => m.F 1 1 v := by
  refine (LipschitzWith.of_dist_le_mul (K := m.L) fun v v' => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq]
  have := m.H_LIP 1 1 v 1 1 v'
  simpa using this

/-- **Goal 2a.** With both requests held high the loop is the hold transfer
`G v = F(1,1,v)`. **H_GAIN**: some `a ≤ b` with `G a ≤ a` and `G b ≥ b` (the
loop pulls down below the midpoint and up above it, i.e. regenerative
feedback). Then there is an equilibrium `vs ∈ [a, b]`. -/
theorem exists_equilibrium {a b : ℝ} (hab : a ≤ b)
    (H_GAIN : m.F 1 1 a ≤ a ∧ b ≤ m.F 1 1 b) : ∃ vs ∈ Icc a b, m.F 1 1 vs = vs := by
  have hc : ContinuousOn (fun v => m.F 1 1 v - v) (Icc a b) :=
    (m.hold_continuous.sub continuous_id).continuousOn
  obtain ⟨vs, hvs, h⟩ := intermediate_value_Icc hab hc
    (show (0 : ℝ) ∈ Icc (m.F 1 1 a - a) (m.F 1 1 b - b) from
      ⟨by linarith [H_GAIN.1], by linarith [H_GAIN.2]⟩)
  exact ⟨vs, hvs, by simp only at h; linarith⟩

/-- **Goal 2b.** At an equilibrium `vs` of the hold loop where `G` has slope
`g > 1`, the field has slope `(g - 1)/tau > 0`: it pushes `v` up just above
`vs` and down just below it. `vs` is unstable (in the 2-gate picture, a saddle). -/
theorem unstable_equilibrium {vs g : ℝ} (heq : m.F 1 1 vs = vs)
    (hd : HasDerivAt (fun v => m.F 1 1 v) g vs) (hg : 1 < g) :
    HasDerivAt (m.field 1 1) ((g - 1) / m.tau) vs ∧
    (∀ᶠ v in 𝓝[>] vs, 0 < m.field 1 1 v) ∧
    (∀ᶠ v in 𝓝[<] vs, m.field 1 1 v < 0) := by
  have hφ : HasDerivAt (m.field 1 1) ((g - 1) / m.tau) vs :=
    (hd.sub (hasDerivAt_id vs)).div_const m.tau
  have hlam : 0 < (g - 1) / m.tau := div_pos (by linarith) m.H_TAU
  have h0 : m.field 1 1 vs = 0 := by simp [field, heq]
  have hs : ∀ᶠ v in 𝓝[≠] vs, 0 < slope (m.field 1 1) vs v :=
    (hasDerivAt_iff_tendsto_slope.mp hφ).eventually (lt_mem_nhds hlam)
  refine ⟨hφ, ?_, ?_⟩
  · have hs' := hs.filter_mono (nhdsWithin_mono vs (fun v (hv : vs < v) => hv.ne'))
    filter_upwards [hs', self_mem_nhdsWithin] with v hsl (hv : vs < v)
    rw [slope_def_field, h0, sub_zero] at hsl
    exact (div_pos_iff_of_pos_right (sub_pos.mpr hv)).mp hsl
  · have hs' := hs.filter_mono (nhdsWithin_mono vs (fun v (hv : v < vs) => hv.ne))
    filter_upwards [hs', self_mem_nhdsWithin] with v hsl (hv : v < vs)
    rw [slope_def_field, h0, sub_zero] at hsl
    by_contra hc
    push_neg at hc
    have : (m.field 1 1 v) / (v - vs) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos hc (by linarith)
    linarith

end Loop

section Hold
variable {m : Loop} {S : Stim} {v0 : ℝ} {x : ℝ → ℝ → ℝ}

/-- **H_HOLD_INPUTS**: from time `tw` on, both requests are fully high for every
timing in the sweep (the contention window is over; the cell is in its hold
region). Test: by construction of the stimulus. -/
def HoldInputs (S : Stim) (sA sB tw : ℝ) : Prop :=
  ∀ s ∈ Icc sA sB, ∀ t, tw ≤ t → S.u1 s t = 1 ∧ S.u2 s t = 1

lemma hold_deriv (hx : IsSolFamily m S v0 x) {sA sB tw : ℝ} (htw : 0 ≤ tw)
    (hH : HoldInputs S sA sB tw) {s : ℝ} (hs : s ∈ Icc sA sB) {t : ℝ} (ht : tw ≤ t) :
    HasDerivWithinAt (x s) (m.field 1 1 (x s t)) (Ici t) t := by
  have h := hx.deriv s t (htw.trans ht)
  rwa [(hH s hs t ht).1, (hH s hs t ht).2] at h

/-- **Metastability forever.** If the hold equilibrium `vs` lies between the
states the two ends of the sweep reach at `tw`, one timing `s*` puts `q`
exactly on `vs` at `tw`, and then `q(t) = vs` for EVERY `t ≥ tw` (ODE
uniqueness). No resolution time works for all input timings. -/
theorem metastable_forever (hx : IsSolFamily m S v0 x) {sA sB tw vs : ℝ}
    (hab : sA ≤ sB) (htw : 0 ≤ tw) (hH : HoldInputs S sA sB tw)
    (heq : m.F 1 1 vs = vs) (hvs : vs ∈ uIcc (x sA tw) (x sB tw)) :
    ∃ s ∈ Icc sA sB, ∀ t, tw ≤ t → x s t = vs := by
  obtain ⟨s, hs, hxs⟩ := buridan hab (H_CONT_of_lipschitz hx tw htw).continuousOn hvs
  refine ⟨s, hs, fun t ht => ?_⟩
  have h0 : m.field 1 1 vs = 0 := by simp [Loop.field, heq]
  have := ODE_solution_unique (v := fun _ => m.field 1 1) (K := m.K)
    (f := x s) (g := fun _ => vs) (a := tw) (b := t)
    (fun _ => m.field_lipschitz 1 1)
    ((hx.cont s).mono fun y hy => (htw.trans hy.1 : (0 : ℝ) ≤ y))
    (fun y hy => hold_deriv hx htw hH hs hy.1)
    continuousOn_const
    (fun y _ => by beta_reduce; rw [h0]; exact hasDerivWithinAt_const _ _ _)
    hxs
  exact this ⟨ht, le_rfl⟩

/-- Near the equilibrium the node escapes no faster than `exp(K t)`
(Groenwall with the global gain bound `K = (L+1)/tau`). -/
theorem stays_near (hx : IsSolFamily m S v0 x) {sA sB tw vs : ℝ} (htw : 0 ≤ tw)
    (hH : HoldInputs S sA sB tw) (heq : m.F 1 1 vs = vs) {s : ℝ} (hs : s ∈ Icc sA sB)
    {t : ℝ} (ht : tw ≤ t) :
    |x s t - vs| ≤ |x s tw - vs| * exp (m.K * (t - tw)) := by
  have h0 : m.field 1 1 vs = 0 := by simp [Loop.field, heq]
  have := dist_le_of_trajectories_ODE (v := fun _ => m.field 1 1) (K := m.K)
    (f := x s) (g := fun _ => vs) (a := tw) (b := t) (δ := |x s tw - vs|)
    (fun _ => m.field_lipschitz 1 1)
    ((hx.cont s).mono fun y hy => (htw.trans hy.1 : (0 : ℝ) ≤ y))
    (fun y hy => hold_deriv hx htw hH hs hy.1)
    continuousOn_const
    (fun y _ => by beta_reduce; rw [h0]; exact hasDerivWithinAt_const _ _ _)
    (le_of_eq (Real.dist_eq _ _))
    t ⟨ht, le_rfl⟩
  rwa [Real.dist_eq] at this

/-- **Aperture lower bound (the e^(-t/tau) law, lower half).** With `s*` from
`metastable_forever`, every timing `s` in the sweep satisfies
`|q_s(t) - vs| ≤ C(tw) * |s - s*| * exp(K (t - tw))`. So at resolution time
`t`, all timings within `δ / (C(tw) exp(K (t - tw)))` of `s*` are still within
`δ` of the metastable point: the bad-timing window shrinks at most
exponentially, never faster. -/
theorem aperture_lower_bound (hx : IsSolFamily m S v0 x) {sA sB tw vs sstar : ℝ}
    (htw : 0 ≤ tw) (hH : HoldInputs S sA sB tw) (heq : m.F 1 1 vs = vs)
    (hstar : x sstar tw = vs) {s : ℝ} (hs : s ∈ Icc sA sB) {t : ℝ} (ht : tw ≤ t) :
    |x s t - vs|
      ≤ 2 * m.L * S.M / m.tau * gronwallBound 0 m.K 1 tw * |s - sstar|
          * exp (m.K * (t - tw)) := by
  refine (stays_near hx htw hH heq hs ht).trans ?_
  gcongr
  rw [← hstar]
  exact sol_dist_le hx s sstar tw htw

end Hold

end Formal.Cells.ArbAnalog
