import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Trace benchmark, representation (a): continuous time, `ℝ → Bool`

Track 2 probe. A signal is a function `ℝ → Bool`. Well-formedness (`WF`) is
local: at every time `t` the signal is constant on some `[t, t+ε)` (right
continuity) and constant on some `(t-ε, t)` (a left limit exists). By
compactness this is equivalent to "finitely many transitions in every bounded
window" (non-Zeno); we state the local form because it is what the proofs use.

Benchmark items proved here: B0-B5. B4 (inertial delay) uses the
completeness of ℝ, taken as the explicit hypothesis `RealComplete` until the
Mathlib module proving it (`Real.exists_isGLB`) is built here.
-/

namespace Formal.Core.TraceReal

/-! ## B0: values, signals, well-formedness -/

/-- Binary values. -/
abbrev Val := Bool

/-- A signal: a value at every real time. -/
abbrev Sig := ℝ → Val

/-- Well-formedness: right-continuous and locally finitely variable. At each
`t` the signal is constant on `[t, t+ε)` and constant on `(t-ε, t)`. -/
def WF (s : Sig) : Prop :=
  ∀ t : ℝ, ∃ ε > 0, (∀ u, t ≤ u → u < t + ε → s u = s t) ∧
    (∀ u v, t - ε < u → u < t → t - ε < v → v < t → s u = s v)

/-- The signal is constant up to time `T` (its initial value is `s T`). -/
def ConstBefore (T : ℝ) (s : Sig) : Prop := ∀ t ≤ T, s t = s T

/-- `s` has a transition at `t`: just before `t` it differs from `s t`. -/
def Trans (s : Sig) (t : ℝ) : Prop :=
  ∃ ε > 0, ∀ u, t - ε < u → u < t → s u ≠ s t

theorem wf_const (b : Val) : WF (fun _ => b) :=
  fun _ => ⟨1, one_pos, fun _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

/-! ## B1: fixed pure delay -/

/-- Pure delay by `d`: `out t = in (t - d)`. -/
def delay (d : ℝ) (x : Sig) : Sig := fun t => x (t - d)

theorem delay_delay (d₁ d₂ : ℝ) (x : Sig) :
    delay d₂ (delay d₁ x) = delay (d₁ + d₂) x := by
  funext t
  simp only [delay]
  congr 1
  linarith

theorem delay_zero (x : Sig) : delay 0 x = x := by
  funext t; simp [delay]

theorem delay_wf (d : ℝ) {x : Sig} (hx : WF x) : WF (delay d x) := by
  intro t
  obtain ⟨ε, hε, h1, h2⟩ := hx (t - d)
  refine ⟨ε, hε, ?_, ?_⟩
  · intro u hu1 hu2
    exact h1 (u - d) (by linarith) (by linarith)
  · intro u v hu1 hu2 hv1 hv2
    exact h2 (u - d) (v - d) (by linarith) (by linarith) (by linarith) (by linarith)

theorem delay_trans_iff (d : ℝ) (x : Sig) (t : ℝ) :
    Trans (delay d x) (t + d) ↔ Trans x t := by
  constructor
  · rintro ⟨ε, hε, h⟩
    refine ⟨ε, hε, fun u hu1 hu2 => ?_⟩
    have := h (u + d) (by linarith) (by linarith)
    simpa [delay] using this
  · rintro ⟨ε, hε, h⟩
    refine ⟨ε, hε, fun u hu1 hu2 => ?_⟩
    have := h (u - d) (by linarith) (by linarith)
    simpa [delay] using this

/-! ## B2: bounded transport delay as a relation

The channel relation is phrased through a *time warp* `θ`: a strictly
increasing bijection `ℝ → ℝ` that moves every instant forward by an amount in
`[lo, hi]`, with `out (θ t) = in t`. A transition of the input at `t` appears
at the output at `θ t` (delay in `[lo,hi]`), order is preserved (`θ` is
strictly monotone) and there are no other output transitions (`θ` is onto).
`tchan_trans_iff` and `tchan_trans_out` prove these three readings. -/

/-- An admissible warp for a `[lo, hi]` transport channel. -/
structure Warp (lo hi : ℝ) (θ : ℝ → ℝ) : Prop where
  mono : StrictMono θ
  surj : Function.Surjective θ
  lo_le : ∀ t, lo ≤ θ t - t
  le_hi : ∀ t, θ t - t ≤ hi

/-- Bounded transport (pure) delay channel, order preserving. -/
def TChan (lo hi : ℝ) (x y : Sig) : Prop :=
  ∃ θ, Warp lo hi θ ∧ ∀ t, y (θ t) = x t

theorem Warp.comp {lo₁ hi₁ lo₂ hi₂ : ℝ} {θ₁ θ₂ : ℝ → ℝ}
    (h₁ : Warp lo₁ hi₁ θ₁) (h₂ : Warp lo₂ hi₂ θ₂) :
    Warp (lo₁ + lo₂) (hi₁ + hi₂) (θ₂ ∘ θ₁) where
  mono := h₂.mono.comp h₁.mono
  surj := h₂.surj.comp h₁.surj
  lo_le t := by
    have := h₁.lo_le t; have := h₂.lo_le (θ₁ t)
    simp only [Function.comp]; linarith
  le_hi t := by
    have := h₁.le_hi t; have := h₂.le_hi (θ₁ t)
    simp only [Function.comp]; linarith

/-- B2 composition: `[lo₁,hi₁]` then `[lo₂,hi₂]` is contained in
`[lo₁+lo₂, hi₁+hi₂]`. -/
theorem tchan_comp {lo₁ hi₁ lo₂ hi₂ : ℝ} {x y z : Sig}
    (hxy : TChan lo₁ hi₁ x y) (hyz : TChan lo₂ hi₂ y z) :
    TChan (lo₁ + lo₂) (hi₁ + hi₂) x z := by
  obtain ⟨θ₁, h₁, e₁⟩ := hxy
  obtain ⟨θ₂, h₂, e₂⟩ := hyz
  exact ⟨θ₂ ∘ θ₁, h₁.comp h₂, fun t => by simp [Function.comp, e₂, e₁]⟩

/-- B2 monotonicity. -/
theorem tchan_mono {lo hi lo' hi' : ℝ} {x y : Sig} (hlo : lo' ≤ lo) (hhi : hi ≤ hi')
    (h : TChan lo hi x y) : TChan lo' hi' x y := by
  obtain ⟨θ, hθ, e⟩ := h
  refine ⟨θ, ⟨hθ.mono, hθ.surj, fun t => ?_, fun t => ?_⟩, e⟩
  · have := hθ.lo_le t; linarith
  · have := hθ.le_hi t; linarith

/-- A fixed delay is a transport channel. -/
theorem delay_tchan {lo hi d : ℝ} (h1 : lo ≤ d) (h2 : d ≤ hi) (x : Sig) :
    TChan lo hi x (delay d x) := by
  refine ⟨fun t => t + d, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro a b hab; show a + d < b + d; linarith
  · intro v; exact ⟨v - d, show v - d + d = v by linarith⟩
  · intro t; show lo ≤ t + d - t; linarith
  · intro t; show t + d - t ≤ hi; linarith
  · intro t; show x (t + d - d) = x t; congr 1; linarith

/-- Input transitions are exactly mapped to output transitions by the warp. -/
theorem tchan_trans_iff {lo hi : ℝ} {θ : ℝ → ℝ} {x y : Sig} (hθ : Warp lo hi θ)
    (e : ∀ t, y (θ t) = x t) (t : ℝ) : Trans y (θ t) ↔ Trans x t := by
  constructor
  · rintro ⟨δ, hδ, h⟩
    obtain ⟨u₀, hu₀⟩ := hθ.surj (θ t - δ)
    have hlt : u₀ < t := hθ.mono.lt_iff_lt.mp (by linarith)
    refine ⟨t - u₀, by linarith, fun u hu1 hu2 => ?_⟩
    have a1 : θ u₀ < θ u := hθ.mono (by linarith)
    have a2 : θ u < θ t := hθ.mono hu2
    have := h (θ u) (by linarith) a2
    rwa [e, e] at this
  · rintro ⟨ε, hε, h⟩
    have hlt : θ (t - ε) < θ t := hθ.mono (by linarith)
    refine ⟨θ t - θ (t - ε), by linarith, fun v hv1 hv2 => ?_⟩
    obtain ⟨u, rfl⟩ := hθ.surj v
    have b1 : t - ε < u := hθ.mono.lt_iff_lt.mp (by linarith)
    have b2 : u < t := hθ.mono.lt_iff_lt.mp hv2
    rw [e, e]
    exact h u b1 b2

/-- No other output transitions: every output transition comes from an input
transition, with delay in `[lo, hi]`. -/
theorem tchan_trans_out {lo hi : ℝ} {x y : Sig} (h : TChan lo hi x y) {v : ℝ}
    (hv : Trans y v) : ∃ t, Trans x t ∧ lo ≤ v - t ∧ v - t ≤ hi := by
  obtain ⟨θ, hθ, e⟩ := h
  obtain ⟨t, rfl⟩ := hθ.surj v
  exact ⟨t, (tchan_trans_iff hθ e t).mp hv, hθ.lo_le t, hθ.le_hi t⟩

/-- Every input transition appears at the output with delay in `[lo, hi]`,
and order between transitions is preserved. -/
theorem tchan_trans_in {lo hi : ℝ} {θ : ℝ → ℝ} {x y : Sig} (hθ : Warp lo hi θ)
    (e : ∀ t, y (θ t) = x t) {t₁ t₂ : ℝ} (h₁ : Trans x t₁) (h₂ : Trans x t₂) :
    Trans y (θ t₁) ∧ Trans y (θ t₂) ∧ lo ≤ θ t₁ - t₁ ∧ θ t₁ - t₁ ≤ hi ∧
      (t₁ < t₂ ↔ θ t₁ < θ t₂) :=
  ⟨(tchan_trans_iff hθ e t₁).mpr h₁, (tchan_trans_iff hθ e t₂).mpr h₂,
    hθ.lo_le t₁, hθ.le_hi t₁, hθ.mono.lt_iff_lt.symm⟩

/-- The output of a transport channel is well formed when the input is. -/
theorem tchan_wf {lo hi : ℝ} {x y : Sig} (hx : WF x) (h : TChan lo hi x y) : WF y := by
  obtain ⟨θ, hθ, e⟩ := h
  intro v
  obtain ⟨t, rfl⟩ := hθ.surj v
  obtain ⟨ε, hε, h1, h2⟩ := hx t
  have p1 : θ t < θ (t + ε) := hθ.mono (by linarith)
  have p2 : θ (t - ε) < θ t := hθ.mono (by linarith)
  refine ⟨min (θ (t + ε) - θ t) (θ t - θ (t - ε)), lt_min (by linarith) (by linarith),
    ?_, ?_⟩
  · intro u hu1 hu2
    obtain ⟨w, rfl⟩ := hθ.surj u
    have m := min_le_left (θ (t + ε) - θ t) (θ t - θ (t - ε))
    have c1 : t ≤ w := hθ.mono.le_iff_le.mp hu1
    have c2 : w < t + ε := hθ.mono.lt_iff_lt.mp (by linarith)
    rw [e, e]; exact h1 w c1 c2
  · intro u u' hu1 hu2 hu1' hu2'
    obtain ⟨w, rfl⟩ := hθ.surj u
    obtain ⟨w', rfl⟩ := hθ.surj u'
    have m := min_le_right (θ (t + ε) - θ t) (θ t - θ (t - ε))
    have c1 : t - ε < w := hθ.mono.lt_iff_lt.mp (by linarith)
    have c2 : w < t := hθ.mono.lt_iff_lt.mp hu2
    have c1' : t - ε < w' := hθ.mono.lt_iff_lt.mp (by linarith)
    have c2' : w' < t := hθ.mono.lt_iff_lt.mp hu2'
    rw [e, e]; exact h2 w w' c1 c2 c1' c2'

/-! ## B2': the sampling-window channel (sound over-approximation)

`Window lo hi x y`: the output at `t` equals the input at *some* instant in
`[t-hi, t-lo]`. Strictly more permissive than `TChan` (`tchan_window`): it
admits loss of short pulses (`window_pulse_lost`) and glitches. -/

def Window (lo hi : ℝ) (x y : Sig) : Prop :=
  ∀ t, ∃ s, t - hi ≤ s ∧ s ≤ t - lo ∧ y t = x s

theorem tchan_window {lo hi : ℝ} {x y : Sig} (h : TChan lo hi x y) : Window lo hi x y := by
  obtain ⟨θ, hθ, e⟩ := h
  intro v
  obtain ⟨u, rfl⟩ := hθ.surj v
  exact ⟨u, by linarith [hθ.le_hi u], by linarith [hθ.lo_le u], e u⟩

theorem window_comp {lo₁ hi₁ lo₂ hi₂ : ℝ} {x y z : Sig}
    (hxy : Window lo₁ hi₁ x y) (hyz : Window lo₂ hi₂ y z) :
    Window (lo₁ + lo₂) (hi₁ + hi₂) x z := by
  intro t
  obtain ⟨s, hs1, hs2, hs⟩ := hyz t
  obtain ⟨r, hr1, hr2, hr⟩ := hxy s
  exact ⟨r, by linarith, by linarith, hs.trans hr⟩

theorem window_mono {lo hi lo' hi' : ℝ} {x y : Sig} (hlo : lo' ≤ lo) (hhi : hi ≤ hi')
    (h : Window lo hi x y) : Window lo' hi' x y := by
  intro t
  obtain ⟨s, h1, h2, h3⟩ := h t
  exact ⟨s, by linarith, by linarith, h3⟩

/-- If the input is constant on the whole window `[t-hi, t-lo]`, the output at
`t` has that value. -/
theorem window_stable {lo hi : ℝ} {x y : Sig} (h : Window lo hi x y) {t : ℝ} {b : Val}
    (hx : ∀ s, t - hi ≤ s → s ≤ t - lo → x s = b) : y t = b := by
  obtain ⟨s, h1, h2, h3⟩ := h t
  rw [h3]; exact hx s h1 h2

/-! ## B3: pulses -/

/-- A positive pulse starting at `a` of width `w` (half-open `[a, a+w)`). -/
noncomputable def pulse (a w : ℝ) : Sig := fun t => decide (a ≤ t ∧ t < a + w)

theorem pulse_in {a w t : ℝ} (h1 : a ≤ t) (h2 : t < a + w) : pulse a w t = true := by
  simp [pulse, h1, h2]

theorem pulse_out {a w t : ℝ} (h : t < a ∨ a + w ≤ t) : pulse a w t = false := by
  simp only [pulse, decide_eq_false_iff_not, not_and, not_lt]
  intro h1; rcases h with h | h
  · exact absurd h1 (not_le.mpr h)
  · exact h

theorem pulse_true {a w t : ℝ} (h : pulse a w t = true) : a ≤ t ∧ t < a + w := by
  simpa [pulse] using h

theorem pulse_false {a w t : ℝ} (h : pulse a w t = false) : t < a ∨ a + w ≤ t := by
  by_contra hc
  push Not at hc
  rw [pulse_in hc.1 hc.2] at h
  exact Bool.noConfusion h

/-- Pulse value on a region: true inside, false outside. -/
theorem pulse_const_in {a w : ℝ} {u v : ℝ} (hu : a ≤ u ∧ u < a + w) (hv : a ≤ v ∧ v < a + w) :
    pulse a w u = pulse a w v := by rw [pulse_in hu.1 hu.2, pulse_in hv.1 hv.2]

theorem pulse_const_out {a w : ℝ} {u v : ℝ} (hu : u < a ∨ a + w ≤ u) (hv : v < a ∨ a + w ≤ v) :
    pulse a w u = pulse a w v := by rw [pulse_out hu, pulse_out hv]

theorem pulse_wf (a w : ℝ) (hw : 0 < w) : WF (pulse a w) := by
  intro t
  rcases lt_or_ge t a with h | h
  · refine ⟨a - t, by linarith, ?_, ?_⟩
    · intro u _ hu2
      exact pulse_const_out (Or.inl (by linarith)) (Or.inl h)
    · intro u v _ hu2 _ hv2
      exact pulse_const_out (Or.inl (by linarith)) (Or.inl (by linarith))
  · rcases lt_or_ge t (a + w) with h' | h'
    · rcases eq_or_lt_of_le h with h0 | h0
      · subst h0
        refine ⟨w, hw, ?_, ?_⟩
        · intro u hu1 hu2
          exact pulse_const_in ⟨hu1, by linarith⟩ ⟨le_refl _, h'⟩
        · intro u v _ hu2 _ hv2
          exact pulse_const_out (Or.inl hu2) (Or.inl hv2)
      · have m1 := min_le_left (t - a) (a + w - t)
        have m2 := min_le_right (t - a) (a + w - t)
        refine ⟨min (t - a) (a + w - t), lt_min (by linarith) (by linarith), ?_, ?_⟩
        · intro u hu1 hu2
          exact pulse_const_in ⟨by linarith, by linarith⟩ ⟨h, h'⟩
        · intro u v hu1 hu2 hv1 hv2
          exact pulse_const_in ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    · rcases eq_or_lt_of_le h' with h0 | h0
      · refine ⟨w, hw, ?_, ?_⟩
        · intro u hu1 _
          exact pulse_const_out (Or.inr (by linarith)) (Or.inr h')
        · intro u v hu1 hu2 hv1 hv2
          exact pulse_const_in ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
      · refine ⟨t - (a + w), by linarith, ?_, ?_⟩
        · intro u hu1 _
          exact pulse_const_out (Or.inr (by linarith)) (Or.inr h')
        · intro u v hu1 _ hv1 _
          exact pulse_const_out (Or.inr (by linarith)) (Or.inr (by linarith))

/-- B3, transport channel: a pulse of width `w` comes out as a single pulse
`[θ a, θ (a+w))` whose width lies in `[w-(hi-lo), w+(hi-lo)]` and is strictly
positive: the order-preserving channel never loses or inverts a pulse. -/
theorem tchan_pulse {lo hi a w : ℝ} {θ : ℝ → ℝ} {y : Sig} (hθ : Warp lo hi θ)
    (e : ∀ t, y (θ t) = pulse a w t) :
    y = pulse (θ a) (θ (a + w) - θ a) ∧
      w - (hi - lo) ≤ θ (a + w) - θ a ∧ θ (a + w) - θ a ≤ w + (hi - lo) := by
  refine ⟨?_, ?_, ?_⟩
  · funext v
    obtain ⟨u, rfl⟩ := hθ.surj v
    rw [e]
    simp only [pulse, add_sub_cancel, hθ.mono.le_iff_le, hθ.mono.lt_iff_lt]
  · linarith [hθ.lo_le (a + w), hθ.le_hi a]
  · linarith [hθ.le_hi (a + w), hθ.lo_le a]

theorem tchan_pulse_width_pos {lo hi a w : ℝ} {θ : ℝ → ℝ} (hθ : Warp lo hi θ)
    (hw : 0 < w) : 0 < θ (a + w) - θ a := by
  have := hθ.mono (show a < a + w by linarith); linarith

/-- B3, transport channel: a positive pulse is never lost. -/
theorem tchan_pulse_not_lost {lo hi a w : ℝ} {y : Sig} (hw : 0 < w)
    (h : TChan lo hi (pulse a w) y) : ∃ t, y t = true := by
  obtain ⟨θ, _, e⟩ := h
  exact ⟨θ a, by rw [e]; exact pulse_in (le_refl a) (by linarith)⟩

/-- B3, window channel: if `0 ≤ w ≤ hi - lo` the pulse may be lost entirely
(the constant-0 output is an admitted behaviour). -/
theorem window_pulse_lost {lo hi a w : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ hi - lo) :
    Window lo hi (pulse a w) (fun _ => false) := by
  intro t
  rcases lt_or_ge (t - hi) a with h | h
  · exact ⟨t - hi, le_refl _, by linarith, (pulse_out (Or.inl h)).symm⟩
  · exact ⟨t - lo, by linarith, le_refl _, (pulse_out (Or.inr (by linarith))).symm⟩

/-- ... and if `w ≤ hi - lo` is violated the window channel cannot lose it:
some output instant sees only the pulse. -/
theorem window_pulse_kept {lo hi a w : ℝ} {y : Sig} (hw : hi - lo < w)
    (h : Window lo hi (pulse a w) y) : y (a + hi) = true := by
  apply window_stable h
  intro s h1 h2
  exact pulse_in (by linarith) (by linarith)

/-! ## B4: inertial delay

Arguments of the form "the first time the output changes" need the
completeness of ℝ. Mathlib proves it (`Real.exists_isGLB`) in
`Mathlib.Algebra.Order.Archimedean.Real.Basic`, which is not built in this
sandbox yet, so here it is an explicit hypothesis `RealComplete`. It is a
theorem of mathematics, not a modelling assumption; `Wip/TraceReal.lean`
discharges it once that module is available. -/

/-- Completeness of ℝ, in GLB form (a Mathlib theorem; see above). -/
def RealComplete : Prop :=
  ∀ S : Set ℝ, S.Nonempty → BddBelow S → ∃ g, IsGLB S g

/-- First change: a right-continuous signal that has value `b` at `v₀` and not
`b` at `t > v₀` has a transition at some `s ∈ (v₀, t]` with `y s ≠ b`.
This is the induction-over-time principle for continuous traces; it needs the
completeness of ℝ. -/
theorem first_change (hc : RealComplete) {y : Sig} (hy : WF y) {v₀ t : ℝ} {b : Val} (hv : v₀ ≤ t)
    (h0 : y v₀ = b) (ht : y t ≠ b) :
    ∃ s, v₀ < s ∧ s ≤ t ∧ y s ≠ b ∧ Trans y s := by
  let S : Set ℝ := {u | v₀ ≤ u ∧ u ≤ t ∧ y u ≠ b}
  have hne : S.Nonempty := ⟨t, hv, le_refl t, ht⟩
  have hbdd : BddBelow S := ⟨v₀, fun u hu => hu.1⟩
  obtain ⟨g, hg⟩ := hc S hne hbdd
  have hgt : g ≤ t := hg.1 ⟨hv, le_refl t, ht⟩
  have hv0g : v₀ ≤ g := hg.2 (fun u hu => hu.1)
  -- below g (and from v₀) the signal is b
  have below : ∀ u, v₀ ≤ u → u < g → y u = b := by
    intro u hu1 hu2
    by_contra hne'
    have := hg.1 ⟨hu1, by linarith, hne'⟩
    linarith
  have hgb : y g ≠ b := by
    intro hgb
    obtain ⟨ε, hε, h1, _⟩ := hy g
    have : g + ε ≤ g := by
      apply hg.2
      intro u hu
      by_contra hlt
      push Not at hlt
      have hgu : g ≤ u := hg.1 hu
      exact hu.2.2 ((h1 u hgu hlt).trans hgb)
    linarith
  have hv0lt : v₀ < g := by
    rcases eq_or_lt_of_le hv0g with h | h
    · exact absurd (h ▸ h0) hgb
    · exact h
  refine ⟨g, hv0lt, hgt, hgb, g - v₀, by linarith, fun u hu1 hu2 => ?_⟩
  rw [below u (by linarith) hu2]
  exact fun h => hgb h.symm

/-- Inertial delay `δ` as a relation. (1) if the input has been constant on
`[t-δ, t]` the output at `t` equals it; (2) the output only has a transition
at `t` when the input has been constant on `[t-δ, t]`. -/
def Inertial (δ : ℝ) (x y : Sig) : Prop :=
  (∀ t, (∀ u, t - δ ≤ u → u ≤ t → x u = x t) → y t = x t) ∧
  (∀ t, Trans y t → ∀ u, t - δ ≤ u → u ≤ t → x u = x t)

/-- B4 (short pulses): a pulse of width `w ≤ δ` produces no output at all. -/
theorem inertial_short (hc : RealComplete) {δ a w : ℝ} {y : Sig} (hδ : 0 ≤ δ)
    (hw : w ≤ δ) (hy : WF y) (h : Inertial δ (pulse a w) y) : ∀ t, y t = false := by
  intro t
  by_contra ht
  have m := min_le_right t a
  have v0 : y (min t a - 1) = false := by
    apply (h.1 _ _).trans
    · exact pulse_out (Or.inl (by linarith))
    · intro u _ hu2
      exact pulse_const_out (Or.inl (by linarith)) (Or.inl (by linarith))
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ :=
    first_change hc hy (by linarith [min_le_left t a]) v0 ht
  have stab := h.2 s hs4
  have ys := h.1 s stab
  have xs : pulse a w s = true := by rw [← ys]; simpa using hs3
  have xsd : pulse a w (s - δ) = true := (stab (s - δ) (le_refl _) (by linarith)).trans xs
  have := pulse_true xs
  have := pulse_true xsd
  linarith

/-- B4 (long pulses): a pulse of width `w > δ` is propagated, delayed by `δ`. -/
theorem inertial_long (hc : RealComplete) {δ a w : ℝ} {y : Sig} (hδ : 0 ≤ δ)
    (hw : δ < w) (hy : WF y) (h : Inertial δ (pulse a w) y) : y = pulse (a + δ) w := by
  have r2 : ∀ t, a + δ ≤ t → t < a + w → y t = true := by
    intro t h1 h2
    rw [h.1 t (fun u hu1 hu2 =>
      pulse_const_in ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩)]
    exact pulse_in (by linarith) h2
  have r4 : ∀ t, a + w + δ ≤ t → y t = false := by
    intro t h1
    rw [h.1 t (fun u hu1 hu2 =>
      pulse_const_out (Or.inr (by linarith)) (Or.inr (by linarith)))]
    exact pulse_out (Or.inr (by linarith))
  have r1 : ∀ t, t < a + δ → y t = false := by
    intro t h1
    by_contra ht
    have m := min_le_right t a
    have v0 : y (min t a - 1) = false := by
      apply (h.1 _ _).trans
      · exact pulse_out (Or.inl (by linarith))
      · intro u _ hu2
        exact pulse_const_out (Or.inl (by linarith)) (Or.inl (by linarith))
    obtain ⟨s, hs1, hs2, hs3, hs4⟩ :=
      first_change hc hy (by linarith [min_le_left t a]) v0 ht
    have stab := h.2 s hs4
    have ys := h.1 s stab
    have xs : pulse a w s = true := by rw [← ys]; simpa using hs3
    have xsd : pulse a w (s - δ) = true :=
      (stab (s - δ) (le_refl _) (by linarith)).trans xs
    have := pulse_true xsd
    linarith
  have r3 : ∀ t, a + w ≤ t → t < a + w + δ → y t = true := by
    intro t h1 h2
    by_contra ht
    have v0 : y (a + δ) = true := r2 _ (le_refl _) (by linarith)
    obtain ⟨s, hs1, hs2, hs3, hs4⟩ := first_change hc hy (by linarith) v0 ht
    have stab := h.2 s hs4
    have ys := h.1 s stab
    have xs : pulse a w s = false := by rw [← ys]; simpa using hs3
    have xsd : pulse a w (s - δ) = false :=
      (stab (s - δ) (le_refl _) (by linarith)).trans xs
    rcases pulse_false xsd with c | c <;> linarith
  funext t
  by_cases c1 : t < a + δ
  · rw [r1 t c1]; exact (pulse_out (Or.inl c1)).symm
  by_cases c2 : t < a + w
  · rw [r2 t (by linarith) c2]; exact (pulse_in (by linarith) (by linarith)).symm
  by_cases c3 : t < a + w + δ
  · rw [r3 t (by linarith) c3]; exact (pulse_in (by linarith) (by linarith)).symm
  · rw [r4 t (by linarith)]; exact (pulse_out (Or.inr (by linarith))).symm

/-! ## B5: a 2-input gate and a circuit -/

/-- A 2-input gate: Boolean function `f` of the inputs, through channel `ch`. -/
def Gate2 (ch : Sig → Sig → Prop) (f : Val → Val → Val) (a b y : Sig) : Prop :=
  ch (fun t => f (a t) (b t)) y

/-- With `b` held at 1, AND(a,b) through a `[lo,hi]` transport channel follows
`a` within `[lo,hi]`. -/
theorem and_follows {lo hi : ℝ} {a b y : Sig} (hb : ∀ t, b t = true)
    (h : Gate2 (TChan lo hi) (· && ·) a b y) : TChan lo hi a y := by
  have : (fun t => a t && b t) = a := by funext t; simp [hb]
  unfold Gate2 at h; rwa [this] at h

theorem and_follows_window {lo hi : ℝ} {a b y : Sig} (hb : ∀ t, b t = true)
    (h : Gate2 (Window lo hi) (· && ·) a b y) : Window lo hi a y := by
  have : (fun t => a t && b t) = a := by funext t; simp [hb]
  unfold Gate2 at h; rwa [this] at h

/-- Local version (window channel): if `b` is 1 and `a` is `v` on the whole
window `[t-hi, t-lo]`, then the output at `t` is `v`. -/
theorem and_window_local {lo hi t : ℝ} {a b y : Sig} {v : Val}
    (h : Gate2 (Window lo hi) (· && ·) a b y)
    (hb : ∀ s, t - hi ≤ s → s ≤ t - lo → b s = true)
    (ha : ∀ s, t - hi ≤ s → s ≤ t - lo → a s = v) : y t = v :=
  window_stable h fun s h1 h2 => by simp [hb s h1 h2, ha s h1 h2]

/-- A circuit is the conjunction of its gate relations: two ANDs in series. -/
def AndChain (lo₁ hi₁ lo₂ hi₂ : ℝ) (a b c m y : Sig) : Prop :=
  Gate2 (TChan lo₁ hi₁) (· && ·) a b m ∧ Gate2 (TChan lo₂ hi₂) (· && ·) m c y

theorem andChain_follows {lo₁ hi₁ lo₂ hi₂ : ℝ} {a b c m y : Sig}
    (hb : ∀ t, b t = true) (hc : ∀ t, c t = true)
    (h : AndChain lo₁ hi₁ lo₂ hi₂ a b c m y) : TChan (lo₁ + lo₂) (hi₁ + hi₂) a y :=
  tchan_comp (and_follows hb h.1) (and_follows hc h.2)

/-! ## Discharging `RealComplete`
Mathlib's `Real.exists_isGLB` proves the completeness hypothesis, so the
inertial results hold unconditionally. -/

theorem realComplete : RealComplete := fun _ hne hbdd => Real.exists_isGLB hne hbdd

theorem inertial_short' {δ a w : ℝ} {y : Sig} (hδ : 0 ≤ δ) (hw : w ≤ δ) (hy : WF y)
    (h : Inertial δ (pulse a w) y) : ∀ t, y t = false :=
  inertial_short realComplete hδ hw hy h

theorem inertial_long' {δ a w : ℝ} {y : Sig} (hδ : 0 ≤ δ) (hw : δ < w) (hy : WF y)
    (h : Inertial δ (pulse a w) y) : y = pulse (a + δ) w :=
  inertial_long realComplete hδ hw hy h

end Formal.Core.TraceReal
