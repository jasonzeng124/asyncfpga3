import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# WIP (NOT PROVED, never built): delay-channel hypotheses per primitive

Work in progress for `formal/notes/A-fidelity.md`. Every `sorry` below is
an open obligation, not a claim. The file is self-contained: the proved
`Formal.Core.Fidelity` has no .olean yet, and building one is the lead's
job, so delay bounds appear here as bare `lo hi : ℝ`.

The channel shapes (bounded transport, a pulse-filter envelope, and
involution) are stated as `Prop`s so that a circuit theorem can take one
per primitive as a named hypothesis.
-/

namespace Formal.Wip.Fidelity

/-- A binary signal: a trace over real time. -/
abbrev Sig := ℝ → Bool

/-- **Bounded transport with order-preserving warp.** `y` is `x` delayed by
a per-instant delay `δ t ∈ [lo, hi]`, and the warp `t ↦ t + δ t` is
strictly monotone. Every input pulse, however short, appears at the
output: none is created and none is dropped. This is the hypothesis for a
buffered routing hop and for any CMOS arc whose relevant pulses are far
wider than its rejection window (see the notes). -/
def BoundedTransport (lo hi : ℝ) (x y : Sig) : Prop :=
  ∃ δ : ℝ → ℝ, (∀ t, lo ≤ δ t ∧ δ t ≤ hi) ∧
    (∀ t, y (t + δ t) = x t) ∧
    (∀ s t, s < t → s + δ s < t + δ t) ∧
    (∀ u, ∃ t, u = t + δ t)   -- the warp is onto, so `y` has no edges of its own

/-- A pulse of `x`: `x` is constant `v` on `[a, b)` and differs just before
`a` and at `b`. -/
def Pulse (x : Sig) (v : Bool) (a b : ℝ) : Prop :=
  a < b ∧ (∀ t, a ≤ t → t < b → x t = v) ∧ x b = !v ∧
    ∃ ε > 0, ∀ t, a - ε < t → t < a → x t = !v

/-- **Pulse-filter envelope** (the inertial-ish behaviour of a restoring
stage behind an RC load). A pulse of width at least `wpass` passes, with
its width changed by at most `dw`. A pulse narrower than `wkill` may vanish.
In between, anything may happen, including a runt that the next stage
sees as X. Only the passing half is stated here. The other half is a
permission, not an obligation. -/
def PassesWide (wpass dw : ℝ) (lo hi : ℝ) (x y : Sig) : Prop :=
  ∀ v a b, Pulse x v a b → wpass ≤ b - a →
    ∃ a' b', Pulse y v a' b' ∧ lo ≤ a' - a ∧ a' - a ≤ hi ∧
      |(b' - a') - (b - a)| ≤ dw

/-- **Involution channel** (Függer, Najvirt, Nowak, Schmid): the delay of
an edge depends on `T`, the time since the previous output edge. The delay
functions `δup`, `δdn` satisfy `-δup (-δdn T) = T`. Only the defining
property is recorded here. The trace semantics (edge cancellation) is
future work. -/
structure Involution where
  δup : ℝ → ℝ
  δdn : ℝ → ℝ
  inv1 : ∀ T, -δup (-δdn T) = T
  inv2 : ∀ T, -δdn (-δup T) = T
  mono_up : ∀ s t, s ≤ t → δup s ≤ δup t
  mono_dn : ∀ s t, s ≤ t → δdn s ≤ δdn t

/-! ## Open obligations -/

/-- Series composition of bounded-transport channels. Proved; the same
statement over `DelayBound` is `Formal.Core.Fidelity.boundedTransport_series`. -/
theorem boundedTransport_comp (lo₁ hi₁ lo₂ hi₂ : ℝ) (x y z : Sig)
    (h₁ : BoundedTransport lo₁ hi₁ x y) (h₂ : BoundedTransport lo₂ hi₂ y z) :
    BoundedTransport (lo₁ + lo₂) (hi₁ + hi₂) x z := by
  obtain ⟨δ₁, hb₁, hy₁, hm₁, ho₁⟩ := h₁
  obtain ⟨δ₂, hb₂, hy₂, hm₂, ho₂⟩ := h₂
  refine ⟨fun t => δ₁ t + δ₂ (t + δ₁ t), ?_, ?_, ?_, ?_⟩
  · intro t
    have := hb₁ t; have := hb₂ (t + δ₁ t)
    constructor <;> linarith
  · intro t
    have e := hy₂ (t + δ₁ t)
    rw [hy₁ t] at e
    rw [← add_assoc]; exact e
  · intro s t hst
    have h1 := hm₁ s t hst
    have h2 := hm₂ _ _ h1
    linarith
  · intro u
    obtain ⟨s, hs⟩ := ho₂ u
    obtain ⟨t, ht⟩ := ho₁ s
    refine ⟨t, ?_⟩
    rw [hs, ht, add_assoc]

/-- A bounded-transport channel passes every pulse, with its width changed
by at most `hi - lo`. Open: this needs the warp to be continuous at the
pulse ends, which `BoundedTransport` does not yet require. -/
theorem boundedTransport_passes (lo hi : ℝ) (x y : Sig)
    (h : BoundedTransport lo hi x y) :
    PassesWide 0 (hi - lo) lo hi x y := by
  sorry

/-- RC claim, stated informally (it needs `Real.exp` and an RC-tree ODE,
which are not in the built Mathlib subset). For a single pole, the
step response is `1 - exp(-t/τ)`, which is monotone, so a clean edge stays
glitch-free. A rectangular pulse of width `w` peaks at `1 - exp(-w/τ)`, which
falls below the receiver's threshold `θ` iff `w < τ · ln(1/(1-θ))`. That
gives `wkill ≈ 0.69 τ` for `θ = 1/2`. Placeholder only. -/
theorem rc_single_pole_rejects_runt : True := trivial

end Formal.Wip.Fidelity
