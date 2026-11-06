import Formal.Target.Spec

/-!
# Formal.Target.SpecSkip — how wide a pulse the gate relation can swallow

Shard A, 2026-11-06. Spec.lean's prose says "a read time that jumps swallows a pulse (inertial behaviour)". **Plainly:**
a pin whose read delay stays in `[lo, hi]` ps can skip (never read) an input interval `[a, b)` only if
`b - a ≤ hi - lo` (`skip_width`). So `GateOK` covers inertial filtering only of pulses no wider than the pin's delay
window; a pure inertial channel with delay `d` (it swallows every pulse narrower than `d`) is a `GateOK` behaviour
only where `d` fits the window. For the claims about THE target this is the pessimistic direction for safety: fewer
pulses are filtered than an inertial fabric would filter (H_RUNT(w), `SpecRunt`, is the named hypothesis for more).
-/

namespace Formal.Target

/-- If read times `f` (monotone, delays in `[lo, hi]` from `t0` on) jump over `[a, b)` between `t` and `t + 1`,
the skipped interval is at most `hi - lo` wide. -/
theorem skip_width {f : Nat → Nat} {lo hi t0 t a b : Nat} (hd : ∀ s, t0 ≤ s → f s ≤ s ∧ lo ≤ s - f s ∧ s - f s ≤ hi)
    (ht : t0 ≤ t) (h1 : f t < a) (h2 : b ≤ f (t + 1)) : b - a ≤ hi - lo := by
  have e1 := hd t ht
  have e2 := hd (t + 1) (by omega)
  omega

/-- Read times never skip a pulse of width more than `hi - lo`: every interval `[a, b)` with `b - a > hi - lo`
inside the read range is hit by some read time. -/
theorem read_hits {f : Nat → Nat} {lo hi t0 a b : Nat} (hm : Monotone f)
    (hd : ∀ s, t0 ≤ s → f s ≤ s ∧ lo ≤ s - f s ∧ s - f s ≤ hi) (hw : hi - lo < b - a) (ha : f t0 < a)
    (hb : ∃ s, t0 ≤ s ∧ b ≤ f s) : ∃ s, t0 ≤ s ∧ a ≤ f s ∧ f s < b := by
  classical
  obtain ⟨s, hs0, hs⟩ := hb
  by_contra hc
  push Not at hc
  -- every read time from t0 to s is < a, by induction; contradiction at s
  have : ∀ u, t0 ≤ u → f u < a := by
    intro u hu
    induction u, hu using Nat.le_induction with
    | base => exact ha
    | succ u hu ih =>
      by_contra hn
      push Not at hn
      have hb' : b ≤ f (u + 1) := by
        by_contra hlt
        push Not at hlt
        exact absurd (hc (u + 1) (by omega) hn) (by omega)
      have := skip_width hd hu ih hb'
      omega
  have := this s hs0
  omega

end Formal.Target
