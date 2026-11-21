import Formal.Core.Delay.Corner

/-!
# WIP — corner-correlated delays: open statements (NOT PROVED, contains `sorry`)

Never built. Checked by concatenating with `Formal/Core/Delay/Corner.lean`
(the Corner module has no .olean until the lead builds it):

    (cat Formal/Core/Delay/Corner.lean; tail -n +2 Wip/DelayCorner.lean) > /tmp/delay-corner/W.lean
    ../slot.sh lake env lean /tmp/delay-corner/W.lean

Status: elaborates; 2 `sorry`s (marked SORRY below).
-/

noncomputable section

namespace Formal.Core.Corner.Wip

open Formal.Core.Corner Formal.Core.DelayPure

/-- SORRY 1. **Rule A at both SDF endpoints.** Under affine (non-proportional)
corners, tighten.py's `t_req ≥ t_data + max(0.2·t_data, 200)` checked on the
fast-endpoint and on the slow-endpoint predictions should hold at every
corner, because `t ↦ max(t/5, 200)` is convex and `P_req - P_data` is affine,
so the slack is concave in `c` (a `bundle_ratio_chord`-type argument).
Combined with `ruleA_sound` at each corner this gives rule A under affine
corners. Proof sketch: `max (lerp a b c / 5) 200 ≤ lerp (max (a/5) 200)
(max (b/5) 200) c` by cases on which branch is active, then
`lerp_ge_of_ends`. Estimate: 1 hour. -/
theorem ruleA_two_corner {c Fd Sd Fr Sr : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hF : Fd + max (Fd / 5) 200 ≤ Fr) (hS : Sd + max (Sd / 5) 200 ≤ Sr) :
    lerp Fd Sd c + max (lerp Fd Sd c / 5) 200 ≤ lerp Fr Sr c := by
  sorry

/-- A read-time map whose delay may drift, but only slowly: the corner moves
with temperature during a run, `|Δdelay| ≤ ρ·|Δt|`. -/
structure SlowRetime (lo hi ρ : ℝ) extends Retime lo hi where
  drift : ∀ a b, a ≤ b → (b - σ b) - (a - σ a) ≤ ρ * (b - a) ∧
                         (a - σ a) - (b - σ b) ≤ ρ * (b - a)

/-- SORRY 2. **Drift does not reopen the independent band.** With a delay that
drifts at rate `ρ < 1` inside the corner band `[lo, hi]`, a pulse of width
`w` survives with width at least `(1-ρ)·w`, instead of the
`w - (hi - lo)` of `DelayPure.pulse_out_core`. This is the trace-level form of
"one corner per die (per moment)". It needs an intermediate-value / sSup
argument on `σ`, which needs `Mathlib.Order.ConditionallyCompleteLattice`
(not built). Estimate: half a day once built. -/
theorem slow_pulse_survives {lo hi ρ w : ℝ} (hρ : ρ < 1) (hw : 0 < w)
    (r : SlowRetime lo hi ρ) :
    ∃ a b, (1 - ρ) * w ≤ b - a ∧ ∀ s, a ≤ s → s < b → pulse w (r.σ s) = true := by
  sorry

/-! Not formalised (needs measure theory, which is not built here):
the population form of LocalScatter. The deterministic `κ` of `Scat` is a
worst case; ring data supports only "a tail exceeds κ with probability ≤ p".
With `N` select gates whose tails scatter independently, a union bound gives
P(any rule-E violation) ≤ N·p. With p = 5 % (the 95/95 tolerance reading of
GUARD_LO/GUARD_HI) and N = 118 select gates (gcd), the bound is vacuous;
that is the quantitative reason the guardband must be read as a population
quantile rather than a proof hypothesis. -/

end Formal.Core.Corner.Wip

end
