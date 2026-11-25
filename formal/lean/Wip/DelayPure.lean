import Formal.Core.Delay.Pure
/-!
# WIP (NOT PROVED, never built): bounded pure delay, open items

Everything below is a statement only; each `sorry` is an open obligation.
Proved material lives in `Formal/Core/Delay/Pure.lean`.
-/
namespace Formal.Core.DelayPure.Wip
open Formal.Core.DelayPure

/-- Event-list view: a signal given by an initial value and a strictly
increasing finite list of transition times. -/
noncomputable def ofEvents (init : Bool) (ev : List ℝ) : Sig :=
  fun t => Nat.rec init (fun _ b => !b) (ev.countP (fun e => decide (e ≤ t)))

/-- OPEN (adequacy w.r.t. the textbook per-transition model): if every
transition `t_i` is delayed by `d_i ∈ [lo, hi]` and the delayed times stay
strictly increasing (FIFO, no crossing), the delayed event list is a
behaviour of `Chan lo hi`.  Proof idea: piecewise σ, `σ s = t_i` on
`[t_i + d_i, t_{i+1} + d_{i+1})`, clamped into the band between events. -/
theorem events_adequate (lo hi : ℝ) (init : Bool) (ev ds : List ℝ)
    (hlen : ev.length = ds.length)
    (hd : ∀ d ∈ ds, lo ≤ d ∧ d ≤ hi)
    (hsorted : (List.zipWith (· + ·) ev ds).Pairwise (· < ·))
    (hev : ev.Pairwise (· < ·)) :
    Chan lo hi (ofEvents init ev) (ofEvents init (List.zipWith (· + ·) ev ds)) := by
  sorry

/-- OPEN (refinement): rise/fall skew bound.  A channel whose per-run
delay varies by at most a skew `κ ≤ hi - lo` between any two output times
(|(σ s - σ s') - (s - s')| ≤ κ).  Pulse collapse then needs width ≤ κ,
not ≤ hi - lo. -/
structure SkewRetime (lo hi κ : ℝ) extends Retime lo hi where
  skew_lo : ∀ s s', s' ≤ s → (s - s') - κ ≤ σ s - σ s'
  skew_hi : ∀ s s', s' ≤ s → σ s - σ s' ≤ (s - s') + κ

theorem skew_pulse_survives (lo hi κ w : ℝ) (hw : κ < w) (y : Sig)
    (r : SkewRetime lo hi κ) (e : ∀ s, y s = pulse w (r.σ s)) :
    ∃ s, y s = true := by
  sorry

end Formal.Core.DelayPure.Wip
