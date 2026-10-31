import Formal.Core.Circuit
import Formal.Core.Trace.Bridge

/-!
# WIP (probe A-circuit): NOT PROVED — statements only, `sorry` marks open goals.

Everything in `Formal/Core/Circuit.lean` and `Formal/Core/Trace/Bridge.lean`
is proved; this file records the next statements.
-/

namespace Formal.Core.Wip

open Formal.Core Formal.Core.Bridge

/-- (open) Bridge on `ℝ≥0`: signals defined only for `t ≥ 0`. A right-continuous
`f` on `[0, ∞)` with finitely many changes in `(0, ∞)` is denoted by an event
trace whose times are all `> 0`, with `init = f 0`. Expected to follow from
`exists_evTrace` applied to the extension `t ↦ f (max t 0)`; not done because the
project has not decided whether time starts at 0 (all current results use ℝ). -/
theorem exists_evTrace_nonneg (f : ℝ → Bool)
    (hf : ∀ t, 0 ≤ t → ∃ ε > 0, ∀ s, t ≤ s → s < t + ε → f s = f t)
    (hfin : ∃ l : List ℝ, ∀ t, 0 < t → ChangesAt f t → t ∈ l) :
    ∃ e : EvTrace, (∀ τ ∈ e.ts, 0 < τ) ∧ ∀ t, 0 ≤ t → e.toFun t = f t := by
  sorry

/-- (open) Non-vacuity of a feedback loop: a single inverter with pure delay
`d > 0` closed on itself (wire `()`), signals `ℝ → Bool`, has a satisfying
behaviour (the period-`2d` square wave). Receptiveness of *cyclic* circuits
needs such a time-induction construction; `Circuit.receptive_append` only
covers feed-forward composition. -/
theorem inverter_ring_nonvacuous (d : ℝ) (hd : 0 < d) :
    ∃ v : Beh Unit (ℝ → Bool),
      Circuit.Sat [Gate.rel1 (fun a o => ∀ t, o t = !a (t - d)) () ()] v := by
  sorry

end Formal.Core.Wip
