import Formal.Core.Trace.Event

/-!
# WIP for the event-list trace probe (NOT proved; never built)

Open statements left over from `Formal/Core/Trace/Event.lean`.
Everything here is marked `sorry` on purpose.
-/

namespace Formal.Core.TraceEvent.Wip

open Formal.Core.TraceEvent

/-- UNPROVED. Composition for the crossing-permitting channel `ChanX`.
Believed true: the canonical events of `y` are the raw events of the first
stage taken with odd multiplicity; pairs of even multiplicity can be routed
through the second stage with equal delays (`lo₂`) so they cancel again.
Proving it needs a multiset-parity normal form for raw lists
(`flips l = flips (normalize l)` with `normalize` sorted and duplicate-free)
and a matching between `raw₁` and `y.evs`; estimated 150-250 lines. -/
theorem ChanX.comp {lo₁ hi₁ lo₂ hi₂ : ℝ} {x y z : Sig}
    (h₁ : ChanX lo₁ hi₁ x y) (h₂ : ChanX lo₂ hi₂ y z) :
    ChanX (lo₁ + lo₂) (hi₁ + hi₂) x z := by
  sorry

end Formal.Core.TraceEvent.Wip
