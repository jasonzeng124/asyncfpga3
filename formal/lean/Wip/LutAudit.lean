import Formal.Core.LutAudit

/-!
# Wip.LutAudit — open statements of the LUT hazard audit (NOT proved, not built)

What `Formal.Core.LutAudit` proves for a dynamic hazard-free transition is
`dyn_single_window`: the Kleene value of the output goes old → X → new under
any monotone pin progress. Under `H_mux_kleene` the physical output then
equals old before ONE window and new after it, but the model says nothing
inside the window. The statement below asks for more: in the exact model of
`LutTree` (`exactTree`, every mux is `kmux` of its delayed inputs, transport
delays), with clean pin edges (`CleanEdge`), a dynamic hazard-free transition
gives at most one clean output transition. This is the dynamic analogue of
`exact_sic_clean`.

Why it is not obvious: in `exactTree` the select of a mux copy on one path
can see a pin's edge at a different time from another copy (per-copy `dsel`),
so the internal nodes do NOT see one consistent vertex sequence; an output
pulse could in principle come from two copies of one pin disagreeing. The
Kleene argument covers this (copies disagreeing is just X), the clean-edge
argument has to be redone per path.
-/

namespace Wip.LutAudit
open Formal.Core.LutTree Formal.Core.LutTree.K3 Formal.Core.LutAudit Formal.Core.LutCells

/- CONJECTURE (unproved, not yet stated formally): for `exactTree n (effTable L o) pin
dsel ddat` whose pins realise the free-pin transition `old → new` with every
changing pin a `CleanEdge`, `DynHF L o old new` implies the root waveform has
at most one clean transition. Next step: state it with the per-copy edge
times of `exact_sic_clean` and prove it by induction on the tree, using
`dyn_stays_new`/`dyn_never_back` at every node. -/

end Wip.LutAudit
