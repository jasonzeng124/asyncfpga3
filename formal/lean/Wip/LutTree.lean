import Formal.Core.LutTree
/-!
# Wip/LutTree.lean — next steps for Formal.Core.LutTree (NOT built, NOT claimed)

These statements are not proved yet. Each `sorry` is deliberate and marked.
The proved base is `Formal/Core/LutTree.lean`.
-/

namespace Formal.Core.LutTree.Wip
open Formal.Core.LutTree K3

/-- Positive unateness of the INIT on the cube that a transition spans: raising any
changing pin never lowers the entry. -/
def UnateUp (init : List Bool → Bool) (old new : List Bool) : Prop :=
  ∀ w w', Consistent (PhysTree.mergeK old new) w → Consistent (PhysTree.mergeK old new) w' →
    (∀ i (h : i < w.length) (h' : i < w'.length), w[i] = true → w'[i] = true) →
    init w = true → init w' = true

/-- CONJECTURE (unproved). In the exact model, a multi-input change in which every
changing pin rises with a clean edge (any skews, any per-mux delays) and the INIT is
positively unate on the spanned cube gives at most one output transition: there is
a time T before which the output is the old entry, and after which it never returns
to it. This is what a LUT C-element or majority gate relies on when
several inputs rise one after another. The mux-tree structure should give it. Proof idea:
each node's waveform is a monotone function of monotone select waveforms.
Missing: a K3 waveform order ("only goes 0 → X → 1"), and kmux preserving it
under unateness. -/
theorem exact_unate_single_transition : True := by
  -- placeholder: the real statement (see docstring) is not yet written
  sorry

/-- CONJECTURE (unproved, needs a weaker silicon hypothesis). Under `H_mux_kleene`
alone, the X window of a single input change with differing entries may hide a
non-monotone runt (0 → 1 → 0 → 1). To exclude it one needs
`H_mux_monotone`: a pass-transistor mux driven by a monotone select between two
constant data levels has a monotone output. State and use it here. -/
theorem sic_monotone_under_H_mux_monotone : True := by
  sorry

end Formal.Core.LutTree.Wip
