import Formal.Cells.ZeroDelayNetWit
import Formal.Cells.ZeroDelayNetTok
/-! P10c item 3: ZeroDelayNet* (f05a8d1), ZeroDelayRefine (260e219). -/
open Formal.Cells Formal.Cells.LinkExact Formal.Cells.ZeroDelayRefine Formal.Cells.ZeroDelayNet

#print axioms Formal.Cells.ZeroDelayNet.chain_refines
#print axioms Formal.Cells.ZeroDelayNet.chain_witness
#print axioms Formal.Cells.ZeroDelayNet.chain_causal
#print axioms Formal.Cells.ZeroDelayNet.chain_spec
#print axioms Formal.Cells.ZeroDelayNet.negdelay_breaks_causal
#print axioms Formal.Cells.ZeroDelayNet.net_mono
#print axioms Formal.Cells.ZeroDelayRefine.link_refines
#print axioms Formal.Cells.ZeroDelayRefine.link_ref_iff
#print axioms Formal.Cells.ZeroDelayRefine.link_ref_breaks
#print axioms Formal.Cells.ZeroDelayRefine.steer_refines
#print axioms Formal.Cells.ZeroDelayRefine.mux_refines
#print axioms Formal.Cells.ZeroDelayRefine.abs_link

namespace P10c3
/-- Feed the witness into the headline itself (not only chain_ref). -/
example (v : Bool) (u : Nat → Nat) : ∀ i < 2, Causal (Pw i) := by
  obtain ⟨hc, rd, r, A, B, D, C, Q, hb, _⟩ := chain_witness v
  exact (chain_refines hc hb u).2.2.2.2.1

/-- The C-side run is built from the parameters alone: abs_link has NO hypotheses. -/
example (sw v : Bool) (w0 u : Nat) := abs_link sw v w0 u

/-- Mutation: stage 1's data window one ps earlier breaks H_DATA_LOOP. -/
def Pm (i : Nat) : Par := if i = 0 then Pw0 else { Pw1 with Td := Pw1.Td - 1 }
example : ¬ ((Pm 0).U1 + (Pm 0).Ehi ≤ (Pm 1).Td) := by decide
example : (Pw 0).U1 + (Pw 0).Ehi = (Pw 1).Td := by decide
end P10c3
