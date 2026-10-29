import Formal.Net.CapstoneRefineNet
import Formal.Net.CapstoneWalk

/-!
# Probe C-8x: the capstone with H_BUNDLE replaced by physical bundling certificates

* `gcd_hw_init`: reset of every channel from H_CELLS alone (no H_BUNDLE).
* `gcd_hw_circuit_safe_phys`: `gcd_hw_circuit_safe3` with H_BUNDLE replaced by
  `held_net`'s hypotheses (per channel a tcheck certificate `BCert`, H_ZD_AGREE, H_RECV).
* `gcd_hw_phys_witness`: 8t's witness run meets every hypothesis (observed bus = Ops bus, every
  channel `exempt`): joint consistency only; the tcheck constructors' non-vacuity is
  `Formal.Net.CapstoneRefine.Wit.refine_witness`.
-/

namespace Formal.Net.CapNet.Gcd
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Timing
open Formal.Net.CapstoneRefine

/-- Reset of every channel, from the gate models alone (no H_BUNDLE needed). -/
theorem gcd_hw_init (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o)) : ∀ c, Init (ch c) := fun c =>
  ⟨(cell_proto ch (srcV a b) (opAt (net.prod c)) (H_CELLS _) (dist_of _ (ops_ok _))).initOut c
      ((net.prod_iff c _).2 rfl),
   (cell_proto ch (srcV a b) (opAt (net.cons c)) (H_CELLS _) (dist_of _ (ops_ok _))).initIn c
      ((net.cons_iff c _).2 rfl)⟩

/-- **gcd_hw safety from the physical bundling certificates.** H_BUNDLE of
`gcd_hw_circuit_safe3` is replaced by: per channel, a tcheck row PASS with H_TXWIN (or an
explicit H_DERIVED exemption), H_ZD_AGREE and H_RECV. -/
theorem gcd_hw_circuit_safe_phys (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (ch : Fin NC → Chan) (pdat : Fin NC → Nat → Nat)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch start).req) t ≤ 1)
    (H_RECV : ∀ c t, RecvStep (ch c) t)
    (H_ZD_AGREE : ∀ c t, inTx (ch c) t = true → (ch c).dat t = pdat c t)
    (H_TCHECK : ∀ c, BCert (obsCh ch pdat c)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t =
      List.replicate (Handshake.cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) :=
  gcd_hw_circuit_safe3 a b ha hb ch H_CELLS
    (held_net ch pdat (gcd_hw_init a b ch H_CELLS) H_RECV H_ZD_AGREE H_TCHECK) H_START_ONCE

end Formal.Net.CapNet.Gcd

