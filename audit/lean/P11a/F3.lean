import Formal.Net.CapstoneRefineGcd
import Formal.Net.CapstoneRefineWit
/-! P11a item 3 (formal 424e8ee, C-8x). -/
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapstoneRefine Formal.Timing

#print axioms Formal.Net.CapstoneRefine.run_settles
#print axioms Formal.Net.CapstoneRefine.held_dag
#print axioms Formal.Net.CapstoneRefine.held_cert
#print axioms Formal.Net.CapstoneRefine.sampled_eq_zd_dag
#print axioms Formal.Net.CapstoneRefine.held_net
#print axioms Formal.Net.CapNet.Gcd.gcd_hw_circuit_safe_phys
#print axioms Formal.Net.CapNet.Wit.gcd_hw_phys_witness
#print axioms Formal.Net.CapstoneRefine.Wit.refine_witness

namespace P11a

/-- Own: H_TCHECK can be met by H_BUNDLE itself (observed bus := Ops bus, every channel
`exempt`; H_ZD_AGREE is then `rfl`). So `gcd_hw_circuit_safe_phys` generalises
`gcd_hw_circuit_safe3` (plus H_RECV); it does not discharge H_BUNDLE. -/
theorem phys_from_bundle (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch start).req) t ≤ 1)
    (H_RECV : ∀ c t, RecvStep (ch c) t) (H_BUNDLE : ∀ c, Held (ch c)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) :=
  (gcd_hw_circuit_safe_phys a b ha hb ch (fun c => (ch c).dat) H_CELLS H_START_ONCE H_RECV
    (fun _ _ _ => rfl) (fun c => .exempt (H_BUNDLE c))).1

/-- Own: conversely every BCert yields Held of the observed channel: H_TCHECK is exactly
"the observed channel is bundled" (given reset and H_RECV); the content is in which
constructor each channel uses. -/
theorem bcert_iff_held (P : Chan) (hi : Init P) (hr : ∀ t, RecvStep P t) : BCert P ↔ Held P :=
  ⟨fun B => held_of_bcert B hi hr, fun h => .exempt h⟩

-- MUTATION: widen the witness netlist's data arc to [1,6] (overlapping the request arc [5,6]):
-- tcheck's DAG verdict rejects it, so no `BCert.dag` can be built from it.
example : checkArr ⟨[⟨0, 1, 1, 6⟩, ⟨0, 2, 5, 6⟩]⟩ 2 [1] 0 = false := by decide
example : checkArr Wit.wnet 2 [1] 0 = true := by decide

#print axioms phys_from_bundle
#print axioms bcert_iff_held
end P11a
