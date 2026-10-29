import Formal.Net.CapstoneRigAll
import Formal.Net.RigAllWit
/-! P11a item 4 (formal 047094b, C-8s3, and its witness). -/
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapNet.RigWit

#print axioms Formal.Net.CapNet.Gcd.gcd_rig_all
#print axioms Formal.Net.CapNet.RigWit.gcd_rig_all_witness
#print axioms Formal.Net.CapNet.RigWit.gcd_rig_all_witness_consistent
#check @Formal.Net.CapNet.Gcd.gcd_rig_all

namespace P11a
-- own: gcd_rig.v vector idx 2 = {g 0x0C, b 0x12, a 0x06}?  (vec = {g, b, a}, a_v = vec[31:0])
-- research: 4'd2: vector = {32'h00000006, 32'h00000012, 32'h0000000C} -> g=6, b=18, a=12.
example : Nat.gcd 0x0C 0x12 = 0x06 := by decide

/-- MUTATION: the theorem's spec cannot be replaced by a wrong value on the witness
(three offers really are observed and carry 6, not gcd 12 19 = 1). -/
theorem rig_wrong_spec_false :
    ¬ (∀ k r, OffAt (chR out0) k r → (chR out0).dat (r + 1) = Nat.gcd 12 19) := by
  intro h
  have h1 := h 0 430 r_out0.1.1
  rw [r_out0.1.2] at h1
  exact absurd h1 (by decide)
#print axioms rig_wrong_spec_false
end P11a
