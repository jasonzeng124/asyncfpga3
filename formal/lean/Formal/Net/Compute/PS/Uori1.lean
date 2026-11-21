import Formal.Gen.Compute.PSMap.Uori1.All
import Formal.Net.Compute.GcdBitwise
import Formal.Net.Compute.PS.Common

/-!
# THE target's `uori1` datapath unit, on the decoded netlist (shard C, 2026-11-09)

**Problem.** `GcdD.uori1_fn` (GcdBitwise.lean) proves that the yosys cells of `bdc_fused_uori1` compute
`e0 | e1` (32 bits). Do THE target's DECODED gates (`Formal.Target.DecodedPS.net`) compute the same thing?

**Proved** (`uori1_ps`): for every valuation `v` of the decoded nodes in which every decoded gate
driving a node of `S` is settled (`OnDecoded.Settled`), the word at the unit's decoded `z` nodes is
the op applied to the words at its decoded input nodes.


Route: `PS.unit_ps` (`OnDecoded.corr_sound`) with the generated certificate
`Gen/Compute/PSMap/Uori1/*` (untrusted generator `formal/tools/compute/ps/psmap.py`; every gate, map
entry and cell checked by the kernel against DecodedPS's gate list), then `uori1_fn`.

**Not shown.** That the nodes settle (timing), that the input nodes hold the operands the token
protocol delivers.
-/

namespace Formal.Net.Compute.PS.Uori1
open Formal.Target Formal.Net.Compute Formal.Net.Compute.OnDecoded Formal.Net.Compute.PS Formal.Net.GcdHw

abbrev maps := Formal.Gen.Compute.PSMap.Uori1.maps
abbrev outs := Formal.Gen.Compute.GcdD.Uori1.outs

/-- The decoded nodes the statement needs settled. -/
abbrev S := Formal.Gen.Compute.PSMap.Uori1.S

/-- The decoded node carrying bit `k` of input `e0_data`. -/
def e0Node (k : Nat) : Nat := inNode maps 0 k
/-- The decoded node carrying bit `k` of input `e1_data`. -/
def e1Node (k : Nat) : Nat := inNode maps 1 k

/-- The decoded node carrying bit `i` of `z_data`. -/
def zNode (i : Nat) : Nat := outNode maps outs i

set_option maxRecDepth 100000 in
theorem psi_ok : maps.psi.all (fun e => decide (e.1 < ([32, 32]:List Nat).length) &&
    decide (e.2.1 < ([32, 32]:List Nat).getD e.1 0)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem outs_ok : outsMapped maps Formal.Gen.Compute.PSMap.Uori1.cells outs = true := by decide +kernel

/-- **THE target's decoded `uori1` gates compute `e0 | e1` (32 bits)**, for every valuation of the decoded nodes
in which the gates driving `S` are settled. -/
theorem uori1_ps (v : Nat → Bool) (h : Settled DecodedPS.net S v) :
    word (v ∘ zNode) 32 = Ops.ori 32 (word (v ∘ e0Node) 32) (word (v ∘ e1Node) 32) := by
  have hu := unit_ps Formal.Gen.Compute.PSMap.Uori1.D_ok Formal.Gen.Compute.PSMap.Uori1.topo_ok
    Formal.Gen.Compute.PSMap.Uori1.cells_ok [32, 32] psi_ok outs_ok h
  have e : inWords maps v [32, 32] = [(word (v ∘ e0Node) 32), (word (v ∘ e1Node) 32)] := rfl
  rw [e, Formal.Net.Compute.GcdD.uori1_fn _ _] at hu
  exact hu

end Formal.Net.Compute.PS.Uori1
