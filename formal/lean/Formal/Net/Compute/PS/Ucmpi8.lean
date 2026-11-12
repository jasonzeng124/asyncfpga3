import Formal.Gen.Compute.PSMap.Ucmpi8.All
import Formal.Net.Compute.GcdEqZero
import Formal.Net.Compute.PS.Common

/-!
# THE target's `ucmpi8` datapath unit, on the decoded netlist (shard C, 2026-11-09)

**Problem.** `GcdD.ucmpi8_fn` (GcdEqZero.lean) proves that the yosys cells of `bdc_fused_ucmpi8` compute
`e0 == 0` (32-bit zero test, a 1-bit condition read by the control). Do THE target's DECODED gates (`Formal.Target.DecodedPS.net`) compute the same thing?

**Proved** (`ucmpi8_ps`): for every valuation `v` of the decoded nodes in which every decoded gate
driving a node of `S` is settled (`OnDecoded.Settled`), the word at the unit's decoded `z` nodes is
the op applied to the words at its decoded input nodes.


Route: `PS.unit_ps` (`OnDecoded.corr_sound`) with the generated certificate
`Gen/Compute/PSMap/Ucmpi8/*` (untrusted generator `formal/tools/compute/ps/psmap.py`; every gate, map
entry and cell checked by the kernel against DecodedPS's gate list), then `ucmpi8_fn`.

**Not shown.** That the nodes settle (timing), that the input nodes hold the operands the token
protocol delivers.
-/

namespace Formal.Net.Compute.PS.Ucmpi8
open Formal.Target Formal.Net.Compute Formal.Net.Compute.OnDecoded Formal.Net.Compute.PS Formal.Net.GcdHw

abbrev maps := Formal.Gen.Compute.PSMap.Ucmpi8.maps
abbrev outs := Formal.Gen.Compute.GcdD.Ucmpi8.outs

/-- The decoded nodes the statement needs settled. -/
abbrev S := Formal.Gen.Compute.PSMap.Ucmpi8.S

/-- The decoded node carrying bit `k` of input `e0_data`. -/
def e0Node (k : Nat) : Nat := inNode maps 0 k

/-- The decoded node carrying bit `i` of `z_data`. -/
def zNode (i : Nat) : Nat := outNode maps outs i

set_option maxRecDepth 100000 in
theorem psi_ok : maps.psi.all (fun e => decide (e.1 < ([32]:List Nat).length) &&
    decide (e.2.1 < ([32]:List Nat).getD e.1 0)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem outs_ok : outsMapped maps Formal.Gen.Compute.PSMap.Ucmpi8.cells outs = true := by decide +kernel

/-- **THE target's decoded `ucmpi8` gates compute `e0 == 0` (32-bit zero test, a 1-bit condition read by the control)**, for every valuation of the decoded nodes
in which the gates driving `S` are settled. -/
theorem ucmpi8_ps (v : Nat → Bool) (h : Settled DecodedPS.net S v) :
    word (v ∘ zNode) 1 = Ops.cmpi .eq 32 (word (v ∘ e0Node) 32) 0 := by
  have hu := unit_ps Formal.Gen.Compute.PSMap.Ucmpi8.D_ok Formal.Gen.Compute.PSMap.Ucmpi8.topo_ok
    Formal.Gen.Compute.PSMap.Ucmpi8.cells_ok [32] psi_ok outs_ok h
  have e : inWords maps v [32] = [(word (v ∘ e0Node) 32)] := rfl
  rw [e, Formal.Net.Compute.GcdD.ucmpi8_fn _] at hu
  exact hu

end Formal.Net.Compute.PS.Ucmpi8
