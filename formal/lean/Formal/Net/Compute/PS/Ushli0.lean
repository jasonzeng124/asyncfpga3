import Formal.Gen.Compute.PSMap.Ushli0.All
import Formal.Net.Compute.GcdShli0
import Formal.Net.Compute.PS.Common

/-!
# THE target's `ushli0` datapath unit, on the decoded netlist (shard C, 2026-11-09)

**Problem.** `GcdD.ushli0_fn` (GcdShli0.lean) proves that the yosys cells of `bdc_fused_ushli0` compute
`e0 << e1` for shift amounts `e1 < 32` (hypothesis, as in `ushli0_fn`). Do THE target's DECODED gates (`Formal.Target.DecodedPS.net`) compute the same thing?

**Proved** (`ushli0_ps`): for every valuation `v` of the decoded nodes in which every decoded gate
driving a node of `S` is settled (`OnDecoded.Settled`), the word at the unit's decoded `z` nodes is
the op applied to the words at its decoded input nodes (under the same side condition as `ushli0_fn`).


Route: `PS.unit_ps` (`OnDecoded.corr_sound`) with the generated certificate
`Gen/Compute/PSMap/Ushli0/*` (untrusted generator `formal/tools/compute/ps/psmap.py`; every gate, map
entry and cell checked by the kernel against DecodedPS's gate list), then `ushli0_fn`.

**Not shown.** That the nodes settle (timing), that the input nodes hold the operands the token
protocol delivers, or that the side condition holds in THE target.
-/

namespace Formal.Net.Compute.PS.Ushli0
open Formal.Target Formal.Net.Compute Formal.Net.Compute.OnDecoded Formal.Net.Compute.PS Formal.Net.GcdHw

abbrev maps := Formal.Gen.Compute.PSMap.Ushli0.maps
abbrev outs := Formal.Gen.Compute.GcdD.Ushli0.outs

/-- The decoded nodes the statement needs settled. -/
abbrev S := Formal.Gen.Compute.PSMap.Ushli0.S

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
theorem outs_ok : outsMapped maps Formal.Gen.Compute.PSMap.Ushli0.cells outs = true := by decide +kernel

/-- **THE target's decoded `ushli0` gates compute `e0 << e1` for shift amounts `e1 < 32` (hypothesis, as in `ushli0_fn`)**, for every valuation of the decoded nodes
in which the gates driving `S` are settled. -/
theorem ushli0_ps (v : Nat → Bool) (h : Settled DecodedPS.net S v) (hk : (word (v ∘ e1Node) 32) < 32) :
    word (v ∘ zNode) 32 = Ops.shli 32 (word (v ∘ e0Node) 32) (word (v ∘ e1Node) 32) := by
  have hu := unit_ps Formal.Gen.Compute.PSMap.Ushli0.D_ok Formal.Gen.Compute.PSMap.Ushli0.topo_ok
    Formal.Gen.Compute.PSMap.Ushli0.cells_ok [32, 32] psi_ok outs_ok h
  have e : inWords maps v [32, 32] = [(word (v ∘ e0Node) 32), (word (v ∘ e1Node) 32)] := rfl
  rw [e, Formal.Net.Compute.GcdD.ushli0_fn _ _ hk] at hu
  exact hu

end Formal.Net.Compute.PS.Ushli0
