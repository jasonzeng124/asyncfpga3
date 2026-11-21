import Formal.Gen.Compute.PSMap.Uselect1.All
import Formal.Net.Compute.GcdUselect1Fn

/-!
# THE target's `uselect1` datapath unit, on the decoded netlist (shard C, 2026-11-09)

**Problem.** `GcdUselect1Fn.uselect1_fn` proves that the yosys cells of `bdc_fused_uselect1`
compute `d = e0 - e1; (d > -1) ? d : 0 - d`. THE theorem is about the DECODED target
(`Formal.Target.DecodedPS.net`). Do the decoded gates compute the same thing?

**Proved** (`uselect1_ps`): for every valuation `v` of the decoded nodes in which every decoded
gate driving a node of `S` (2,645 gates: the unit's LUTs, CARRY4 outputs, pips, site hops,
route-through LUTs and constant drivers) is settled (`Settled`: output = INIT at its pins' current
values), the 32 decoded `z` nodes carry the op applied to the 32 + 32 decoded input nodes.

Route: `OnDecoded.corr_sound` with the generated certificate `Gen/Compute/PSMap/Uselect1/*`
(untrusted generator `formal/tools/compute/ps/psmap.py`; every gate, map entry and cell is
kernel-checked against DecodedPS's gate list: `D_ok`, `topo_ok`, `cells_ok`), composed with
`uselect1_fn`.

**Not shown.** That the nodes ever settle (timing), that the input nodes hold the operands the
token protocol delivers, or anything about the other 19 units.
-/

namespace Formal.Net.Compute.PS.Uselect1
open Formal.Target Formal.Net.Compute Formal.Net.Compute.OnDecoded Formal.Net.GcdHw

abbrev cells := Formal.Gen.Compute.PSMap.Uselect1.cells
abbrev outs := Formal.Gen.Compute.GcdD.Uselect1.outs
abbrev maps := Formal.Gen.Compute.PSMap.Uselect1.maps

/-- The decoded nodes the statement needs settled. -/
abbrev S := Formal.Gen.Compute.PSMap.Uselect1.S

/-- The decoded node carrying bit `k` of input `e0_data` / `e1_data`. -/
def e0Node (k : Nat) : Nat := inNode maps 0 k
def e1Node (k : Nat) : Nat := inNode maps 1 k

/-- The decoded node carrying bit `i` of `z_data`. -/
def zNode (i : Nat) : Nat := (lk maps.phi (outNet outs i)).getD 0

set_option maxRecDepth 100000 in
theorem psi_ok : maps.psi.all (fun e => decide (e.1 < 2) && decide (e.2.1 < 32)) = true := by
  decide +kernel

/-- Every output wire is a mapped net driven by a cell. -/
def outsMapped : Bool :=
  (List.range 32).all fun i => match outs.getD i .c0 with
    | .net n => mem n (cells.flatMap Cell.outs) && (lk maps.phi n).isSome
    | _ => false

set_option maxRecDepth 100000 in
theorem outsMapped_ok : outsMapped = true := by decide +kernel

theorem out_wire (i : Nat) (hi : i < 32) :
    ∃ n, outs.getD i .c0 = .net n ∧ n ∈ cells.flatMap Cell.outs ∧ lk maps.phi n = some (zNode i) := by
  have h := List.all_eq_true.mp outsMapped_ok i (List.mem_range.mpr hi)
  revert h
  unfold zNode outNet
  split
  · rename_i n hn
    intro h
    simp only [Bool.and_eq_true, Option.isSome_iff_exists] at h
    obtain ⟨h1, d, hd⟩ := h
    refine ⟨n, hn, (mem_iff _ _).mp h1, ?_⟩
    simp only [hn, hd, Option.getD_some]
  · intro h; simp at h

set_option maxRecDepth 100000 in
/-- **THE target's decoded `uselect1` gates compute `d = e0 - e1; (d > -1) ? d : 0 - d`**, for every
valuation of the decoded nodes in which the gates driving `S` are settled. -/
theorem uselect1_ps (v : Nat → Bool) (h : Settled DecodedPS.net S v) :
    word (v ∘ zNode) 32 =
      Ops.select (Ops.cmpi .sgt 32 (Ops.subi 32 (word (v ∘ e0Node) 32) (word (v ∘ e1Node) 32)) 4294967295)
        (Ops.subi 32 (word (v ∘ e0Node) 32) (word (v ∘ e1Node) 32))
        (Ops.subi 32 0 (Ops.subi 32 (word (v ∘ e0Node) 32) (word (v ∘ e1Node) 32))) := by
  rw [← Formal.Net.Compute.GcdD.uselect1_fn]
  have hc := corr_sound Formal.Gen.Compute.PSMap.Uselect1.D_ok Formal.Gen.Compute.PSMap.Uselect1.topo_ok
    Formal.Gen.Compute.PSMap.Uselect1.cells_ok h (inEnv2_ok maps 32 psi_ok v)
  unfold unitVal
  apply word_congr
  intro i hi
  obtain ⟨n, hn, hmem, hz⟩ := out_wire i hi
  show v (zNode i) = eval _ [] Formal.Gen.Compute.GcdD.Uselect1.cells (outs.getD i .c0)
  rw [hn]
  exact (hc n hmem (zNode i) hz).symm

end Formal.Net.Compute.PS.Uselect1
