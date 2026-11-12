import Formal.Net.CViewPS.Quiet

/-!
# One real storage node through the collapsed view: `ulink_n143.many.stage[2].u.ctl` (shard C)

The link-controller C-element at `SLICE_X40Y49.A6LUT` (node 151633; the cell name is nextpnr's
placement, provenance only) is the storage node with the smallest static margin in
`tools/cview/out/obl_summary.txt`. Kernel-checked here: it is a logic node of THE target's
circuit and a storage node (`isStor`); its pin 1 reads its own output through its routing
(`srcPS 151633 1 = 151633`), i.e. pin 1 is the feedback pin of `cgate_hold`/`cgate_switch`
(B's `cfb_*`); and the routed loop's composite arcs are exactly the seven listed (pin arc +
six copy gates), whose `smax` sum to 959 ps (`sumMax` at g = 1, κ = 0). So the switch obligation
of this node is "every forcing episode lasts ≥ 959 ps" at the slow corner bound.
-/

namespace Formal.Net.CViewPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecSettle Formal.Timing.SpecChain
  Formal.Timing.ChunkCM Formal.Timing.Huffman Formal.Timing.SpecLoop

theorem n143_logic : logicPS 151633 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem n143_stor : isStor (gAt cs 2500 151633) (pvAt vss 2500 151633) = true := by decide +kernel

theorem n143_k : (gAt cs 2500 151633).k = 6 := by decide +kernel

theorem n143_fb : srcPS 151633 1 = 151633 := by
  rw [srcPS_eq (by rw [n143_k]; decide)]; decide +kernel

theorem n143_loop_smax : ((arcsPS 151633 1).map Arc.smax).sum = 959 ∧ (arcsPS 151633 1).length = 7 := by
  decide +kernel

end Formal.Net.CViewPS
