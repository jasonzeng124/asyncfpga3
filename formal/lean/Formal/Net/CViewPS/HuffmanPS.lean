import Formal.Net.CViewPS.Ranks
import Formal.Net.CViewPS.Collapsed

/-!
# Every loop of THE target's circuit passes through a storage node (shard C)

**Problem, plainly.** In the collapsed view (`Collapsed.lean`) of THE target's circuit, call a
logic gate a storage node if one of its pins reads its own output through the routing
(`isStor`; 4,597 gates: C-elements, latches, arbiter states) and the other logic gates
combinational (15,281). Is there feedback that does not go through a storage node?

**Proved** (`comb_ranked`): no. There is a rank `ρ` on nodes such that for every combinational
gate at node `w` and every pin of it whose source `s` (the same pin data as in `collapsed`) is a
combinational gate, `ρ s < ρ w`. So every cycle of pin-to-source links contains a storage node:
the circuit is 4,597 storage nodes plus acyclic logic (depth ≤ 96), and loop obligations are
needed only at the storage nodes (`SpecLoop.cgate_switch`) and along the acyclic paths
(`SpecLoop.cgate_stable`). Kernel-checked per chunk (`ranks_ok`); the ranks are untrusted data.

**Not shown.** That the storage nodes behave (their switch obligations); this is structure only.
-/

namespace Formal.Net.CViewPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.Huffman

theorem comb_ranked :
    ∀ w, w / 2500 < cs.length → w % 2500 < (cs.getD (w / 2500) []).length →
      isComb keepPS (gAt cs 2500 w) (pvAt vss 2500 w) = true →
      ∀ i, i < (gAt cs 2500 w).k →
        ∀ s, s = ((pvAt vss 2500 w).getD i (0, 0)).1 →
          s / 2500 < cs.length → s % 2500 < (cs.getD (s / 2500) []).length →
          isComb keepPS (gAt cs 2500 s) (pvAt vss 2500 s) = true →
          (rkPS s).getD 0 < (rkPS w).getD 0 :=
  ranked_of_chunks ranks_ok

end Formal.Net.CViewPS
