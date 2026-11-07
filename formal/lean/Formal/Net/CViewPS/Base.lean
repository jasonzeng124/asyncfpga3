import Formal.Timing.ChunkCM
import Formal.Target.NetPS.All

/-!
# The collapsed view of THE target (gcd_ps_e6bb4aec): definitions (shard C)

`keepPS` is the predicate by which `Spec.circuit` drops the gates that drive environment nodes.
The generated files `T*.lean` (copy-map trees per chunk), `CM.lean` and `V*.lean` (per-gate pin
data) are produced by `formal/tools/cview/gen_lean.py` and checked by the kernel; the
theorem is in `Formal/Net/CViewPS/Collapsed.lean`.
-/

namespace Formal.Net.CViewPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.ChunkCM

/-- The circuit keeps a gate iff it drives no environment node (`Spec.circuit`). -/
def keepPS (g : Gate) : Bool := decide (g.out ∉ boundary.envNodes)

theorem circuit_gates : (circuit net boundary).gates = gates.filter keepPS := by
  simp only [circuit, net]; rfl

/-- The circuit of a well-formed netlist is well formed (it drops gates only). -/
theorem circuit_wf {N : Net} {B : Boundary} (h : N.WF) : (circuit N B).WF := by
  refine ⟨fun g hg => h.1 g (List.mem_filter.mp hg).1, ?_⟩
  exact h.2.sublist ((List.filter_sublist).map Gate.out)

end Formal.Net.CViewPS
