import Formal.Net.CViewPS.RIslDefs
import Formal.Net.CViewPS.P1Defs

/-! Shard C: the delay bounds of the reset island's members in prjxray slow-max units (checked per block in
RIslBnd*.lean): every member's collapsed start is at most `A2` and every pin's composite slow-max delay at most `M2`. -/

namespace Formal.Net.CViewPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecSettle Formal.Timing.SpecChain
  Formal.Timing.SpecChainM Formal.Timing.ChunkCM Formal.Timing.Huffman Formal.Timing.SpecLoop Formal.Timing.Island

def A2 : Nat := 19832
def M2 : Nat := 4636

def rBndOK (e : Nat × Bool × List Nat × Nat) : Bool :=
  decide (cStartN (gAt cs 2500 e.1) (pcsPS e.1) ≤ A2) &&
  ((List.range (gAt cs 2500 e.1).k).all fun i => decide (sumMaxN (arcsPS e.1 i) ≤ M2))

end Formal.Net.CViewPS
