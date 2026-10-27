import Formal.Net.FasmLink.LinkArb
import Formal.Net.FasmLink.S1
open Formal.Net.FasmLink
#eval (LinkArb.design S1.net S1.ports S1.rho).check
#eval (List.range 3).map fun k => match LinkArb.insts[k]?, S1.rho[k]? with
  | some I, some r => ((LinkArb.design S1.net S1.ports S1.rho).supp k I r).length
  | _, _ => 0
set_option maxHeartbeats 0 in
theorem t1 : (LinkArb.design S1.net S1.ports S1.rho).Correct := Design.check_sound _ (by decide)
