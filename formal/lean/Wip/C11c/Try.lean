import Formal.Net.FasmLink.LinkArb
import Formal.Net.FasmLink.S1
open Formal.Net.FasmLink
theorem t1 : (LinkArb.design S1.net S1.ports S1.rho).Correct := Design.check_sound _ (by decide)
