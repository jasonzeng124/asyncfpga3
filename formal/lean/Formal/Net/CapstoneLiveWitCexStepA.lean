import Formal.Net.CapstoneLiveWitCexData

/-!
# Probe C-8z2 (8A): step property of the counterexample run, operators 0 .. 179
-/

namespace Formal.Net.CapNet.LiveWit
open Formal.Net Formal.Net.CapNet Formal.Net.CapNet.Gcd

set_option maxRecDepth 100000

theorem xstepA : stepR cdX 0 180 = true := by decide +kernel

end Formal.Net.CapNet.LiveWit
