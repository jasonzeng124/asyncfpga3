import Formal.Net.CapstoneLiveWitCexData

/-!
# Probe C-8z2 (8B): step property of the counterexample run, operators 180 .. 366
-/

namespace Formal.Net.CapNet.LiveWit
open Formal.Net Formal.Net.CapNet Formal.Net.CapNet.Gcd

set_option maxRecDepth 100000

theorem xstepB : stepR cdX 180 367 = true := by decide +kernel

end Formal.Net.CapNet.LiveWit
