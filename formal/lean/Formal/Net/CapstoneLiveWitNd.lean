import Formal.Net.CapstoneLiveWitData

/-!
# Probe C-8z2 (4): the witness run never deadlocks before out0 closes

`lnd`: the certificate `certL` (one excited gate, not `start`'s LUT, for each tick
`0 .. closeL`) checks against the run.
-/

namespace Formal.Net.CapNet.LiveWit
open Formal.Net Formal.Net.CapNet Formal.Net.CapNet.Gcd

set_option maxRecDepth 100000

theorem lnd : ndChk cdW 0 certL = true := by decide +kernel

theorem lcert_len : certL.length = closeL + 1 := by decide +kernel

end Formal.Net.CapNet.LiveWit
