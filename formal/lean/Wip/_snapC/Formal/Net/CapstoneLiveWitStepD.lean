import Formal.Net.CapstoneLiveWitData

/-!
# Probe C-8z2 (3D): step property of the witness run, operators 180 .. 239

Every gate of every operator in the range (except `start`'s LUT) is at its excitation's target
one tick after it is excited, at every tick (`opStep`, checked at change points).
-/

namespace Formal.Net.CapNet.LiveWit
open Formal.Net Formal.Net.CapNet Formal.Net.CapNet.Gcd

set_option maxRecDepth 100000

theorem lstepD : stepR cdW 180 240 = true := by decide +kernel

end Formal.Net.CapNet.LiveWit
