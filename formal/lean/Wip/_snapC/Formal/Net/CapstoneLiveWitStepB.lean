import Formal.Net.CapstoneLiveWitData

/-!
# Probe C-8z2 (3B): step property of the witness run, operators 60 .. 119

Every gate of every operator in the range (except `start`'s LUT) is at its excitation's target
one tick after it is excited, at every tick (`opStep`, checked at change points).
-/

namespace Formal.Net.CapNet.LiveWit
open Formal.Net Formal.Net.CapNet Formal.Net.CapNet.Gcd

set_option maxRecDepth 100000

theorem lstepB : stepR cdW 60 120 = true := by decide +kernel

end Formal.Net.CapNet.LiveWit
