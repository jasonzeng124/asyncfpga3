import Formal.Net.Muller
open Formal.Net.Muller
set_option maxRecDepth 100000 in
theorem t : (reachList .iso 4).length = 1152 := by decide +kernel
