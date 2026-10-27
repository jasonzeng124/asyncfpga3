import Formal.Net.Muller
open Formal.Net.Muller
set_option maxRecDepth 100000 in
theorem t : check .rt 1 = true := by decide +kernel
