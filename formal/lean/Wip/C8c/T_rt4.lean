import Formal.Net.Muller
open Formal.Net.Muller
set_option maxRecDepth 100000 in
theorem t : check .rt 4 = true := by decide +kernel
