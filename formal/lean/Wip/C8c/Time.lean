import Formal.Net.Muller
open Formal.Net.Muller
#eval (reachList .iso 1).length
#eval (reachList .iso 2).length
#eval (reachList .rt 2).length
#eval (reachList .iso 4).length
#eval (reachList .rt 4).length
#eval check .iso 4
#eval check .rt 4
#eval check .free 1
set_option maxRecDepth 100000 in
theorem t1 : check .iso 1 = true := by decide +kernel
