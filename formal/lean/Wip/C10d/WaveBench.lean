import Formal.Timing.RoutedMuller64S1Wave
open Formal.Timing Formal.Timing.Routed
set_option maxRecDepth 100000 in
theorem wave_qn : winB Muller64S1Wave.indepB Muller64S1Wave.qn = some (13922, 47367) := by decide +kernel
set_option maxRecDepth 100000 in
theorem wave_qn_slowE : winB Muller64S1Wave.slowEB Muller64S1Wave.qn = some (38420, 47367) := by decide +kernel
