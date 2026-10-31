import Formal.Timing.ChainSettleExeGcdDData7
namespace Formal.Timing.ChainSettleExe.GcdD
open Formal.Timing Formal.Timing.ChainSettleExe
set_option profiler true
theorem a1 : (sets r1151.arcs 1 r1151.T r1151.N).length = 285 := by decide +kernel
theorem a2 : lrip r1151 = 48022 := by decide +kernel
theorem a3 : ((sets r1151.arcs 1 r1151.T r1151.N).all sepB) = true := by decide +kernel
theorem a4 : dAllB r1151 (sets r1151.arcs 1 r1151.T r1151.N) = true := by decide +kernel
end Formal.Timing.ChainSettleExe.GcdD
