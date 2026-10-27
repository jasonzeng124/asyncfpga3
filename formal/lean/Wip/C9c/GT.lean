import Wip.C9c.GuardL
namespace Formal.Net.MullerAll
#eval (List.range 16).all chkPredW
#eval (List.range 16).all chkSuccW
theorem p0 : chkPredW 0 = true := by decide +kernel
theorem s0 : chkSuccW 0 = true := by decide +kernel
theorem p1 : chkPredW 1 = true := by decide +kernel
theorem s1 : chkSuccW 1 = true := by decide +kernel
theorem p2 : chkPredW 2 = true := by decide +kernel
theorem s2 : chkSuccW 2 = true := by decide +kernel
end Formal.Net.MullerAll
