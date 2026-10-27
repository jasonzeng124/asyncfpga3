import Wip.C9c.Local
namespace Formal.Net.MullerAll
open Formal.Net.Muller
theorem t1 : chkMid .rt = true := by decide +kernel
theorem t2 : chkLeft .rt = true := by decide +kernel
theorem t3 : chkRight .rt = true := by decide +kernel
theorem t4 : chkMid .iso = true := by decide +kernel
theorem t5 : chkLeft .iso = true := by decide +kernel
theorem t6 : chkRight .iso = true := by decide +kernel
end Formal.Net.MullerAll
