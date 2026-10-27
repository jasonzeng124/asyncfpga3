import Formal.Net.Muller
import Formal.Net.MullerCert
open Formal.Net.Muller
set_option profiler true
theorem t1 : ((List.range 256).map (fun j => cert_rt4.getD j 0)).length = 256 := by decide +kernel
theorem t2 : ((List.range 256).map (fun j => (bucket cert_rt4 j).length)).sum = 6076 := by decide +kernel
