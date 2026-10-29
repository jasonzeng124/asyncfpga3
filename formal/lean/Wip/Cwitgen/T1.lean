import Formal.Net.GenWitOx
namespace Formal.Net.CellBind.GenWit
open Formal.Net Formal.Net.CapNet Formal.Net.CapNet.Wit Formal.Net.CapNet.Gcd
set_option maxRecDepth 100000
theorem t1 : (List.range' 0 367).all (fun i => kChkG gcdA (goxA i) (srcV 12 18) (ops.getD i (K.sink 0))) = true := by decide +kernel
end Formal.Net.CellBind.GenWit
