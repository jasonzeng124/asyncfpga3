import Formal.Net.GenWitOx
namespace Formal.Net.CellBind.GenWit
open Formal.Net Formal.Net.CapNet Formal.Net.CapNet.Wit Formal.Net.CapNet.Gcd
#eval (List.range 367).filter (fun i => !kChk gcdA (srcV 12 18) (ops.getD i (K.sink 0)))
#eval (List.range 367).filter (fun i => !xChk gcdA (goxA i) (ops.getD i (K.sink 0)))
end Formal.Net.CellBind.GenWit
