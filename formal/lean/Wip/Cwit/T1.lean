import Formal.Net.RigAllWitData
namespace Formal.Net.CapNet.RigWit
open Formal.Net Formal.Net.CapNet Formal.Net.CapNet.Gcd
set_option maxRecDepth 100000
theorem c1 : ((ops.drop 0).take 46).all (fun k => kChkR cdA (srcV 12 18) k) = true := by decide +kernel
end Formal.Net.CapNet.RigWit
