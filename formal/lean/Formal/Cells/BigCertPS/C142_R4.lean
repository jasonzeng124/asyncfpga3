import Formal.Cells.BigCertPS.C142

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c142_k4 : (List.range' 49 3).all (fun i => krowOK (c142.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c142_sf4 : ((List.range' 49 3).map fun i => sFmin ((c142.2.getD i default).r.arcs (pathPin (c142.2.getD i default)))).sum = 1622 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c142_ss4 : ((List.range' 49 3).map fun i => sSmin ((c142.2.getD i default).r.arcs (pathPin (c142.2.getD i default)))).sum = 3890 := by decide +kernel

end Formal.Cells.BigCertPS
