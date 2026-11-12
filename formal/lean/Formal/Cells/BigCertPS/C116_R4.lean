import Formal.Cells.BigCertPS.C116

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c116_k4 : (List.range' 36 1).all (fun i => krowOK (c116.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c116_sf4 : ((List.range' 36 1).map fun i => sFmin ((c116.2.getD i default).r.arcs (pathPin (c116.2.getD i default)))).sum = 430 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c116_ss4 : ((List.range' 36 1).map fun i => sSmin ((c116.2.getD i default).r.arcs (pathPin (c116.2.getD i default)))).sum = 1022 := by decide +kernel

end Formal.Cells.BigCertPS
