import Formal.Cells.BigCertPS.C140

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c140_k4 : (List.range' 5 1).all (fun i => krowOK (c140.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c140_sf4 : ((List.range' 5 1).map fun i => sFmin ((c140.2.getD i default).r.arcs (pathPin (c140.2.getD i default)))).sum = 206 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c140_ss4 : ((List.range' 5 1).map fun i => sSmin ((c140.2.getD i default).r.arcs (pathPin (c140.2.getD i default)))).sum = 570 := by decide +kernel

end Formal.Cells.BigCertPS
