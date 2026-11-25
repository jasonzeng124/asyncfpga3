import Formal.Cells.BigCertPS.C140

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c140_k12 : (List.range' 15 4).all (fun i => krowOK (c140.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c140_sf12 : ((List.range' 15 4).map fun i => sFmin ((c140.2.getD i default).r.arcs (pathPin (c140.2.getD i default)))).sum = 656 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c140_ss12 : ((List.range' 15 4).map fun i => sSmin ((c140.2.getD i default).r.arcs (pathPin (c140.2.getD i default)))).sum = 1668 := by decide +kernel

end Formal.Cells.BigCertPS
