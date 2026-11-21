import Formal.Cells.BigCertPS.C135

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c135_k3 : (List.range' 21 5).all (fun i => krowOK (c135.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c135_sf3 : ((List.range' 21 5).map fun i => sFmin ((c135.2.getD i default).r.arcs (pathPin (c135.2.getD i default)))).sum = 1593 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c135_ss3 : ((List.range' 21 5).map fun i => sSmin ((c135.2.getD i default).r.arcs (pathPin (c135.2.getD i default)))).sum = 3876 := by decide +kernel

end Formal.Cells.BigCertPS
