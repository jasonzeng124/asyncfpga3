import Formal.Cells.BigCertPS.C150

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c150_k3 : (List.range' 98 4).all (fun i => krowOK (c150.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c150_sf3 : ((List.range' 98 4).map fun i => sFmin ((c150.2.getD i default).r.arcs (pathPin (c150.2.getD i default)))).sum = 1851 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c150_ss3 : ((List.range' 98 4).map fun i => sSmin ((c150.2.getD i default).r.arcs (pathPin (c150.2.getD i default)))).sum = 4574 := by decide +kernel

end Formal.Cells.BigCertPS
