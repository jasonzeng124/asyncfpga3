import Formal.Cells.BigCertPS.C107

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c107_k1 : (List.range' 2 6).all (fun i => krowOK (c107.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c107_sf1 : ((List.range' 2 6).map fun i => sFmin ((c107.2.getD i default).r.arcs (pathPin (c107.2.getD i default)))).sum = 1903 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c107_ss1 : ((List.range' 2 6).map fun i => sSmin ((c107.2.getD i default).r.arcs (pathPin (c107.2.getD i default)))).sum = 4637 := by decide +kernel

end Formal.Cells.BigCertPS
