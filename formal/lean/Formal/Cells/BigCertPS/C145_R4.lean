import Formal.Cells.BigCertPS.C145

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c145_k4 : (List.range' 32 3).all (fun i => krowOK (c145.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c145_sf4 : ((List.range' 32 3).map fun i => sFmin ((c145.2.getD i default).r.arcs (pathPin (c145.2.getD i default)))).sum = 1456 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c145_ss4 : ((List.range' 32 3).map fun i => sSmin ((c145.2.getD i default).r.arcs (pathPin (c145.2.getD i default)))).sum = 3520 := by decide +kernel

end Formal.Cells.BigCertPS
