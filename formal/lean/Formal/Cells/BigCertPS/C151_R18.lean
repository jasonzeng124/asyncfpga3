import Formal.Cells.BigCertPS.C151

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c151_k18 : (List.range' 105 1).all (fun i => krowOK (c151.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c151_sf18 : ((List.range' 105 1).map fun i => sFmin ((c151.2.getD i default).r.arcs (pathPin (c151.2.getD i default)))).sum = 221 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c151_ss18 : ((List.range' 105 1).map fun i => sSmin ((c151.2.getD i default).r.arcs (pathPin (c151.2.getD i default)))).sum = 537 := by decide +kernel

end Formal.Cells.BigCertPS
