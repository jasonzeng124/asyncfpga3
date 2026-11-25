import Formal.Cells.BigCertPS.C151

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c151_k33 : (List.range' 136 1).all (fun i => krowOK (c151.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c151_sf33 : ((List.range' 136 1).map fun i => sFmin ((c151.2.getD i default).r.arcs (pathPin (c151.2.getD i default)))).sum = 582 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c151_ss33 : ((List.range' 136 1).map fun i => sSmin ((c151.2.getD i default).r.arcs (pathPin (c151.2.getD i default)))).sum = 1417 := by decide +kernel

end Formal.Cells.BigCertPS
