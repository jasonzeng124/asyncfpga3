import Formal.Cells.BigCertPS.C156

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c156_k29 : (List.range' 152 1).all (fun i => krowOK (c156.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c156_sf29 : ((List.range' 152 1).map fun i => sFmin ((c156.2.getD i default).r.arcs (pathPin (c156.2.getD i default)))).sum = 221 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c156_ss29 : ((List.range' 152 1).map fun i => sSmin ((c156.2.getD i default).r.arcs (pathPin (c156.2.getD i default)))).sum = 537 := by decide +kernel

end Formal.Cells.BigCertPS
