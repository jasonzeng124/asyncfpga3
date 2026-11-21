import Formal.Cells.BigCertPS.C156

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c156_k11 : (List.range' 47 13).all (fun i => krowOK (c156.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c156_sf11 : ((List.range' 47 13).map fun i => sFmin ((c156.2.getD i default).r.arcs (pathPin (c156.2.getD i default)))).sum = 2348 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c156_ss11 : ((List.range' 47 13).map fun i => sSmin ((c156.2.getD i default).r.arcs (pathPin (c156.2.getD i default)))).sum = 5953 := by decide +kernel

end Formal.Cells.BigCertPS
