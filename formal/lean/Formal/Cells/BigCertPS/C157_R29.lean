import Formal.Cells.BigCertPS.C157

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c157_k29 : (List.range' 164 1).all (fun i => krowOK (c157.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c157_sf29 : ((List.range' 164 1).map fun i => sFmin ((c157.2.getD i default).r.arcs (pathPin (c157.2.getD i default)))).sum = 193 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c157_ss29 : ((List.range' 164 1).map fun i => sSmin ((c157.2.getD i default).r.arcs (pathPin (c157.2.getD i default)))).sum = 497 := by decide +kernel

end Formal.Cells.BigCertPS
