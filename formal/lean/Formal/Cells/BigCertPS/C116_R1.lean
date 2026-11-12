import Formal.Cells.BigCertPS.C116

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c116_k1 : (List.range' 13 16).all (fun i => krowOK (c116.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c116_sf1 : ((List.range' 13 16).map fun i => sFmin ((c116.2.getD i default).r.arcs (pathPin (c116.2.getD i default)))).sum = 3686 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c116_ss1 : ((List.range' 13 16).map fun i => sSmin ((c116.2.getD i default).r.arcs (pathPin (c116.2.getD i default)))).sum = 9208 := by decide +kernel

end Formal.Cells.BigCertPS
