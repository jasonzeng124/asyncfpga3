import Formal.Cells.BigCertPS.C155

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c155_k1 : (List.range' 1 13).all (fun i => krowOK (c155.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c155_sf1 : ((List.range' 1 13).map fun i => sFmin ((c155.2.getD i default).r.arcs (pathPin (c155.2.getD i default)))).sum = 2871 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c155_ss1 : ((List.range' 1 13).map fun i => sSmin ((c155.2.getD i default).r.arcs (pathPin (c155.2.getD i default)))).sum = 7180 := by decide +kernel

end Formal.Cells.BigCertPS
