import Formal.Cells.BigCertPS.C154

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c154_k4 : (List.range' 62 19).all (fun i => krowOK (c154.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c154_sf4 : ((List.range' 62 19).map fun i => sFmin ((c154.2.getD i default).r.arcs (pathPin (c154.2.getD i default)))).sum = 4253 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c154_ss4 : ((List.range' 62 19).map fun i => sSmin ((c154.2.getD i default).r.arcs (pathPin (c154.2.getD i default)))).sum = 10599 := by decide +kernel

end Formal.Cells.BigCertPS
