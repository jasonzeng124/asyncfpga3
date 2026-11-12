import Formal.Cells.BigCertPS.C154

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c154_k3 : (List.range' 51 11).all (fun i => krowOK (c154.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c154_sf3 : ((List.range' 51 11).map fun i => sFmin ((c154.2.getD i default).r.arcs (pathPin (c154.2.getD i default)))).sum = 3242 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c154_ss3 : ((List.range' 51 11).map fun i => sSmin ((c154.2.getD i default).r.arcs (pathPin (c154.2.getD i default)))).sum = 7889 := by decide +kernel

end Formal.Cells.BigCertPS
