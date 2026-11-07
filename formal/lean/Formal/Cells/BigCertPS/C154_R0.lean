import Formal.Cells.BigCertPS.C154

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c154_k0 : (List.range' 0 34).all (fun i => krowOK (c154.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c154_sf0 : ((List.range' 0 34).map fun i => sFmin ((c154.2.getD i default).r.arcs (pathPin (c154.2.getD i default)))).sum = 7449 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c154_ss0 : ((List.range' 0 34).map fun i => sSmin ((c154.2.getD i default).r.arcs (pathPin (c154.2.getD i default)))).sum = 18593 := by decide +kernel

end Formal.Cells.BigCertPS
