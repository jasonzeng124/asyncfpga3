import Formal.Cells.BigCertPS.C147

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c147_k0 : (List.range' 0 7).all (fun i => krowOK (c147.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c147_sf0 : ((List.range' 0 7).map fun i => sFmin ((c147.2.getD i default).r.arcs (pathPin (c147.2.getD i default)))).sum = 2224 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c147_ss0 : ((List.range' 0 7).map fun i => sSmin ((c147.2.getD i default).r.arcs (pathPin (c147.2.getD i default)))).sum = 5470 := by decide +kernel

end Formal.Cells.BigCertPS
