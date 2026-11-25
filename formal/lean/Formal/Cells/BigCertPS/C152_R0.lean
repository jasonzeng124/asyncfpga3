import Formal.Cells.BigCertPS.C152

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c152_k0 : (List.range' 0 37).all (fun i => krowOK (c152.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c152_sf0 : ((List.range' 0 37).map fun i => sFmin ((c152.2.getD i default).r.arcs (pathPin (c152.2.getD i default)))).sum = 7410 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c152_ss0 : ((List.range' 0 37).map fun i => sSmin ((c152.2.getD i default).r.arcs (pathPin (c152.2.getD i default)))).sum = 18535 := by decide +kernel

end Formal.Cells.BigCertPS
