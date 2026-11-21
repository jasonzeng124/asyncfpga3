import Formal.Cells.BigCertPS.C135

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c135_k2 : (List.range' 17 4).all (fun i => krowOK (c135.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c135_sf2 : ((List.range' 17 4).map fun i => sFmin ((c135.2.getD i default).r.arcs (pathPin (c135.2.getD i default)))).sum = 1155 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c135_ss2 : ((List.range' 17 4).map fun i => sSmin ((c135.2.getD i default).r.arcs (pathPin (c135.2.getD i default)))).sum = 2816 := by decide +kernel

end Formal.Cells.BigCertPS
