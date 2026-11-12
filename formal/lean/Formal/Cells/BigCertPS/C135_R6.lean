import Formal.Cells.BigCertPS.C135

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c135_k6 : (List.range' 50 2).all (fun i => krowOK (c135.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c135_sf6 : ((List.range' 50 2).map fun i => sFmin ((c135.2.getD i default).r.arcs (pathPin (c135.2.getD i default)))).sum = 839 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c135_ss6 : ((List.range' 50 2).map fun i => sSmin ((c135.2.getD i default).r.arcs (pathPin (c135.2.getD i default)))).sum = 2012 := by decide +kernel

end Formal.Cells.BigCertPS
