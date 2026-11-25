import Formal.Cells.BigCertPS.C149

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c149_k5 : (List.range' 55 20).all (fun i => krowOK (c149.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c149_sf5 : ((List.range' 55 20).map fun i => sFmin ((c149.2.getD i default).r.arcs (pathPin (c149.2.getD i default)))).sum = 3848 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c149_ss5 : ((List.range' 55 20).map fun i => sSmin ((c149.2.getD i default).r.arcs (pathPin (c149.2.getD i default)))).sum = 9589 := by decide +kernel

end Formal.Cells.BigCertPS
