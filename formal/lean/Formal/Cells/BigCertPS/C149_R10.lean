import Formal.Cells.BigCertPS.C149

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c149_k10 : (List.range' 103 1).all (fun i => krowOK (c149.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c149_sf10 : ((List.range' 103 1).map fun i => sFmin ((c149.2.getD i default).r.arcs (pathPin (c149.2.getD i default)))).sum = 422 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c149_ss10 : ((List.range' 103 1).map fun i => sSmin ((c149.2.getD i default).r.arcs (pathPin (c149.2.getD i default)))).sum = 1039 := by decide +kernel

end Formal.Cells.BigCertPS
