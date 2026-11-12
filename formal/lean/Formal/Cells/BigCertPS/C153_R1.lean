import Formal.Cells.BigCertPS.C153

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c153_k1 : (List.range' 20 20).all (fun i => krowOK (c153.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c153_sf1 : ((List.range' 20 20).map fun i => sFmin ((c153.2.getD i default).r.arcs (pathPin (c153.2.getD i default)))).sum = 3408 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c153_ss1 : ((List.range' 20 20).map fun i => sSmin ((c153.2.getD i default).r.arcs (pathPin (c153.2.getD i default)))).sum = 8713 := by decide +kernel

end Formal.Cells.BigCertPS
