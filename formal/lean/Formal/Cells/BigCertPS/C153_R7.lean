import Formal.Cells.BigCertPS.C153

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c153_k7 : (List.range' 97 1).all (fun i => krowOK (c153.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c153_sf7 : ((List.range' 97 1).map fun i => sFmin ((c153.2.getD i default).r.arcs (pathPin (c153.2.getD i default)))).sum = 413 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c153_ss7 : ((List.range' 97 1).map fun i => sSmin ((c153.2.getD i default).r.arcs (pathPin (c153.2.getD i default)))).sum = 1004 := by decide +kernel

end Formal.Cells.BigCertPS
