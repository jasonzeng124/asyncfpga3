import Formal.Cells.BigCertPS.C148

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c148_k14 : (List.range' 103 7).all (fun i => krowOK (c148.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c148_sf14 : ((List.range' 103 7).map fun i => sFmin ((c148.2.getD i default).r.arcs (pathPin (c148.2.getD i default)))).sum = 1278 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c148_ss14 : ((List.range' 103 7).map fun i => sSmin ((c148.2.getD i default).r.arcs (pathPin (c148.2.getD i default)))).sum = 3195 := by decide +kernel

end Formal.Cells.BigCertPS
