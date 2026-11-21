import Formal.Cells.BigCertPS.C148

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c148_k41 : (List.range' 159 1).all (fun i => krowOK (c148.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c148_sf41 : ((List.range' 159 1).map fun i => sFmin ((c148.2.getD i default).r.arcs (pathPin (c148.2.getD i default)))).sum = 167 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c148_ss41 : ((List.range' 159 1).map fun i => sSmin ((c148.2.getD i default).r.arcs (pathPin (c148.2.getD i default)))).sum = 422 := by decide +kernel

end Formal.Cells.BigCertPS
