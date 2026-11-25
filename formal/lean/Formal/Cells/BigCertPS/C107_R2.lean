import Formal.Cells.BigCertPS.C107

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c107_k2 : (List.range' 8 22).all (fun i => krowOK (c107.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c107_sf2 : ((List.range' 8 22).map fun i => sFmin ((c107.2.getD i default).r.arcs (pathPin (c107.2.getD i default)))).sum = 4912 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c107_ss2 : ((List.range' 8 22).map fun i => sSmin ((c107.2.getD i default).r.arcs (pathPin (c107.2.getD i default)))).sum = 12395 := by decide +kernel

end Formal.Cells.BigCertPS
