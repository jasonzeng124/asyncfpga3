import Formal.Cells.BigCertPS.C136

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c136_k1 : (List.range' 35 18).all (fun i => krowOK (c136.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c136_sf1 : ((List.range' 35 18).map fun i => sFmin ((c136.2.getD i default).r.arcs (pathPin (c136.2.getD i default)))).sum = 3607 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c136_ss1 : ((List.range' 35 18).map fun i => sSmin ((c136.2.getD i default).r.arcs (pathPin (c136.2.getD i default)))).sum = 9122 := by decide +kernel

end Formal.Cells.BigCertPS
