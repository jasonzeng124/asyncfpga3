import Formal.Cells.BigCertPS.C136

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c136_k3 : (List.range' 94 6).all (fun i => krowOK (c136.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c136_sf3 : ((List.range' 94 6).map fun i => sFmin ((c136.2.getD i default).r.arcs (pathPin (c136.2.getD i default)))).sum = 2752 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c136_ss3 : ((List.range' 94 6).map fun i => sSmin ((c136.2.getD i default).r.arcs (pathPin (c136.2.getD i default)))).sum = 6700 := by decide +kernel

end Formal.Cells.BigCertPS
