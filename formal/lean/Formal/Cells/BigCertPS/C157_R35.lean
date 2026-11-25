import Formal.Cells.BigCertPS.C157

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c157_k35 : (List.range' 170 1).all (fun i => krowOK (c157.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c157_sf35 : ((List.range' 170 1).map fun i => sFmin ((c157.2.getD i default).r.arcs (pathPin (c157.2.getD i default)))).sum = 364 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c157_ss35 : ((List.range' 170 1).map fun i => sSmin ((c157.2.getD i default).r.arcs (pathPin (c157.2.getD i default)))).sum = 879 := by decide +kernel

end Formal.Cells.BigCertPS
