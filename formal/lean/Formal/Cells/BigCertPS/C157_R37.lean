import Formal.Cells.BigCertPS.C157

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c157_k37 : (List.range' 172 4).all (fun i => krowOK (c157.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c157_sf37 : ((List.range' 172 4).map fun i => sFmin ((c157.2.getD i default).r.arcs (pathPin (c157.2.getD i default)))).sum = 656 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c157_ss37 : ((List.range' 172 4).map fun i => sSmin ((c157.2.getD i default).r.arcs (pathPin (c157.2.getD i default)))).sum = 1668 := by decide +kernel

end Formal.Cells.BigCertPS
