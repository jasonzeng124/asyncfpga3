import Formal.Cells.BigCertPS.C157

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c157_k14 : (List.range' 107 20).all (fun i => krowOK (c157.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c157_sf14 : ((List.range' 107 20).map fun i => sFmin ((c157.2.getD i default).r.arcs (pathPin (c157.2.getD i default)))).sum = 4319 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c157_ss14 : ((List.range' 107 20).map fun i => sSmin ((c157.2.getD i default).r.arcs (pathPin (c157.2.getD i default)))).sum = 10651 := by decide +kernel

end Formal.Cells.BigCertPS
