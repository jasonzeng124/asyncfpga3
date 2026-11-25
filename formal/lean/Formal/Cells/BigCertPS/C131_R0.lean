import Formal.Cells.BigCertPS.C131

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c131_k0 : (List.range' 0 10).all (fun i => krowOK (c131.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c131_sf0 : ((List.range' 0 10).map fun i => sFmin ((c131.2.getD i default).r.arcs (pathPin (c131.2.getD i default)))).sum = 3126 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c131_ss0 : ((List.range' 0 10).map fun i => sSmin ((c131.2.getD i default).r.arcs (pathPin (c131.2.getD i default)))).sum = 7583 := by decide +kernel

end Formal.Cells.BigCertPS
