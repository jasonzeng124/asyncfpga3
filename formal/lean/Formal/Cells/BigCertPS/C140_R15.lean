import Formal.Cells.BigCertPS.C140

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c140_k15 : (List.range' 33 1).all (fun i => krowOK (c140.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c140_sf15 : ((List.range' 33 1).map fun i => sFmin ((c140.2.getD i default).r.arcs (pathPin (c140.2.getD i default)))).sum = 406 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c140_ss15 : ((List.range' 33 1).map fun i => sSmin ((c140.2.getD i default).r.arcs (pathPin (c140.2.getD i default)))).sum = 1018 := by decide +kernel

end Formal.Cells.BigCertPS
