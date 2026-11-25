import Formal.Cells.BigCertPS.C155

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c155_k17 : (List.range' 124 1).all (fun i => krowOK (c155.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c155_sf17 : ((List.range' 124 1).map fun i => sFmin ((c155.2.getD i default).r.arcs (pathPin (c155.2.getD i default)))).sum = 374 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c155_ss17 : ((List.range' 124 1).map fun i => sSmin ((c155.2.getD i default).r.arcs (pathPin (c155.2.getD i default)))).sum = 890 := by decide +kernel

end Formal.Cells.BigCertPS
