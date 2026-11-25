import Formal.Cells.BigCertPS.C156

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c156_k9 : (List.range' 42 4).all (fun i => krowOK (c156.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c156_sf9 : ((List.range' 42 4).map fun i => sFmin ((c156.2.getD i default).r.arcs (pathPin (c156.2.getD i default)))).sum = 1203 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c156_ss9 : ((List.range' 42 4).map fun i => sSmin ((c156.2.getD i default).r.arcs (pathPin (c156.2.getD i default)))).sum = 2947 := by decide +kernel

end Formal.Cells.BigCertPS
