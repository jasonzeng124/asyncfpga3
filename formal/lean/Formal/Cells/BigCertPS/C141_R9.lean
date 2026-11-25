import Formal.Cells.BigCertPS.C141

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c141_k9 : (List.range' 55 20).all (fun i => krowOK (c141.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c141_sf9 : ((List.range' 55 20).map fun i => sFmin ((c141.2.getD i default).r.arcs (pathPin (c141.2.getD i default)))).sum = 3423 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c141_ss9 : ((List.range' 55 20).map fun i => sSmin ((c141.2.getD i default).r.arcs (pathPin (c141.2.getD i default)))).sum = 8657 := by decide +kernel

end Formal.Cells.BigCertPS
