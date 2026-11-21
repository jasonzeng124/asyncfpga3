import Formal.Cells.BigCertPS.C139

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c139_k1 : (List.range' 6 22).all (fun i => krowOK (c139.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c139_sf1 : ((List.range' 6 22).map fun i => sFmin ((c139.2.getD i default).r.arcs (pathPin (c139.2.getD i default)))).sum = 4912 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c139_ss1 : ((List.range' 6 22).map fun i => sSmin ((c139.2.getD i default).r.arcs (pathPin (c139.2.getD i default)))).sum = 12395 := by decide +kernel

end Formal.Cells.BigCertPS
