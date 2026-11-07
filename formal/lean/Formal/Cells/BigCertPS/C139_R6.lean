import Formal.Cells.BigCertPS.C139

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c139_k6 : (List.range' 46 1).all (fun i => krowOK (c139.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c139_sf6 : ((List.range' 46 1).map fun i => sFmin ((c139.2.getD i default).r.arcs (pathPin (c139.2.getD i default)))).sum = 523 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c139_ss6 : ((List.range' 46 1).map fun i => sSmin ((c139.2.getD i default).r.arcs (pathPin (c139.2.getD i default)))).sum = 1260 := by decide +kernel

end Formal.Cells.BigCertPS
