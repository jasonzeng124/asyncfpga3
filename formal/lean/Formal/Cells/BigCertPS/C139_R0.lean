import Formal.Cells.BigCertPS.C139

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c139_k0 : (List.range' 0 6).all (fun i => krowOK (c139.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c139_sf0 : ((List.range' 0 6).map fun i => sFmin ((c139.2.getD i default).r.arcs (pathPin (c139.2.getD i default)))).sum = 1903 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c139_ss0 : ((List.range' 0 6).map fun i => sSmin ((c139.2.getD i default).r.arcs (pathPin (c139.2.getD i default)))).sum = 4637 := by decide +kernel

end Formal.Cells.BigCertPS
