import Formal.Cells.BigCertPS.C148

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c148_k0 : (List.range' 0 13).all (fun i => krowOK (c148.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c148_sf0 : ((List.range' 0 13).map fun i => sFmin ((c148.2.getD i default).r.arcs (pathPin (c148.2.getD i default)))).sum = 2386 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c148_ss0 : ((List.range' 0 13).map fun i => sSmin ((c148.2.getD i default).r.arcs (pathPin (c148.2.getD i default)))).sum = 6021 := by decide +kernel

end Formal.Cells.BigCertPS
