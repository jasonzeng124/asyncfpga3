import Formal.Cells.BigCertPS.C152

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c152_k2 : (List.range' 39 14).all (fun i => krowOK (c152.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c152_sf2 : ((List.range' 39 14).map fun i => sFmin ((c152.2.getD i default).r.arcs (pathPin (c152.2.getD i default)))).sum = 3806 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c152_ss2 : ((List.range' 39 14).map fun i => sSmin ((c152.2.getD i default).r.arcs (pathPin (c152.2.getD i default)))).sum = 9299 := by decide +kernel

end Formal.Cells.BigCertPS
