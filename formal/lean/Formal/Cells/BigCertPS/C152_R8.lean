import Formal.Cells.BigCertPS.C152

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c152_k8 : (List.range' 92 17).all (fun i => krowOK (c152.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c152_sf8 : ((List.range' 92 17).map fun i => sFmin ((c152.2.getD i default).r.arcs (pathPin (c152.2.getD i default)))).sum = 3580 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c152_ss8 : ((List.range' 92 17).map fun i => sSmin ((c152.2.getD i default).r.arcs (pathPin (c152.2.getD i default)))).sum = 9033 := by decide +kernel

end Formal.Cells.BigCertPS
