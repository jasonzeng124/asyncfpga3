import Formal.Cells.BigCertPS.C146

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c146_k4 : (List.range' 37 2).all (fun i => krowOK (c146.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c146_sf4 : ((List.range' 37 2).map fun i => sFmin ((c146.2.getD i default).r.arcs (pathPin (c146.2.getD i default)))).sum = 689 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c146_ss4 : ((List.range' 37 2).map fun i => sSmin ((c146.2.getD i default).r.arcs (pathPin (c146.2.getD i default)))).sum = 1703 := by decide +kernel

end Formal.Cells.BigCertPS
