import Formal.Cells.BigCertPS.C146

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c146_k5 : (List.range' 39 1).all (fun i => krowOK (c146.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c146_sf5 : ((List.range' 39 1).map fun i => sFmin ((c146.2.getD i default).r.arcs (pathPin (c146.2.getD i default)))).sum = 562 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c146_ss5 : ((List.range' 39 1).map fun i => sSmin ((c146.2.getD i default).r.arcs (pathPin (c146.2.getD i default)))).sum = 1321 := by decide +kernel

end Formal.Cells.BigCertPS
