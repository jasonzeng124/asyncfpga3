import Formal.Cells.BigCertPS.C146

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c146_k0 : (List.range' 0 9).all (fun i => krowOK (c146.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c146_sf0 : ((List.range' 0 9).map fun i => sFmin ((c146.2.getD i default).r.arcs (pathPin (c146.2.getD i default)))).sum = 2869 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c146_ss0 : ((List.range' 0 9).map fun i => sSmin ((c146.2.getD i default).r.arcs (pathPin (c146.2.getD i default)))).sum = 6948 := by decide +kernel

end Formal.Cells.BigCertPS
