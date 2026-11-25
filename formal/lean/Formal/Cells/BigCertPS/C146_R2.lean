import Formal.Cells.BigCertPS.C146

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c146_k2 : (List.range' 30 3).all (fun i => krowOK (c146.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c146_sf2 : ((List.range' 30 3).map fun i => sFmin ((c146.2.getD i default).r.arcs (pathPin (c146.2.getD i default)))).sum = 1722 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c146_ss2 : ((List.range' 30 3).map fun i => sSmin ((c146.2.getD i default).r.arcs (pathPin (c146.2.getD i default)))).sum = 4161 := by decide +kernel

end Formal.Cells.BigCertPS
