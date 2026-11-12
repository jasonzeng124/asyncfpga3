import Formal.Cells.BigCertPS.C144

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.RaceCornersPS

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c144_k2 : (List.range' 24 54).all (fun i => krowOK (c144.2.getD i default).r) = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c144_sf2 : ((List.range' 24 54).map fun i => sFmin ((c144.2.getD i default).r.arcs (pathPin (c144.2.getD i default)))).sum = 11686 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c144_ss2 : ((List.range' 24 54).map fun i => sSmin ((c144.2.getD i default).r.arcs (pathPin (c144.2.getD i default)))).sum = 28909 := by decide +kernel

end Formal.Cells.BigCertPS
