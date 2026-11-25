import Formal.Cells.BigCertPS.C144_R0
import Formal.Cells.BigCertPS.C144_R1
import Formal.Cells.BigCertPS.C144_R2
import Formal.Cells.BigCertPS.C144_R3

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertRaceAll Formal.Cells.CertSwitchAll Formal.Cells.CertSplit Formal.Cells.CertMarginPS Formal.Cells.RaceCornersPS

theorem c144_krow : (List.range' 0 c144.2.length).all (fun i => krowOK (c144.2.getD i default).r) = true := (all_range'_append _ 0 78 1 (all_range'_append _ 0 24 54 (all_range'_append _ 0 4 20 c144_k0 c144_k1) c144_k2) c144_k3)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c144_labs : (List.range c144.2.length).all (fun i => labOK c144.1 c144.2 i (c144.2.getD i default)) = true := by decide +kernel

theorem c144_cert : certOK c144.1 c144.2 = true := certOK_of_split _ _ c144_krow c144_labs

theorem c144_sf : ((List.range' 0 c144.2.length).map fun i => sFmin ((c144.2.getD i default).r.arcs (pathPin (c144.2.getD i default)))).sum = 18995 := (sum_block _ 0 78 1 _ _ (sum_block _ 0 24 54 _ _ (sum_block _ 0 4 20 _ _ c144_sf0 c144_sf1) c144_sf2) c144_sf3)

theorem c144_ss : ((List.range' 0 c144.2.length).map fun i => sSmin ((c144.2.getD i default).r.arcs (pathPin (c144.2.getD i default)))).sum = 46770 := (sum_block _ 0 78 1 _ _ (sum_block _ 0 24 54 _ _ (sum_block _ 0 4 20 _ _ c144_ss0 c144_ss1) c144_ss2) c144_ss3)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c144_race : raceOK c144_sw.rr = true := raceOK_of_split c144_sw.rr _ _ c144_sf c144_ss (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c144_swok : swOK c144_sw = true := by decide +kernel

theorem c144_full : certOK c144_sw.rr.pc.1 c144_sw.rr.pc.2 = true ∧ raceOK c144_sw.rr = true ∧ swOK c144_sw = true :=
  ⟨c144_cert, c144_race, c144_swok⟩

end Formal.Cells.BigCertPS
