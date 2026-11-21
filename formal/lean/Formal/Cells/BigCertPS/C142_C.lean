import Formal.Cells.BigCertPS.C142_R0
import Formal.Cells.BigCertPS.C142_R1
import Formal.Cells.BigCertPS.C142_R2
import Formal.Cells.BigCertPS.C142_R3
import Formal.Cells.BigCertPS.C142_R4

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertRaceAll Formal.Cells.CertSwitchAll Formal.Cells.CertSplit Formal.Cells.CertMarginPS Formal.Cells.RaceCornersPS

theorem c142_krow : (List.range' 0 c142.2.length).all (fun i => krowOK (c142.2.getD i default).r) = true := (all_range'_append _ 0 49 3 (all_range'_append _ 0 28 21 (all_range'_append _ 0 17 11 (all_range'_append _ 0 15 2 c142_k0 c142_k1) c142_k2) c142_k3) c142_k4)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c142_labs : (List.range c142.2.length).all (fun i => labOK c142.1 c142.2 i (c142.2.getD i default)) = true := by decide +kernel

theorem c142_cert : certOK c142.1 c142.2 = true := certOK_of_split _ _ c142_krow c142_labs

theorem c142_sf : ((List.range' 0 c142.2.length).map fun i => sFmin ((c142.2.getD i default).r.arcs (pathPin (c142.2.getD i default)))).sum = 15592 := (sum_block _ 0 49 3 _ _ (sum_block _ 0 28 21 _ _ (sum_block _ 0 17 11 _ _ (sum_block _ 0 15 2 _ _ c142_sf0 c142_sf1) c142_sf2) c142_sf3) c142_sf4)

theorem c142_ss : ((List.range' 0 c142.2.length).map fun i => sSmin ((c142.2.getD i default).r.arcs (pathPin (c142.2.getD i default)))).sum = 38167 := (sum_block _ 0 49 3 _ _ (sum_block _ 0 28 21 _ _ (sum_block _ 0 17 11 _ _ (sum_block _ 0 15 2 _ _ c142_ss0 c142_ss1) c142_ss2) c142_ss3) c142_ss4)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c142_race : raceOK c142_sw.rr = true := raceOK_of_split c142_sw.rr _ _ c142_sf c142_ss (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c142_swok : swOK c142_sw = true := by decide +kernel

theorem c142_full : certOK c142_sw.rr.pc.1 c142_sw.rr.pc.2 = true ∧ raceOK c142_sw.rr = true ∧ swOK c142_sw = true :=
  ⟨c142_cert, c142_race, c142_swok⟩

end Formal.Cells.BigCertPS
