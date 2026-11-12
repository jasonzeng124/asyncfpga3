import Formal.Cells.BigCertPS.C147_R0
import Formal.Cells.BigCertPS.C147_R1
import Formal.Cells.BigCertPS.C147_R2
import Formal.Cells.BigCertPS.C147_R3
import Formal.Cells.BigCertPS.C147_R4
import Formal.Cells.BigCertPS.C147_R5

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertRaceAll Formal.Cells.CertSwitchAll Formal.Cells.CertSplit Formal.Cells.CertMarginPS Formal.Cells.RaceCornersPS

theorem c147_krow : (List.range' 0 c147.2.length).all (fun i => krowOK (c147.2.getD i default).r) = true := (all_range'_append _ 0 42 1 (all_range'_append _ 0 35 7 (all_range'_append _ 0 31 4 (all_range'_append _ 0 28 3 (all_range'_append _ 0 7 21 c147_k0 c147_k1) c147_k2) c147_k3) c147_k4) c147_k5)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c147_labs : (List.range c147.2.length).all (fun i => labOK c147.1 c147.2 i (c147.2.getD i default)) = true := by decide +kernel

theorem c147_cert : certOK c147.1 c147.2 = true := certOK_of_split _ _ c147_krow c147_labs

theorem c147_sf : ((List.range' 0 c147.2.length).map fun i => sFmin ((c147.2.getD i default).r.arcs (pathPin (c147.2.getD i default)))).sum = 13350 := (sum_block _ 0 42 1 _ _ (sum_block _ 0 35 7 _ _ (sum_block _ 0 31 4 _ _ (sum_block _ 0 28 3 _ _ (sum_block _ 0 7 21 _ _ c147_sf0 c147_sf1) c147_sf2) c147_sf3) c147_sf4) c147_sf5)

theorem c147_ss : ((List.range' 0 c147.2.length).map fun i => sSmin ((c147.2.getD i default).r.arcs (pathPin (c147.2.getD i default)))).sum = 32586 := (sum_block _ 0 42 1 _ _ (sum_block _ 0 35 7 _ _ (sum_block _ 0 31 4 _ _ (sum_block _ 0 28 3 _ _ (sum_block _ 0 7 21 _ _ c147_ss0 c147_ss1) c147_ss2) c147_ss3) c147_ss4) c147_ss5)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c147_race : raceOK c147_sw.rr = true := raceOK_of_split c147_sw.rr _ _ c147_sf c147_ss (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c147_swok : swOK c147_sw = true := by decide +kernel

theorem c147_full : certOK c147_sw.rr.pc.1 c147_sw.rr.pc.2 = true ∧ raceOK c147_sw.rr = true ∧ swOK c147_sw = true :=
  ⟨c147_cert, c147_race, c147_swok⟩

end Formal.Cells.BigCertPS
