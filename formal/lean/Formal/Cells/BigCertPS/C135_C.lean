import Formal.Cells.BigCertPS.C135_R0
import Formal.Cells.BigCertPS.C135_R1
import Formal.Cells.BigCertPS.C135_R2
import Formal.Cells.BigCertPS.C135_R3
import Formal.Cells.BigCertPS.C135_R4
import Formal.Cells.BigCertPS.C135_R5
import Formal.Cells.BigCertPS.C135_R6

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertRaceAll Formal.Cells.CertSwitchAll Formal.Cells.CertSplit Formal.Cells.CertMarginPS Formal.Cells.RaceCornersPS

theorem c135_krow : (List.range' 0 c135.2.length).all (fun i => krowOK (c135.2.getD i default).r) = true := (all_range'_append _ 0 50 2 (all_range'_append _ 0 37 13 (all_range'_append _ 0 26 11 (all_range'_append _ 0 21 5 (all_range'_append _ 0 17 4 (all_range'_append _ 0 15 2 c135_k0 c135_k1) c135_k2) c135_k3) c135_k4) c135_k5) c135_k6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c135_labs : (List.range c135.2.length).all (fun i => labOK c135.1 c135.2 i (c135.2.getD i default)) = true := by decide +kernel

theorem c135_cert : certOK c135.1 c135.2 = true := certOK_of_split _ _ c135_krow c135_labs

theorem c135_sf : ((List.range' 0 c135.2.length).map fun i => sFmin ((c135.2.getD i default).r.arcs (pathPin (c135.2.getD i default)))).sum = 15856 := (sum_block _ 0 50 2 _ _ (sum_block _ 0 37 13 _ _ (sum_block _ 0 26 11 _ _ (sum_block _ 0 21 5 _ _ (sum_block _ 0 17 4 _ _ (sum_block _ 0 15 2 _ _ c135_sf0 c135_sf1) c135_sf2) c135_sf3) c135_sf4) c135_sf5) c135_sf6)

theorem c135_ss : ((List.range' 0 c135.2.length).map fun i => sSmin ((c135.2.getD i default).r.arcs (pathPin (c135.2.getD i default)))).sum = 38786 := (sum_block _ 0 50 2 _ _ (sum_block _ 0 37 13 _ _ (sum_block _ 0 26 11 _ _ (sum_block _ 0 21 5 _ _ (sum_block _ 0 17 4 _ _ (sum_block _ 0 15 2 _ _ c135_ss0 c135_ss1) c135_ss2) c135_ss3) c135_ss4) c135_ss5) c135_ss6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c135_race : raceOK c135_sw.rr = true := raceOK_of_split c135_sw.rr _ _ c135_sf c135_ss (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c135_swok : swOK c135_sw = true := by decide +kernel

theorem c135_full : certOK c135_sw.rr.pc.1 c135_sw.rr.pc.2 = true ∧ raceOK c135_sw.rr = true ∧ swOK c135_sw = true :=
  ⟨c135_cert, c135_race, c135_swok⟩

end Formal.Cells.BigCertPS
