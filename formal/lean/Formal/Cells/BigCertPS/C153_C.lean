import Formal.Cells.BigCertPS.C153_R0
import Formal.Cells.BigCertPS.C153_R1
import Formal.Cells.BigCertPS.C153_R2
import Formal.Cells.BigCertPS.C153_R3
import Formal.Cells.BigCertPS.C153_R4
import Formal.Cells.BigCertPS.C153_R5
import Formal.Cells.BigCertPS.C153_R6
import Formal.Cells.BigCertPS.C153_R7

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertRaceAll Formal.Cells.CertSwitchAll Formal.Cells.CertSplit Formal.Cells.CertMarginPS Formal.Cells.RaceCornersPS

theorem c153_krow : (List.range' 0 c153.2.length).all (fun i => krowOK (c153.2.getD i default).r) = true := (all_range'_append _ 0 97 1 (all_range'_append _ 0 96 1 (all_range'_append _ 0 95 1 (all_range'_append _ 0 80 15 (all_range'_append _ 0 60 20 (all_range'_append _ 0 40 20 (all_range'_append _ 0 20 20 c153_k0 c153_k1) c153_k2) c153_k3) c153_k4) c153_k5) c153_k6) c153_k7)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c153_labs : (List.range c153.2.length).all (fun i => labOK c153.1 c153.2 i (c153.2.getD i default)) = true := by decide +kernel

theorem c153_cert : certOK c153.1 c153.2 = true := certOK_of_split _ _ c153_krow c153_labs

theorem c153_sf : ((List.range' 0 c153.2.length).map fun i => sFmin ((c153.2.getD i default).r.arcs (pathPin (c153.2.getD i default)))).sum = 19914 := (sum_block _ 0 97 1 _ _ (sum_block _ 0 96 1 _ _ (sum_block _ 0 95 1 _ _ (sum_block _ 0 80 15 _ _ (sum_block _ 0 60 20 _ _ (sum_block _ 0 40 20 _ _ (sum_block _ 0 20 20 _ _ c153_sf0 c153_sf1) c153_sf2) c153_sf3) c153_sf4) c153_sf5) c153_sf6) c153_sf7)

theorem c153_ss : ((List.range' 0 c153.2.length).map fun i => sSmin ((c153.2.getD i default).r.arcs (pathPin (c153.2.getD i default)))).sum = 50166 := (sum_block _ 0 97 1 _ _ (sum_block _ 0 96 1 _ _ (sum_block _ 0 95 1 _ _ (sum_block _ 0 80 15 _ _ (sum_block _ 0 60 20 _ _ (sum_block _ 0 40 20 _ _ (sum_block _ 0 20 20 _ _ c153_ss0 c153_ss1) c153_ss2) c153_ss3) c153_ss4) c153_ss5) c153_ss6) c153_ss7)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c153_race : raceOK c153_sw.rr = true := raceOK_of_split c153_sw.rr _ _ c153_sf c153_ss (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c153_swok : swOK c153_sw = true := by decide +kernel

theorem c153_full : certOK c153_sw.rr.pc.1 c153_sw.rr.pc.2 = true ∧ raceOK c153_sw.rr = true ∧ swOK c153_sw = true :=
  ⟨c153_cert, c153_race, c153_swok⟩

end Formal.Cells.BigCertPS
