import Formal.Cells.BigCertPS.C149_R0
import Formal.Cells.BigCertPS.C149_R1
import Formal.Cells.BigCertPS.C149_R2
import Formal.Cells.BigCertPS.C149_R3
import Formal.Cells.BigCertPS.C149_R4
import Formal.Cells.BigCertPS.C149_R5
import Formal.Cells.BigCertPS.C149_R6
import Formal.Cells.BigCertPS.C149_R7
import Formal.Cells.BigCertPS.C149_R8
import Formal.Cells.BigCertPS.C149_R9
import Formal.Cells.BigCertPS.C149_R10
import Formal.Cells.BigCertPS.C149_R11
import Formal.Cells.BigCertPS.C149_R12

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertRaceAll Formal.Cells.CertSwitchAll Formal.Cells.CertSplit Formal.Cells.CertMarginPS Formal.Cells.RaceCornersPS

theorem c149_krow : (List.range' 0 c149.2.length).all (fun i => krowOK (c149.2.getD i default).r) = true := (all_range'_append _ 0 105 1 (all_range'_append _ 0 104 1 (all_range'_append _ 0 103 1 (all_range'_append _ 0 101 2 (all_range'_append _ 0 100 1 (all_range'_append _ 0 95 5 (all_range'_append _ 0 75 20 (all_range'_append _ 0 55 20 (all_range'_append _ 0 35 20 (all_range'_append _ 0 15 20 (all_range'_append _ 0 14 1 (all_range'_append _ 0 13 1 c149_k0 c149_k1) c149_k2) c149_k3) c149_k4) c149_k5) c149_k6) c149_k7) c149_k8) c149_k9) c149_k10) c149_k11) c149_k12)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c149_labs : (List.range c149.2.length).all (fun i => labOK c149.1 c149.2 i (c149.2.getD i default)) = true := by decide +kernel

theorem c149_cert : certOK c149.1 c149.2 = true := certOK_of_split _ _ c149_krow c149_labs

theorem c149_sf : ((List.range' 0 c149.2.length).map fun i => sFmin ((c149.2.getD i default).r.arcs (pathPin (c149.2.getD i default)))).sum = 23162 := (sum_block _ 0 105 1 _ _ (sum_block _ 0 104 1 _ _ (sum_block _ 0 103 1 _ _ (sum_block _ 0 101 2 _ _ (sum_block _ 0 100 1 _ _ (sum_block _ 0 95 5 _ _ (sum_block _ 0 75 20 _ _ (sum_block _ 0 55 20 _ _ (sum_block _ 0 35 20 _ _ (sum_block _ 0 15 20 _ _ (sum_block _ 0 14 1 _ _ (sum_block _ 0 13 1 _ _ c149_sf0 c149_sf1) c149_sf2) c149_sf3) c149_sf4) c149_sf5) c149_sf6) c149_sf7) c149_sf8) c149_sf9) c149_sf10) c149_sf11) c149_sf12)

theorem c149_ss : ((List.range' 0 c149.2.length).map fun i => sSmin ((c149.2.getD i default).r.arcs (pathPin (c149.2.getD i default)))).sum = 57568 := (sum_block _ 0 105 1 _ _ (sum_block _ 0 104 1 _ _ (sum_block _ 0 103 1 _ _ (sum_block _ 0 101 2 _ _ (sum_block _ 0 100 1 _ _ (sum_block _ 0 95 5 _ _ (sum_block _ 0 75 20 _ _ (sum_block _ 0 55 20 _ _ (sum_block _ 0 35 20 _ _ (sum_block _ 0 15 20 _ _ (sum_block _ 0 14 1 _ _ (sum_block _ 0 13 1 _ _ c149_ss0 c149_ss1) c149_ss2) c149_ss3) c149_ss4) c149_ss5) c149_ss6) c149_ss7) c149_ss8) c149_ss9) c149_ss10) c149_ss11) c149_ss12)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c149_race : raceOK c149_sw.rr = true := raceOK_of_split c149_sw.rr _ _ c149_sf c149_ss (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c149_swok : swOK c149_sw = true := by decide +kernel

theorem c149_full : certOK c149_sw.rr.pc.1 c149_sw.rr.pc.2 = true ∧ raceOK c149_sw.rr = true ∧ swOK c149_sw = true :=
  ⟨c149_cert, c149_race, c149_swok⟩

end Formal.Cells.BigCertPS
