import Formal.Cells.BigCertPS.C141_R0
import Formal.Cells.BigCertPS.C141_R1
import Formal.Cells.BigCertPS.C141_R2
import Formal.Cells.BigCertPS.C141_R3
import Formal.Cells.BigCertPS.C141_R4
import Formal.Cells.BigCertPS.C141_R5
import Formal.Cells.BigCertPS.C141_R6
import Formal.Cells.BigCertPS.C141_R7
import Formal.Cells.BigCertPS.C141_R8
import Formal.Cells.BigCertPS.C141_R9
import Formal.Cells.BigCertPS.C141_R10
import Formal.Cells.BigCertPS.C141_R11
import Formal.Cells.BigCertPS.C141_R12
import Formal.Cells.BigCertPS.C141_R13
import Formal.Cells.BigCertPS.C141_R14
import Formal.Cells.BigCertPS.C141_R15
import Formal.Cells.BigCertPS.C141_R16
import Formal.Cells.BigCertPS.C141_R17

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertRaceAll Formal.Cells.CertSwitchAll Formal.Cells.CertSplit Formal.Cells.CertMarginPS Formal.Cells.RaceCornersPS

theorem c141_krow : (List.range' 0 c141.2.length).all (fun i => krowOK (c141.2.getD i default).r) = true := (all_range'_append _ 0 124 1 (all_range'_append _ 0 123 1 (all_range'_append _ 0 122 1 (all_range'_append _ 0 121 1 (all_range'_append _ 0 120 1 (all_range'_append _ 0 115 5 (all_range'_append _ 0 95 20 (all_range'_append _ 0 75 20 (all_range'_append _ 0 55 20 (all_range'_append _ 0 35 20 (all_range'_append _ 0 34 1 (all_range'_append _ 0 33 1 (all_range'_append _ 0 20 13 (all_range'_append _ 0 19 1 (all_range'_append _ 0 15 4 (all_range'_append _ 0 14 1 (all_range'_append _ 0 1 13 c141_k0 c141_k1) c141_k2) c141_k3) c141_k4) c141_k5) c141_k6) c141_k7) c141_k8) c141_k9) c141_k10) c141_k11) c141_k12) c141_k13) c141_k14) c141_k15) c141_k16) c141_k17)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c141_labs : (List.range c141.2.length).all (fun i => labOK c141.1 c141.2 i (c141.2.getD i default)) = true := by decide +kernel

theorem c141_cert : certOK c141.1 c141.2 = true := certOK_of_split _ _ c141_krow c141_labs

theorem c141_sf : ((List.range' 0 c141.2.length).map fun i => sFmin ((c141.2.getD i default).r.arcs (pathPin (c141.2.getD i default)))).sum = 27178 := (sum_block _ 0 124 1 _ _ (sum_block _ 0 123 1 _ _ (sum_block _ 0 122 1 _ _ (sum_block _ 0 121 1 _ _ (sum_block _ 0 120 1 _ _ (sum_block _ 0 115 5 _ _ (sum_block _ 0 95 20 _ _ (sum_block _ 0 75 20 _ _ (sum_block _ 0 55 20 _ _ (sum_block _ 0 35 20 _ _ (sum_block _ 0 34 1 _ _ (sum_block _ 0 33 1 _ _ (sum_block _ 0 20 13 _ _ (sum_block _ 0 19 1 _ _ (sum_block _ 0 15 4 _ _ (sum_block _ 0 14 1 _ _ (sum_block _ 0 1 13 _ _ c141_sf0 c141_sf1) c141_sf2) c141_sf3) c141_sf4) c141_sf5) c141_sf6) c141_sf7) c141_sf8) c141_sf9) c141_sf10) c141_sf11) c141_sf12) c141_sf13) c141_sf14) c141_sf15) c141_sf16) c141_sf17)

theorem c141_ss : ((List.range' 0 c141.2.length).map fun i => sSmin ((c141.2.getD i default).r.arcs (pathPin (c141.2.getD i default)))).sum = 67472 := (sum_block _ 0 124 1 _ _ (sum_block _ 0 123 1 _ _ (sum_block _ 0 122 1 _ _ (sum_block _ 0 121 1 _ _ (sum_block _ 0 120 1 _ _ (sum_block _ 0 115 5 _ _ (sum_block _ 0 95 20 _ _ (sum_block _ 0 75 20 _ _ (sum_block _ 0 55 20 _ _ (sum_block _ 0 35 20 _ _ (sum_block _ 0 34 1 _ _ (sum_block _ 0 33 1 _ _ (sum_block _ 0 20 13 _ _ (sum_block _ 0 19 1 _ _ (sum_block _ 0 15 4 _ _ (sum_block _ 0 14 1 _ _ (sum_block _ 0 1 13 _ _ c141_ss0 c141_ss1) c141_ss2) c141_ss3) c141_ss4) c141_ss5) c141_ss6) c141_ss7) c141_ss8) c141_ss9) c141_ss10) c141_ss11) c141_ss12) c141_ss13) c141_ss14) c141_ss15) c141_ss16) c141_ss17)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c141_race : raceOK c141_sw.rr = true := raceOK_of_split c141_sw.rr _ _ c141_sf c141_ss (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c141_swok : swOK c141_sw = true := by decide +kernel

theorem c141_full : certOK c141_sw.rr.pc.1 c141_sw.rr.pc.2 = true ∧ raceOK c141_sw.rr = true ∧ swOK c141_sw = true :=
  ⟨c141_cert, c141_race, c141_swok⟩

end Formal.Cells.BigCertPS
