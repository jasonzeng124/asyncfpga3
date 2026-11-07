import Formal.Cells.BigCertPS.C155_R0
import Formal.Cells.BigCertPS.C155_R1
import Formal.Cells.BigCertPS.C155_R2
import Formal.Cells.BigCertPS.C155_R3
import Formal.Cells.BigCertPS.C155_R4
import Formal.Cells.BigCertPS.C155_R5
import Formal.Cells.BigCertPS.C155_R6
import Formal.Cells.BigCertPS.C155_R7
import Formal.Cells.BigCertPS.C155_R8
import Formal.Cells.BigCertPS.C155_R9
import Formal.Cells.BigCertPS.C155_R10
import Formal.Cells.BigCertPS.C155_R11
import Formal.Cells.BigCertPS.C155_R12
import Formal.Cells.BigCertPS.C155_R13
import Formal.Cells.BigCertPS.C155_R14
import Formal.Cells.BigCertPS.C155_R15
import Formal.Cells.BigCertPS.C155_R16
import Formal.Cells.BigCertPS.C155_R17

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertRaceAll Formal.Cells.CertSwitchAll Formal.Cells.CertSplit Formal.Cells.CertMarginPS Formal.Cells.RaceCornersPS

theorem c155_krow : (List.range' 0 c155.2.length).all (fun i => krowOK (c155.2.getD i default).r) = true := (all_range'_append _ 0 124 1 (all_range'_append _ 0 122 2 (all_range'_append _ 0 121 1 (all_range'_append _ 0 120 1 (all_range'_append _ 0 118 2 (all_range'_append _ 0 98 20 (all_range'_append _ 0 78 20 (all_range'_append _ 0 58 20 (all_range'_append _ 0 38 20 (all_range'_append _ 0 35 3 (all_range'_append _ 0 34 1 (all_range'_append _ 0 33 1 (all_range'_append _ 0 20 13 (all_range'_append _ 0 19 1 (all_range'_append _ 0 15 4 (all_range'_append _ 0 14 1 (all_range'_append _ 0 1 13 c155_k0 c155_k1) c155_k2) c155_k3) c155_k4) c155_k5) c155_k6) c155_k7) c155_k8) c155_k9) c155_k10) c155_k11) c155_k12) c155_k13) c155_k14) c155_k15) c155_k16) c155_k17)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c155_labs : (List.range c155.2.length).all (fun i => labOK c155.1 c155.2 i (c155.2.getD i default)) = true := by decide +kernel

theorem c155_cert : certOK c155.1 c155.2 = true := certOK_of_split _ _ c155_krow c155_labs

theorem c155_sf : ((List.range' 0 c155.2.length).map fun i => sFmin ((c155.2.getD i default).r.arcs (pathPin (c155.2.getD i default)))).sum = 27386 := (sum_block _ 0 124 1 _ _ (sum_block _ 0 122 2 _ _ (sum_block _ 0 121 1 _ _ (sum_block _ 0 120 1 _ _ (sum_block _ 0 118 2 _ _ (sum_block _ 0 98 20 _ _ (sum_block _ 0 78 20 _ _ (sum_block _ 0 58 20 _ _ (sum_block _ 0 38 20 _ _ (sum_block _ 0 35 3 _ _ (sum_block _ 0 34 1 _ _ (sum_block _ 0 33 1 _ _ (sum_block _ 0 20 13 _ _ (sum_block _ 0 19 1 _ _ (sum_block _ 0 15 4 _ _ (sum_block _ 0 14 1 _ _ (sum_block _ 0 1 13 _ _ c155_sf0 c155_sf1) c155_sf2) c155_sf3) c155_sf4) c155_sf5) c155_sf6) c155_sf7) c155_sf8) c155_sf9) c155_sf10) c155_sf11) c155_sf12) c155_sf13) c155_sf14) c155_sf15) c155_sf16) c155_sf17)

theorem c155_ss : ((List.range' 0 c155.2.length).map fun i => sSmin ((c155.2.getD i default).r.arcs (pathPin (c155.2.getD i default)))).sum = 67959 := (sum_block _ 0 124 1 _ _ (sum_block _ 0 122 2 _ _ (sum_block _ 0 121 1 _ _ (sum_block _ 0 120 1 _ _ (sum_block _ 0 118 2 _ _ (sum_block _ 0 98 20 _ _ (sum_block _ 0 78 20 _ _ (sum_block _ 0 58 20 _ _ (sum_block _ 0 38 20 _ _ (sum_block _ 0 35 3 _ _ (sum_block _ 0 34 1 _ _ (sum_block _ 0 33 1 _ _ (sum_block _ 0 20 13 _ _ (sum_block _ 0 19 1 _ _ (sum_block _ 0 15 4 _ _ (sum_block _ 0 14 1 _ _ (sum_block _ 0 1 13 _ _ c155_ss0 c155_ss1) c155_ss2) c155_ss3) c155_ss4) c155_ss5) c155_ss6) c155_ss7) c155_ss8) c155_ss9) c155_ss10) c155_ss11) c155_ss12) c155_ss13) c155_ss14) c155_ss15) c155_ss16) c155_ss17)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c155_race : raceOK c155_sw.rr = true := raceOK_of_split c155_sw.rr _ _ c155_sf c155_ss (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c155_swok : swOK c155_sw = true := by decide +kernel

theorem c155_full : certOK c155_sw.rr.pc.1 c155_sw.rr.pc.2 = true ∧ raceOK c155_sw.rr = true ∧ swOK c155_sw = true :=
  ⟨c155_cert, c155_race, c155_swok⟩

end Formal.Cells.BigCertPS
