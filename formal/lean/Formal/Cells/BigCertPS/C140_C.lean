import Formal.Cells.BigCertPS.C140_R0
import Formal.Cells.BigCertPS.C140_R1
import Formal.Cells.BigCertPS.C140_R2
import Formal.Cells.BigCertPS.C140_R3
import Formal.Cells.BigCertPS.C140_R4
import Formal.Cells.BigCertPS.C140_R5
import Formal.Cells.BigCertPS.C140_R6
import Formal.Cells.BigCertPS.C140_R7
import Formal.Cells.BigCertPS.C140_R8
import Formal.Cells.BigCertPS.C140_R9
import Formal.Cells.BigCertPS.C140_R10
import Formal.Cells.BigCertPS.C140_R11
import Formal.Cells.BigCertPS.C140_R12
import Formal.Cells.BigCertPS.C140_R13
import Formal.Cells.BigCertPS.C140_R14
import Formal.Cells.BigCertPS.C140_R15
import Formal.Cells.BigCertPS.C140_R16
import Formal.Cells.BigCertPS.C140_R17
import Formal.Cells.BigCertPS.C140_R18
import Formal.Cells.BigCertPS.C140_R19
import Formal.Cells.BigCertPS.C140_R20
import Formal.Cells.BigCertPS.C140_R21
import Formal.Cells.BigCertPS.C140_R22
import Formal.Cells.BigCertPS.C140_R23
import Formal.Cells.BigCertPS.C140_R24
import Formal.Cells.BigCertPS.C140_R25
import Formal.Cells.BigCertPS.C140_R26
import Formal.Cells.BigCertPS.C140_R27
import Formal.Cells.BigCertPS.C140_R28
import Formal.Cells.BigCertPS.C140_R29
import Formal.Cells.BigCertPS.C140_R30
import Formal.Cells.BigCertPS.C140_R31

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertRaceAll Formal.Cells.CertSwitchAll Formal.Cells.CertSplit Formal.Cells.CertMarginPS Formal.Cells.RaceCornersPS

theorem c140_krow : (List.range' 0 c140.2.length).all (fun i => krowOK (c140.2.getD i default).r) = true := (all_range'_append _ 0 124 1 (all_range'_append _ 0 123 1 (all_range'_append _ 0 122 1 (all_range'_append _ 0 121 1 (all_range'_append _ 0 120 1 (all_range'_append _ 0 118 2 (all_range'_append _ 0 111 7 (all_range'_append _ 0 104 7 (all_range'_append _ 0 100 4 (all_range'_append _ 0 91 9 (all_range'_append _ 0 82 9 (all_range'_append _ 0 44 38 (all_range'_append _ 0 43 1 (all_range'_append _ 0 42 1 (all_range'_append _ 0 40 2 (all_range'_append _ 0 34 6 (all_range'_append _ 0 33 1 (all_range'_append _ 0 20 13 (all_range'_append _ 0 19 1 (all_range'_append _ 0 15 4 (all_range'_append _ 0 14 1 (all_range'_append _ 0 11 3 (all_range'_append _ 0 10 1 (all_range'_append _ 0 9 1 (all_range'_append _ 0 8 1 (all_range'_append _ 0 7 1 (all_range'_append _ 0 6 1 (all_range'_append _ 0 5 1 (all_range'_append _ 0 4 1 (all_range'_append _ 0 3 1 (all_range'_append _ 0 1 2 c140_k0 c140_k1) c140_k2) c140_k3) c140_k4) c140_k5) c140_k6) c140_k7) c140_k8) c140_k9) c140_k10) c140_k11) c140_k12) c140_k13) c140_k14) c140_k15) c140_k16) c140_k17) c140_k18) c140_k19) c140_k20) c140_k21) c140_k22) c140_k23) c140_k24) c140_k25) c140_k26) c140_k27) c140_k28) c140_k29) c140_k30) c140_k31)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c140_labs : (List.range c140.2.length).all (fun i => labOK c140.1 c140.2 i (c140.2.getD i default)) = true := by decide +kernel

theorem c140_cert : certOK c140.1 c140.2 = true := certOK_of_split _ _ c140_krow c140_labs

theorem c140_sf : ((List.range' 0 c140.2.length).map fun i => sFmin ((c140.2.getD i default).r.arcs (pathPin (c140.2.getD i default)))).sum = 26147 := (sum_block _ 0 124 1 _ _ (sum_block _ 0 123 1 _ _ (sum_block _ 0 122 1 _ _ (sum_block _ 0 121 1 _ _ (sum_block _ 0 120 1 _ _ (sum_block _ 0 118 2 _ _ (sum_block _ 0 111 7 _ _ (sum_block _ 0 104 7 _ _ (sum_block _ 0 100 4 _ _ (sum_block _ 0 91 9 _ _ (sum_block _ 0 82 9 _ _ (sum_block _ 0 44 38 _ _ (sum_block _ 0 43 1 _ _ (sum_block _ 0 42 1 _ _ (sum_block _ 0 40 2 _ _ (sum_block _ 0 34 6 _ _ (sum_block _ 0 33 1 _ _ (sum_block _ 0 20 13 _ _ (sum_block _ 0 19 1 _ _ (sum_block _ 0 15 4 _ _ (sum_block _ 0 14 1 _ _ (sum_block _ 0 11 3 _ _ (sum_block _ 0 10 1 _ _ (sum_block _ 0 9 1 _ _ (sum_block _ 0 8 1 _ _ (sum_block _ 0 7 1 _ _ (sum_block _ 0 6 1 _ _ (sum_block _ 0 5 1 _ _ (sum_block _ 0 4 1 _ _ (sum_block _ 0 3 1 _ _ (sum_block _ 0 1 2 _ _ c140_sf0 c140_sf1) c140_sf2) c140_sf3) c140_sf4) c140_sf5) c140_sf6) c140_sf7) c140_sf8) c140_sf9) c140_sf10) c140_sf11) c140_sf12) c140_sf13) c140_sf14) c140_sf15) c140_sf16) c140_sf17) c140_sf18) c140_sf19) c140_sf20) c140_sf21) c140_sf22) c140_sf23) c140_sf24) c140_sf25) c140_sf26) c140_sf27) c140_sf28) c140_sf29) c140_sf30) c140_sf31)

theorem c140_ss : ((List.range' 0 c140.2.length).map fun i => sSmin ((c140.2.getD i default).r.arcs (pathPin (c140.2.getD i default)))).sum = 65472 := (sum_block _ 0 124 1 _ _ (sum_block _ 0 123 1 _ _ (sum_block _ 0 122 1 _ _ (sum_block _ 0 121 1 _ _ (sum_block _ 0 120 1 _ _ (sum_block _ 0 118 2 _ _ (sum_block _ 0 111 7 _ _ (sum_block _ 0 104 7 _ _ (sum_block _ 0 100 4 _ _ (sum_block _ 0 91 9 _ _ (sum_block _ 0 82 9 _ _ (sum_block _ 0 44 38 _ _ (sum_block _ 0 43 1 _ _ (sum_block _ 0 42 1 _ _ (sum_block _ 0 40 2 _ _ (sum_block _ 0 34 6 _ _ (sum_block _ 0 33 1 _ _ (sum_block _ 0 20 13 _ _ (sum_block _ 0 19 1 _ _ (sum_block _ 0 15 4 _ _ (sum_block _ 0 14 1 _ _ (sum_block _ 0 11 3 _ _ (sum_block _ 0 10 1 _ _ (sum_block _ 0 9 1 _ _ (sum_block _ 0 8 1 _ _ (sum_block _ 0 7 1 _ _ (sum_block _ 0 6 1 _ _ (sum_block _ 0 5 1 _ _ (sum_block _ 0 4 1 _ _ (sum_block _ 0 3 1 _ _ (sum_block _ 0 1 2 _ _ c140_ss0 c140_ss1) c140_ss2) c140_ss3) c140_ss4) c140_ss5) c140_ss6) c140_ss7) c140_ss8) c140_ss9) c140_ss10) c140_ss11) c140_ss12) c140_ss13) c140_ss14) c140_ss15) c140_ss16) c140_ss17) c140_ss18) c140_ss19) c140_ss20) c140_ss21) c140_ss22) c140_ss23) c140_ss24) c140_ss25) c140_ss26) c140_ss27) c140_ss28) c140_ss29) c140_ss30) c140_ss31)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c140_race : raceOK c140_sw.rr = true := raceOK_of_split c140_sw.rr _ _ c140_sf c140_ss (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c140_swok : swOK c140_sw = true := by decide +kernel

theorem c140_full : certOK c140_sw.rr.pc.1 c140_sw.rr.pc.2 = true ∧ raceOK c140_sw.rr = true ∧ swOK c140_sw = true :=
  ⟨c140_cert, c140_race, c140_swok⟩

end Formal.Cells.BigCertPS
