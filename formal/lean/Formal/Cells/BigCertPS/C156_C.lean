import Formal.Cells.BigCertPS.C156_R0
import Formal.Cells.BigCertPS.C156_R1
import Formal.Cells.BigCertPS.C156_R2
import Formal.Cells.BigCertPS.C156_R3
import Formal.Cells.BigCertPS.C156_R4
import Formal.Cells.BigCertPS.C156_R5
import Formal.Cells.BigCertPS.C156_R6
import Formal.Cells.BigCertPS.C156_R7
import Formal.Cells.BigCertPS.C156_R8
import Formal.Cells.BigCertPS.C156_R9
import Formal.Cells.BigCertPS.C156_R10
import Formal.Cells.BigCertPS.C156_R11
import Formal.Cells.BigCertPS.C156_R12
import Formal.Cells.BigCertPS.C156_R13
import Formal.Cells.BigCertPS.C156_R14
import Formal.Cells.BigCertPS.C156_R15
import Formal.Cells.BigCertPS.C156_R16
import Formal.Cells.BigCertPS.C156_R17
import Formal.Cells.BigCertPS.C156_R18
import Formal.Cells.BigCertPS.C156_R19
import Formal.Cells.BigCertPS.C156_R20
import Formal.Cells.BigCertPS.C156_R21
import Formal.Cells.BigCertPS.C156_R22
import Formal.Cells.BigCertPS.C156_R23
import Formal.Cells.BigCertPS.C156_R24
import Formal.Cells.BigCertPS.C156_R25
import Formal.Cells.BigCertPS.C156_R26
import Formal.Cells.BigCertPS.C156_R27
import Formal.Cells.BigCertPS.C156_R28
import Formal.Cells.BigCertPS.C156_R29
import Formal.Cells.BigCertPS.C156_R30

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertRaceAll Formal.Cells.CertSwitchAll Formal.Cells.CertSplit Formal.Cells.CertMarginPS Formal.Cells.RaceCornersPS

theorem c156_krow : (List.range' 0 c156.2.length).all (fun i => krowOK (c156.2.getD i default).r) = true := (all_range'_append _ 0 153 1 (all_range'_append _ 0 152 1 (all_range'_append _ 0 151 1 (all_range'_append _ 0 150 1 (all_range'_append _ 0 149 1 (all_range'_append _ 0 148 1 (all_range'_append _ 0 147 1 (all_range'_append _ 0 145 2 (all_range'_append _ 0 138 7 (all_range'_append _ 0 131 7 (all_range'_append _ 0 127 4 (all_range'_append _ 0 118 9 (all_range'_append _ 0 109 9 (all_range'_append _ 0 71 38 (all_range'_append _ 0 70 1 (all_range'_append _ 0 69 1 (all_range'_append _ 0 67 2 (all_range'_append _ 0 61 6 (all_range'_append _ 0 60 1 (all_range'_append _ 0 47 13 (all_range'_append _ 0 46 1 (all_range'_append _ 0 42 4 (all_range'_append _ 0 41 1 (all_range'_append _ 0 28 13 (all_range'_append _ 0 27 1 (all_range'_append _ 0 23 4 (all_range'_append _ 0 18 5 (all_range'_append _ 0 15 3 (all_range'_append _ 0 14 1 (all_range'_append _ 0 1 13 c156_k0 c156_k1) c156_k2) c156_k3) c156_k4) c156_k5) c156_k6) c156_k7) c156_k8) c156_k9) c156_k10) c156_k11) c156_k12) c156_k13) c156_k14) c156_k15) c156_k16) c156_k17) c156_k18) c156_k19) c156_k20) c156_k21) c156_k22) c156_k23) c156_k24) c156_k25) c156_k26) c156_k27) c156_k28) c156_k29) c156_k30)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c156_labs : (List.range c156.2.length).all (fun i => labOK c156.1 c156.2 i (c156.2.getD i default)) = true := by decide +kernel

theorem c156_cert : certOK c156.1 c156.2 = true := certOK_of_split _ _ c156_krow c156_labs

theorem c156_sf : ((List.range' 0 c156.2.length).map fun i => sFmin ((c156.2.getD i default).r.arcs (pathPin (c156.2.getD i default)))).sum = 32955 := (sum_block _ 0 153 1 _ _ (sum_block _ 0 152 1 _ _ (sum_block _ 0 151 1 _ _ (sum_block _ 0 150 1 _ _ (sum_block _ 0 149 1 _ _ (sum_block _ 0 148 1 _ _ (sum_block _ 0 147 1 _ _ (sum_block _ 0 145 2 _ _ (sum_block _ 0 138 7 _ _ (sum_block _ 0 131 7 _ _ (sum_block _ 0 127 4 _ _ (sum_block _ 0 118 9 _ _ (sum_block _ 0 109 9 _ _ (sum_block _ 0 71 38 _ _ (sum_block _ 0 70 1 _ _ (sum_block _ 0 69 1 _ _ (sum_block _ 0 67 2 _ _ (sum_block _ 0 61 6 _ _ (sum_block _ 0 60 1 _ _ (sum_block _ 0 47 13 _ _ (sum_block _ 0 46 1 _ _ (sum_block _ 0 42 4 _ _ (sum_block _ 0 41 1 _ _ (sum_block _ 0 28 13 _ _ (sum_block _ 0 27 1 _ _ (sum_block _ 0 23 4 _ _ (sum_block _ 0 18 5 _ _ (sum_block _ 0 15 3 _ _ (sum_block _ 0 14 1 _ _ (sum_block _ 0 1 13 _ _ c156_sf0 c156_sf1) c156_sf2) c156_sf3) c156_sf4) c156_sf5) c156_sf6) c156_sf7) c156_sf8) c156_sf9) c156_sf10) c156_sf11) c156_sf12) c156_sf13) c156_sf14) c156_sf15) c156_sf16) c156_sf17) c156_sf18) c156_sf19) c156_sf20) c156_sf21) c156_sf22) c156_sf23) c156_sf24) c156_sf25) c156_sf26) c156_sf27) c156_sf28) c156_sf29) c156_sf30)

theorem c156_ss : ((List.range' 0 c156.2.length).map fun i => sSmin ((c156.2.getD i default).r.arcs (pathPin (c156.2.getD i default)))).sum = 82279 := (sum_block _ 0 153 1 _ _ (sum_block _ 0 152 1 _ _ (sum_block _ 0 151 1 _ _ (sum_block _ 0 150 1 _ _ (sum_block _ 0 149 1 _ _ (sum_block _ 0 148 1 _ _ (sum_block _ 0 147 1 _ _ (sum_block _ 0 145 2 _ _ (sum_block _ 0 138 7 _ _ (sum_block _ 0 131 7 _ _ (sum_block _ 0 127 4 _ _ (sum_block _ 0 118 9 _ _ (sum_block _ 0 109 9 _ _ (sum_block _ 0 71 38 _ _ (sum_block _ 0 70 1 _ _ (sum_block _ 0 69 1 _ _ (sum_block _ 0 67 2 _ _ (sum_block _ 0 61 6 _ _ (sum_block _ 0 60 1 _ _ (sum_block _ 0 47 13 _ _ (sum_block _ 0 46 1 _ _ (sum_block _ 0 42 4 _ _ (sum_block _ 0 41 1 _ _ (sum_block _ 0 28 13 _ _ (sum_block _ 0 27 1 _ _ (sum_block _ 0 23 4 _ _ (sum_block _ 0 18 5 _ _ (sum_block _ 0 15 3 _ _ (sum_block _ 0 14 1 _ _ (sum_block _ 0 1 13 _ _ c156_ss0 c156_ss1) c156_ss2) c156_ss3) c156_ss4) c156_ss5) c156_ss6) c156_ss7) c156_ss8) c156_ss9) c156_ss10) c156_ss11) c156_ss12) c156_ss13) c156_ss14) c156_ss15) c156_ss16) c156_ss17) c156_ss18) c156_ss19) c156_ss20) c156_ss21) c156_ss22) c156_ss23) c156_ss24) c156_ss25) c156_ss26) c156_ss27) c156_ss28) c156_ss29) c156_ss30)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c156_race : raceOK c156_sw.rr = true := raceOK_of_split c156_sw.rr _ _ c156_sf c156_ss (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c156_swok : swOK c156_sw = true := by decide +kernel

theorem c156_full : certOK c156_sw.rr.pc.1 c156_sw.rr.pc.2 = true ∧ raceOK c156_sw.rr = true ∧ swOK c156_sw = true :=
  ⟨c156_cert, c156_race, c156_swok⟩

end Formal.Cells.BigCertPS
