import Formal.Cells.BigCertPS.C151_R0
import Formal.Cells.BigCertPS.C151_R1
import Formal.Cells.BigCertPS.C151_R2
import Formal.Cells.BigCertPS.C151_R3
import Formal.Cells.BigCertPS.C151_R4
import Formal.Cells.BigCertPS.C151_R5
import Formal.Cells.BigCertPS.C151_R6
import Formal.Cells.BigCertPS.C151_R7
import Formal.Cells.BigCertPS.C151_R8
import Formal.Cells.BigCertPS.C151_R9
import Formal.Cells.BigCertPS.C151_R10
import Formal.Cells.BigCertPS.C151_R11
import Formal.Cells.BigCertPS.C151_R12
import Formal.Cells.BigCertPS.C151_R13
import Formal.Cells.BigCertPS.C151_R14
import Formal.Cells.BigCertPS.C151_R15
import Formal.Cells.BigCertPS.C151_R16
import Formal.Cells.BigCertPS.C151_R17
import Formal.Cells.BigCertPS.C151_R18
import Formal.Cells.BigCertPS.C151_R19
import Formal.Cells.BigCertPS.C151_R20
import Formal.Cells.BigCertPS.C151_R21
import Formal.Cells.BigCertPS.C151_R22
import Formal.Cells.BigCertPS.C151_R23
import Formal.Cells.BigCertPS.C151_R24
import Formal.Cells.BigCertPS.C151_R25
import Formal.Cells.BigCertPS.C151_R26
import Formal.Cells.BigCertPS.C151_R27
import Formal.Cells.BigCertPS.C151_R28
import Formal.Cells.BigCertPS.C151_R29
import Formal.Cells.BigCertPS.C151_R30
import Formal.Cells.BigCertPS.C151_R31
import Formal.Cells.BigCertPS.C151_R32
import Formal.Cells.BigCertPS.C151_R33
import Formal.Cells.BigCertPS.C151_R34
import Formal.Cells.BigCertPS.C151_R35
import Formal.Cells.BigCertPS.C151_R36
import Formal.Cells.BigCertPS.C151_R37
import Formal.Cells.BigCertPS.C151_R38
import Formal.Cells.BigCertPS.C151_R39
import Formal.Cells.BigCertPS.C151_R40
import Formal.Cells.BigCertPS.C151_R41
import Formal.Cells.BigCertPS.C151_R42
import Formal.Cells.BigCertPS.C151_R43
import Formal.Cells.BigCertPS.C151_R44
import Formal.Cells.BigCertPS.C151_R45
import Formal.Cells.BigCertPS.C151_R46

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertRaceAll Formal.Cells.CertSwitchAll Formal.Cells.CertSplit Formal.Cells.CertMarginPS Formal.Cells.RaceCornersPS

theorem c151_krow : (List.range' 0 c151.2.length).all (fun i => krowOK (c151.2.getD i default).r) = true := (all_range'_append _ 0 149 4 (all_range'_append _ 0 148 1 (all_range'_append _ 0 147 1 (all_range'_append _ 0 146 1 (all_range'_append _ 0 145 1 (all_range'_append _ 0 144 1 (all_range'_append _ 0 143 1 (all_range'_append _ 0 142 1 (all_range'_append _ 0 141 1 (all_range'_append _ 0 140 1 (all_range'_append _ 0 139 1 (all_range'_append _ 0 138 1 (all_range'_append _ 0 137 1 (all_range'_append _ 0 136 1 (all_range'_append _ 0 135 1 (all_range'_append _ 0 134 1 (all_range'_append _ 0 133 1 (all_range'_append _ 0 122 11 (all_range'_append _ 0 119 3 (all_range'_append _ 0 114 5 (all_range'_append _ 0 113 1 (all_range'_append _ 0 112 1 (all_range'_append _ 0 111 1 (all_range'_append _ 0 110 1 (all_range'_append _ 0 109 1 (all_range'_append _ 0 108 1 (all_range'_append _ 0 107 1 (all_range'_append _ 0 106 1 (all_range'_append _ 0 105 1 (all_range'_append _ 0 104 1 (all_range'_append _ 0 103 1 (all_range'_append _ 0 102 1 (all_range'_append _ 0 101 1 (all_range'_append _ 0 100 1 (all_range'_append _ 0 98 2 (all_range'_append _ 0 91 7 (all_range'_append _ 0 84 7 (all_range'_append _ 0 80 4 (all_range'_append _ 0 71 9 (all_range'_append _ 0 62 9 (all_range'_append _ 0 24 38 (all_range'_append _ 0 23 1 (all_range'_append _ 0 22 1 (all_range'_append _ 0 20 2 (all_range'_append _ 0 14 6 (all_range'_append _ 0 13 1 c151_k0 c151_k1) c151_k2) c151_k3) c151_k4) c151_k5) c151_k6) c151_k7) c151_k8) c151_k9) c151_k10) c151_k11) c151_k12) c151_k13) c151_k14) c151_k15) c151_k16) c151_k17) c151_k18) c151_k19) c151_k20) c151_k21) c151_k22) c151_k23) c151_k24) c151_k25) c151_k26) c151_k27) c151_k28) c151_k29) c151_k30) c151_k31) c151_k32) c151_k33) c151_k34) c151_k35) c151_k36) c151_k37) c151_k38) c151_k39) c151_k40) c151_k41) c151_k42) c151_k43) c151_k44) c151_k45) c151_k46)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c151_labs : (List.range c151.2.length).all (fun i => labOK c151.1 c151.2 i (c151.2.getD i default)) = true := by decide +kernel

theorem c151_cert : certOK c151.1 c151.2 = true := certOK_of_split _ _ c151_krow c151_labs

theorem c151_sf : ((List.range' 0 c151.2.length).map fun i => sFmin ((c151.2.getD i default).r.arcs (pathPin (c151.2.getD i default)))).sum = 36262 := (sum_block _ 0 149 4 _ _ (sum_block _ 0 148 1 _ _ (sum_block _ 0 147 1 _ _ (sum_block _ 0 146 1 _ _ (sum_block _ 0 145 1 _ _ (sum_block _ 0 144 1 _ _ (sum_block _ 0 143 1 _ _ (sum_block _ 0 142 1 _ _ (sum_block _ 0 141 1 _ _ (sum_block _ 0 140 1 _ _ (sum_block _ 0 139 1 _ _ (sum_block _ 0 138 1 _ _ (sum_block _ 0 137 1 _ _ (sum_block _ 0 136 1 _ _ (sum_block _ 0 135 1 _ _ (sum_block _ 0 134 1 _ _ (sum_block _ 0 133 1 _ _ (sum_block _ 0 122 11 _ _ (sum_block _ 0 119 3 _ _ (sum_block _ 0 114 5 _ _ (sum_block _ 0 113 1 _ _ (sum_block _ 0 112 1 _ _ (sum_block _ 0 111 1 _ _ (sum_block _ 0 110 1 _ _ (sum_block _ 0 109 1 _ _ (sum_block _ 0 108 1 _ _ (sum_block _ 0 107 1 _ _ (sum_block _ 0 106 1 _ _ (sum_block _ 0 105 1 _ _ (sum_block _ 0 104 1 _ _ (sum_block _ 0 103 1 _ _ (sum_block _ 0 102 1 _ _ (sum_block _ 0 101 1 _ _ (sum_block _ 0 100 1 _ _ (sum_block _ 0 98 2 _ _ (sum_block _ 0 91 7 _ _ (sum_block _ 0 84 7 _ _ (sum_block _ 0 80 4 _ _ (sum_block _ 0 71 9 _ _ (sum_block _ 0 62 9 _ _ (sum_block _ 0 24 38 _ _ (sum_block _ 0 23 1 _ _ (sum_block _ 0 22 1 _ _ (sum_block _ 0 20 2 _ _ (sum_block _ 0 14 6 _ _ (sum_block _ 0 13 1 _ _ c151_sf0 c151_sf1) c151_sf2) c151_sf3) c151_sf4) c151_sf5) c151_sf6) c151_sf7) c151_sf8) c151_sf9) c151_sf10) c151_sf11) c151_sf12) c151_sf13) c151_sf14) c151_sf15) c151_sf16) c151_sf17) c151_sf18) c151_sf19) c151_sf20) c151_sf21) c151_sf22) c151_sf23) c151_sf24) c151_sf25) c151_sf26) c151_sf27) c151_sf28) c151_sf29) c151_sf30) c151_sf31) c151_sf32) c151_sf33) c151_sf34) c151_sf35) c151_sf36) c151_sf37) c151_sf38) c151_sf39) c151_sf40) c151_sf41) c151_sf42) c151_sf43) c151_sf44) c151_sf45) c151_sf46)

theorem c151_ss : ((List.range' 0 c151.2.length).map fun i => sSmin ((c151.2.getD i default).r.arcs (pathPin (c151.2.getD i default)))).sum = 89961 := (sum_block _ 0 149 4 _ _ (sum_block _ 0 148 1 _ _ (sum_block _ 0 147 1 _ _ (sum_block _ 0 146 1 _ _ (sum_block _ 0 145 1 _ _ (sum_block _ 0 144 1 _ _ (sum_block _ 0 143 1 _ _ (sum_block _ 0 142 1 _ _ (sum_block _ 0 141 1 _ _ (sum_block _ 0 140 1 _ _ (sum_block _ 0 139 1 _ _ (sum_block _ 0 138 1 _ _ (sum_block _ 0 137 1 _ _ (sum_block _ 0 136 1 _ _ (sum_block _ 0 135 1 _ _ (sum_block _ 0 134 1 _ _ (sum_block _ 0 133 1 _ _ (sum_block _ 0 122 11 _ _ (sum_block _ 0 119 3 _ _ (sum_block _ 0 114 5 _ _ (sum_block _ 0 113 1 _ _ (sum_block _ 0 112 1 _ _ (sum_block _ 0 111 1 _ _ (sum_block _ 0 110 1 _ _ (sum_block _ 0 109 1 _ _ (sum_block _ 0 108 1 _ _ (sum_block _ 0 107 1 _ _ (sum_block _ 0 106 1 _ _ (sum_block _ 0 105 1 _ _ (sum_block _ 0 104 1 _ _ (sum_block _ 0 103 1 _ _ (sum_block _ 0 102 1 _ _ (sum_block _ 0 101 1 _ _ (sum_block _ 0 100 1 _ _ (sum_block _ 0 98 2 _ _ (sum_block _ 0 91 7 _ _ (sum_block _ 0 84 7 _ _ (sum_block _ 0 80 4 _ _ (sum_block _ 0 71 9 _ _ (sum_block _ 0 62 9 _ _ (sum_block _ 0 24 38 _ _ (sum_block _ 0 23 1 _ _ (sum_block _ 0 22 1 _ _ (sum_block _ 0 20 2 _ _ (sum_block _ 0 14 6 _ _ (sum_block _ 0 13 1 _ _ c151_ss0 c151_ss1) c151_ss2) c151_ss3) c151_ss4) c151_ss5) c151_ss6) c151_ss7) c151_ss8) c151_ss9) c151_ss10) c151_ss11) c151_ss12) c151_ss13) c151_ss14) c151_ss15) c151_ss16) c151_ss17) c151_ss18) c151_ss19) c151_ss20) c151_ss21) c151_ss22) c151_ss23) c151_ss24) c151_ss25) c151_ss26) c151_ss27) c151_ss28) c151_ss29) c151_ss30) c151_ss31) c151_ss32) c151_ss33) c151_ss34) c151_ss35) c151_ss36) c151_ss37) c151_ss38) c151_ss39) c151_ss40) c151_ss41) c151_ss42) c151_ss43) c151_ss44) c151_ss45) c151_ss46)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c151_race : raceOK c151_sw.rr = true := raceOK_of_split c151_sw.rr _ _ c151_sf c151_ss (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c151_swok : swOK c151_sw = true := by decide +kernel

theorem c151_full : certOK c151_sw.rr.pc.1 c151_sw.rr.pc.2 = true ∧ raceOK c151_sw.rr = true ∧ swOK c151_sw = true :=
  ⟨c151_cert, c151_race, c151_swok⟩

end Formal.Cells.BigCertPS
