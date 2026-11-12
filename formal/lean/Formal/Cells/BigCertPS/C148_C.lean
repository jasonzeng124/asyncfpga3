import Formal.Cells.BigCertPS.C148_R0
import Formal.Cells.BigCertPS.C148_R1
import Formal.Cells.BigCertPS.C148_R2
import Formal.Cells.BigCertPS.C148_R3
import Formal.Cells.BigCertPS.C148_R4
import Formal.Cells.BigCertPS.C148_R5
import Formal.Cells.BigCertPS.C148_R6
import Formal.Cells.BigCertPS.C148_R7
import Formal.Cells.BigCertPS.C148_R8
import Formal.Cells.BigCertPS.C148_R9
import Formal.Cells.BigCertPS.C148_R10
import Formal.Cells.BigCertPS.C148_R11
import Formal.Cells.BigCertPS.C148_R12
import Formal.Cells.BigCertPS.C148_R13
import Formal.Cells.BigCertPS.C148_R14
import Formal.Cells.BigCertPS.C148_R15
import Formal.Cells.BigCertPS.C148_R16
import Formal.Cells.BigCertPS.C148_R17
import Formal.Cells.BigCertPS.C148_R18
import Formal.Cells.BigCertPS.C148_R19
import Formal.Cells.BigCertPS.C148_R20
import Formal.Cells.BigCertPS.C148_R21
import Formal.Cells.BigCertPS.C148_R22
import Formal.Cells.BigCertPS.C148_R23
import Formal.Cells.BigCertPS.C148_R24
import Formal.Cells.BigCertPS.C148_R25
import Formal.Cells.BigCertPS.C148_R26
import Formal.Cells.BigCertPS.C148_R27
import Formal.Cells.BigCertPS.C148_R28
import Formal.Cells.BigCertPS.C148_R29
import Formal.Cells.BigCertPS.C148_R30
import Formal.Cells.BigCertPS.C148_R31
import Formal.Cells.BigCertPS.C148_R32
import Formal.Cells.BigCertPS.C148_R33
import Formal.Cells.BigCertPS.C148_R34
import Formal.Cells.BigCertPS.C148_R35
import Formal.Cells.BigCertPS.C148_R36
import Formal.Cells.BigCertPS.C148_R37
import Formal.Cells.BigCertPS.C148_R38
import Formal.Cells.BigCertPS.C148_R39
import Formal.Cells.BigCertPS.C148_R40
import Formal.Cells.BigCertPS.C148_R41
import Formal.Cells.BigCertPS.C148_R42
import Formal.Cells.BigCertPS.C148_R43
import Formal.Cells.BigCertPS.C148_R44
import Formal.Cells.BigCertPS.C148_R45
import Formal.Cells.BigCertPS.C148_R46
import Formal.Cells.BigCertPS.C148_R47

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertRaceAll Formal.Cells.CertSwitchAll Formal.Cells.CertSplit Formal.Cells.CertMarginPS Formal.Cells.RaceCornersPS

theorem c148_krow : (List.range' 0 c148.2.length).all (fun i => krowOK (c148.2.getD i default).r) = true := (all_range'_append _ 0 167 1 (all_range'_append _ 0 164 3 (all_range'_append _ 0 163 1 (all_range'_append _ 0 162 1 (all_range'_append _ 0 161 1 (all_range'_append _ 0 160 1 (all_range'_append _ 0 159 1 (all_range'_append _ 0 158 1 (all_range'_append _ 0 157 1 (all_range'_append _ 0 156 1 (all_range'_append _ 0 155 1 (all_range'_append _ 0 154 1 (all_range'_append _ 0 153 1 (all_range'_append _ 0 152 1 (all_range'_append _ 0 141 11 (all_range'_append _ 0 138 3 (all_range'_append _ 0 133 5 (all_range'_append _ 0 132 1 (all_range'_append _ 0 131 1 (all_range'_append _ 0 130 1 (all_range'_append _ 0 129 1 (all_range'_append _ 0 128 1 (all_range'_append _ 0 127 1 (all_range'_append _ 0 126 1 (all_range'_append _ 0 125 1 (all_range'_append _ 0 124 1 (all_range'_append _ 0 123 1 (all_range'_append _ 0 122 1 (all_range'_append _ 0 121 1 (all_range'_append _ 0 120 1 (all_range'_append _ 0 119 1 (all_range'_append _ 0 117 2 (all_range'_append _ 0 110 7 (all_range'_append _ 0 103 7 (all_range'_append _ 0 99 4 (all_range'_append _ 0 90 9 (all_range'_append _ 0 81 9 (all_range'_append _ 0 43 38 (all_range'_append _ 0 42 1 (all_range'_append _ 0 41 1 (all_range'_append _ 0 39 2 (all_range'_append _ 0 33 6 (all_range'_append _ 0 32 1 (all_range'_append _ 0 19 13 (all_range'_append _ 0 18 1 (all_range'_append _ 0 14 4 (all_range'_append _ 0 13 1 c148_k0 c148_k1) c148_k2) c148_k3) c148_k4) c148_k5) c148_k6) c148_k7) c148_k8) c148_k9) c148_k10) c148_k11) c148_k12) c148_k13) c148_k14) c148_k15) c148_k16) c148_k17) c148_k18) c148_k19) c148_k20) c148_k21) c148_k22) c148_k23) c148_k24) c148_k25) c148_k26) c148_k27) c148_k28) c148_k29) c148_k30) c148_k31) c148_k32) c148_k33) c148_k34) c148_k35) c148_k36) c148_k37) c148_k38) c148_k39) c148_k40) c148_k41) c148_k42) c148_k43) c148_k44) c148_k45) c148_k46) c148_k47)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c148_labs : (List.range c148.2.length).all (fun i => labOK c148.1 c148.2 i (c148.2.getD i default)) = true := by decide +kernel

theorem c148_cert : certOK c148.1 c148.2 = true := certOK_of_split _ _ c148_krow c148_labs

theorem c148_sf : ((List.range' 0 c148.2.length).map fun i => sFmin ((c148.2.getD i default).r.arcs (pathPin (c148.2.getD i default)))).sum = 39795 := (sum_block _ 0 167 1 _ _ (sum_block _ 0 164 3 _ _ (sum_block _ 0 163 1 _ _ (sum_block _ 0 162 1 _ _ (sum_block _ 0 161 1 _ _ (sum_block _ 0 160 1 _ _ (sum_block _ 0 159 1 _ _ (sum_block _ 0 158 1 _ _ (sum_block _ 0 157 1 _ _ (sum_block _ 0 156 1 _ _ (sum_block _ 0 155 1 _ _ (sum_block _ 0 154 1 _ _ (sum_block _ 0 153 1 _ _ (sum_block _ 0 152 1 _ _ (sum_block _ 0 141 11 _ _ (sum_block _ 0 138 3 _ _ (sum_block _ 0 133 5 _ _ (sum_block _ 0 132 1 _ _ (sum_block _ 0 131 1 _ _ (sum_block _ 0 130 1 _ _ (sum_block _ 0 129 1 _ _ (sum_block _ 0 128 1 _ _ (sum_block _ 0 127 1 _ _ (sum_block _ 0 126 1 _ _ (sum_block _ 0 125 1 _ _ (sum_block _ 0 124 1 _ _ (sum_block _ 0 123 1 _ _ (sum_block _ 0 122 1 _ _ (sum_block _ 0 121 1 _ _ (sum_block _ 0 120 1 _ _ (sum_block _ 0 119 1 _ _ (sum_block _ 0 117 2 _ _ (sum_block _ 0 110 7 _ _ (sum_block _ 0 103 7 _ _ (sum_block _ 0 99 4 _ _ (sum_block _ 0 90 9 _ _ (sum_block _ 0 81 9 _ _ (sum_block _ 0 43 38 _ _ (sum_block _ 0 42 1 _ _ (sum_block _ 0 41 1 _ _ (sum_block _ 0 39 2 _ _ (sum_block _ 0 33 6 _ _ (sum_block _ 0 32 1 _ _ (sum_block _ 0 19 13 _ _ (sum_block _ 0 18 1 _ _ (sum_block _ 0 14 4 _ _ (sum_block _ 0 13 1 _ _ c148_sf0 c148_sf1) c148_sf2) c148_sf3) c148_sf4) c148_sf5) c148_sf6) c148_sf7) c148_sf8) c148_sf9) c148_sf10) c148_sf11) c148_sf12) c148_sf13) c148_sf14) c148_sf15) c148_sf16) c148_sf17) c148_sf18) c148_sf19) c148_sf20) c148_sf21) c148_sf22) c148_sf23) c148_sf24) c148_sf25) c148_sf26) c148_sf27) c148_sf28) c148_sf29) c148_sf30) c148_sf31) c148_sf32) c148_sf33) c148_sf34) c148_sf35) c148_sf36) c148_sf37) c148_sf38) c148_sf39) c148_sf40) c148_sf41) c148_sf42) c148_sf43) c148_sf44) c148_sf45) c148_sf46) c148_sf47)

theorem c148_ss : ((List.range' 0 c148.2.length).map fun i => sSmin ((c148.2.getD i default).r.arcs (pathPin (c148.2.getD i default)))).sum = 98678 := (sum_block _ 0 167 1 _ _ (sum_block _ 0 164 3 _ _ (sum_block _ 0 163 1 _ _ (sum_block _ 0 162 1 _ _ (sum_block _ 0 161 1 _ _ (sum_block _ 0 160 1 _ _ (sum_block _ 0 159 1 _ _ (sum_block _ 0 158 1 _ _ (sum_block _ 0 157 1 _ _ (sum_block _ 0 156 1 _ _ (sum_block _ 0 155 1 _ _ (sum_block _ 0 154 1 _ _ (sum_block _ 0 153 1 _ _ (sum_block _ 0 152 1 _ _ (sum_block _ 0 141 11 _ _ (sum_block _ 0 138 3 _ _ (sum_block _ 0 133 5 _ _ (sum_block _ 0 132 1 _ _ (sum_block _ 0 131 1 _ _ (sum_block _ 0 130 1 _ _ (sum_block _ 0 129 1 _ _ (sum_block _ 0 128 1 _ _ (sum_block _ 0 127 1 _ _ (sum_block _ 0 126 1 _ _ (sum_block _ 0 125 1 _ _ (sum_block _ 0 124 1 _ _ (sum_block _ 0 123 1 _ _ (sum_block _ 0 122 1 _ _ (sum_block _ 0 121 1 _ _ (sum_block _ 0 120 1 _ _ (sum_block _ 0 119 1 _ _ (sum_block _ 0 117 2 _ _ (sum_block _ 0 110 7 _ _ (sum_block _ 0 103 7 _ _ (sum_block _ 0 99 4 _ _ (sum_block _ 0 90 9 _ _ (sum_block _ 0 81 9 _ _ (sum_block _ 0 43 38 _ _ (sum_block _ 0 42 1 _ _ (sum_block _ 0 41 1 _ _ (sum_block _ 0 39 2 _ _ (sum_block _ 0 33 6 _ _ (sum_block _ 0 32 1 _ _ (sum_block _ 0 19 13 _ _ (sum_block _ 0 18 1 _ _ (sum_block _ 0 14 4 _ _ (sum_block _ 0 13 1 _ _ c148_ss0 c148_ss1) c148_ss2) c148_ss3) c148_ss4) c148_ss5) c148_ss6) c148_ss7) c148_ss8) c148_ss9) c148_ss10) c148_ss11) c148_ss12) c148_ss13) c148_ss14) c148_ss15) c148_ss16) c148_ss17) c148_ss18) c148_ss19) c148_ss20) c148_ss21) c148_ss22) c148_ss23) c148_ss24) c148_ss25) c148_ss26) c148_ss27) c148_ss28) c148_ss29) c148_ss30) c148_ss31) c148_ss32) c148_ss33) c148_ss34) c148_ss35) c148_ss36) c148_ss37) c148_ss38) c148_ss39) c148_ss40) c148_ss41) c148_ss42) c148_ss43) c148_ss44) c148_ss45) c148_ss46) c148_ss47)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c148_race : raceOK c148_sw.rr = true := raceOK_of_split c148_sw.rr _ _ c148_sf c148_ss (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c148_swok : swOK c148_sw = true := by decide +kernel

theorem c148_full : certOK c148_sw.rr.pc.1 c148_sw.rr.pc.2 = true ∧ raceOK c148_sw.rr = true ∧ swOK c148_sw = true :=
  ⟨c148_cert, c148_race, c148_swok⟩

end Formal.Cells.BigCertPS
