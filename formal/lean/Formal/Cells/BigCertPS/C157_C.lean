import Formal.Cells.BigCertPS.C157_R0
import Formal.Cells.BigCertPS.C157_R1
import Formal.Cells.BigCertPS.C157_R2
import Formal.Cells.BigCertPS.C157_R3
import Formal.Cells.BigCertPS.C157_R4
import Formal.Cells.BigCertPS.C157_R5
import Formal.Cells.BigCertPS.C157_R6
import Formal.Cells.BigCertPS.C157_R7
import Formal.Cells.BigCertPS.C157_R8
import Formal.Cells.BigCertPS.C157_R9
import Formal.Cells.BigCertPS.C157_R10
import Formal.Cells.BigCertPS.C157_R11
import Formal.Cells.BigCertPS.C157_R12
import Formal.Cells.BigCertPS.C157_R13
import Formal.Cells.BigCertPS.C157_R14
import Formal.Cells.BigCertPS.C157_R15
import Formal.Cells.BigCertPS.C157_R16
import Formal.Cells.BigCertPS.C157_R17
import Formal.Cells.BigCertPS.C157_R18
import Formal.Cells.BigCertPS.C157_R19
import Formal.Cells.BigCertPS.C157_R20
import Formal.Cells.BigCertPS.C157_R21
import Formal.Cells.BigCertPS.C157_R22
import Formal.Cells.BigCertPS.C157_R23
import Formal.Cells.BigCertPS.C157_R24
import Formal.Cells.BigCertPS.C157_R25
import Formal.Cells.BigCertPS.C157_R26
import Formal.Cells.BigCertPS.C157_R27
import Formal.Cells.BigCertPS.C157_R28
import Formal.Cells.BigCertPS.C157_R29
import Formal.Cells.BigCertPS.C157_R30
import Formal.Cells.BigCertPS.C157_R31
import Formal.Cells.BigCertPS.C157_R32
import Formal.Cells.BigCertPS.C157_R33
import Formal.Cells.BigCertPS.C157_R34
import Formal.Cells.BigCertPS.C157_R35
import Formal.Cells.BigCertPS.C157_R36
import Formal.Cells.BigCertPS.C157_R37
import Formal.Cells.BigCertPS.C157_R38
import Formal.Cells.BigCertPS.C157_R39
import Formal.Cells.BigCertPS.C157_R40
import Formal.Cells.BigCertPS.C157_R41
import Formal.Cells.BigCertPS.C157_R42
import Formal.Cells.BigCertPS.C157_R43
import Formal.Cells.BigCertPS.C157_R44
import Formal.Cells.BigCertPS.C157_R45
import Formal.Cells.BigCertPS.C157_R46
import Formal.Cells.BigCertPS.C157_R47

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertRaceAll Formal.Cells.CertSwitchAll Formal.Cells.CertSplit Formal.Cells.CertMarginPS Formal.Cells.RaceCornersPS

theorem c157_krow : (List.range' 0 c157.2.length).all (fun i => krowOK (c157.2.getD i default).r) = true := (all_range'_append _ 0 198 4 (all_range'_append _ 0 197 1 (all_range'_append _ 0 196 1 (all_range'_append _ 0 195 1 (all_range'_append _ 0 194 1 (all_range'_append _ 0 193 1 (all_range'_append _ 0 191 2 (all_range'_append _ 0 190 1 (all_range'_append _ 0 177 13 (all_range'_append _ 0 176 1 (all_range'_append _ 0 172 4 (all_range'_append _ 0 171 1 (all_range'_append _ 0 170 1 (all_range'_append _ 0 169 1 (all_range'_append _ 0 168 1 (all_range'_append _ 0 167 1 (all_range'_append _ 0 166 1 (all_range'_append _ 0 165 1 (all_range'_append _ 0 164 1 (all_range'_append _ 0 163 1 (all_range'_append _ 0 162 1 (all_range'_append _ 0 160 2 (all_range'_append _ 0 159 1 (all_range'_append _ 0 158 1 (all_range'_append _ 0 157 1 (all_range'_append _ 0 156 1 (all_range'_append _ 0 155 1 (all_range'_append _ 0 154 1 (all_range'_append _ 0 141 13 (all_range'_append _ 0 140 1 (all_range'_append _ 0 139 1 (all_range'_append _ 0 138 1 (all_range'_append _ 0 127 11 (all_range'_append _ 0 107 20 (all_range'_append _ 0 106 1 (all_range'_append _ 0 103 3 (all_range'_append _ 0 102 1 (all_range'_append _ 0 101 1 (all_range'_append _ 0 100 1 (all_range'_append _ 0 98 2 (all_range'_append _ 0 78 20 (all_range'_append _ 0 58 20 (all_range'_append _ 0 38 20 (all_range'_append _ 0 18 20 (all_range'_append _ 0 15 3 (all_range'_append _ 0 14 1 (all_range'_append _ 0 13 1 c157_k0 c157_k1) c157_k2) c157_k3) c157_k4) c157_k5) c157_k6) c157_k7) c157_k8) c157_k9) c157_k10) c157_k11) c157_k12) c157_k13) c157_k14) c157_k15) c157_k16) c157_k17) c157_k18) c157_k19) c157_k20) c157_k21) c157_k22) c157_k23) c157_k24) c157_k25) c157_k26) c157_k27) c157_k28) c157_k29) c157_k30) c157_k31) c157_k32) c157_k33) c157_k34) c157_k35) c157_k36) c157_k37) c157_k38) c157_k39) c157_k40) c157_k41) c157_k42) c157_k43) c157_k44) c157_k45) c157_k46) c157_k47)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c157_labs : (List.range c157.2.length).all (fun i => labOK c157.1 c157.2 i (c157.2.getD i default)) = true := by decide +kernel

theorem c157_cert : certOK c157.1 c157.2 = true := certOK_of_split _ _ c157_krow c157_labs

theorem c157_sf : ((List.range' 0 c157.2.length).map fun i => sFmin ((c157.2.getD i default).r.arcs (pathPin (c157.2.getD i default)))).sum = 47420 := (sum_block _ 0 198 4 _ _ (sum_block _ 0 197 1 _ _ (sum_block _ 0 196 1 _ _ (sum_block _ 0 195 1 _ _ (sum_block _ 0 194 1 _ _ (sum_block _ 0 193 1 _ _ (sum_block _ 0 191 2 _ _ (sum_block _ 0 190 1 _ _ (sum_block _ 0 177 13 _ _ (sum_block _ 0 176 1 _ _ (sum_block _ 0 172 4 _ _ (sum_block _ 0 171 1 _ _ (sum_block _ 0 170 1 _ _ (sum_block _ 0 169 1 _ _ (sum_block _ 0 168 1 _ _ (sum_block _ 0 167 1 _ _ (sum_block _ 0 166 1 _ _ (sum_block _ 0 165 1 _ _ (sum_block _ 0 164 1 _ _ (sum_block _ 0 163 1 _ _ (sum_block _ 0 162 1 _ _ (sum_block _ 0 160 2 _ _ (sum_block _ 0 159 1 _ _ (sum_block _ 0 158 1 _ _ (sum_block _ 0 157 1 _ _ (sum_block _ 0 156 1 _ _ (sum_block _ 0 155 1 _ _ (sum_block _ 0 154 1 _ _ (sum_block _ 0 141 13 _ _ (sum_block _ 0 140 1 _ _ (sum_block _ 0 139 1 _ _ (sum_block _ 0 138 1 _ _ (sum_block _ 0 127 11 _ _ (sum_block _ 0 107 20 _ _ (sum_block _ 0 106 1 _ _ (sum_block _ 0 103 3 _ _ (sum_block _ 0 102 1 _ _ (sum_block _ 0 101 1 _ _ (sum_block _ 0 100 1 _ _ (sum_block _ 0 98 2 _ _ (sum_block _ 0 78 20 _ _ (sum_block _ 0 58 20 _ _ (sum_block _ 0 38 20 _ _ (sum_block _ 0 18 20 _ _ (sum_block _ 0 15 3 _ _ (sum_block _ 0 14 1 _ _ (sum_block _ 0 13 1 _ _ c157_sf0 c157_sf1) c157_sf2) c157_sf3) c157_sf4) c157_sf5) c157_sf6) c157_sf7) c157_sf8) c157_sf9) c157_sf10) c157_sf11) c157_sf12) c157_sf13) c157_sf14) c157_sf15) c157_sf16) c157_sf17) c157_sf18) c157_sf19) c157_sf20) c157_sf21) c157_sf22) c157_sf23) c157_sf24) c157_sf25) c157_sf26) c157_sf27) c157_sf28) c157_sf29) c157_sf30) c157_sf31) c157_sf32) c157_sf33) c157_sf34) c157_sf35) c157_sf36) c157_sf37) c157_sf38) c157_sf39) c157_sf40) c157_sf41) c157_sf42) c157_sf43) c157_sf44) c157_sf45) c157_sf46) c157_sf47)

theorem c157_ss : ((List.range' 0 c157.2.length).map fun i => sSmin ((c157.2.getD i default).r.arcs (pathPin (c157.2.getD i default)))).sum = 117363 := (sum_block _ 0 198 4 _ _ (sum_block _ 0 197 1 _ _ (sum_block _ 0 196 1 _ _ (sum_block _ 0 195 1 _ _ (sum_block _ 0 194 1 _ _ (sum_block _ 0 193 1 _ _ (sum_block _ 0 191 2 _ _ (sum_block _ 0 190 1 _ _ (sum_block _ 0 177 13 _ _ (sum_block _ 0 176 1 _ _ (sum_block _ 0 172 4 _ _ (sum_block _ 0 171 1 _ _ (sum_block _ 0 170 1 _ _ (sum_block _ 0 169 1 _ _ (sum_block _ 0 168 1 _ _ (sum_block _ 0 167 1 _ _ (sum_block _ 0 166 1 _ _ (sum_block _ 0 165 1 _ _ (sum_block _ 0 164 1 _ _ (sum_block _ 0 163 1 _ _ (sum_block _ 0 162 1 _ _ (sum_block _ 0 160 2 _ _ (sum_block _ 0 159 1 _ _ (sum_block _ 0 158 1 _ _ (sum_block _ 0 157 1 _ _ (sum_block _ 0 156 1 _ _ (sum_block _ 0 155 1 _ _ (sum_block _ 0 154 1 _ _ (sum_block _ 0 141 13 _ _ (sum_block _ 0 140 1 _ _ (sum_block _ 0 139 1 _ _ (sum_block _ 0 138 1 _ _ (sum_block _ 0 127 11 _ _ (sum_block _ 0 107 20 _ _ (sum_block _ 0 106 1 _ _ (sum_block _ 0 103 3 _ _ (sum_block _ 0 102 1 _ _ (sum_block _ 0 101 1 _ _ (sum_block _ 0 100 1 _ _ (sum_block _ 0 98 2 _ _ (sum_block _ 0 78 20 _ _ (sum_block _ 0 58 20 _ _ (sum_block _ 0 38 20 _ _ (sum_block _ 0 18 20 _ _ (sum_block _ 0 15 3 _ _ (sum_block _ 0 14 1 _ _ (sum_block _ 0 13 1 _ _ c157_ss0 c157_ss1) c157_ss2) c157_ss3) c157_ss4) c157_ss5) c157_ss6) c157_ss7) c157_ss8) c157_ss9) c157_ss10) c157_ss11) c157_ss12) c157_ss13) c157_ss14) c157_ss15) c157_ss16) c157_ss17) c157_ss18) c157_ss19) c157_ss20) c157_ss21) c157_ss22) c157_ss23) c157_ss24) c157_ss25) c157_ss26) c157_ss27) c157_ss28) c157_ss29) c157_ss30) c157_ss31) c157_ss32) c157_ss33) c157_ss34) c157_ss35) c157_ss36) c157_ss37) c157_ss38) c157_ss39) c157_ss40) c157_ss41) c157_ss42) c157_ss43) c157_ss44) c157_ss45) c157_ss46) c157_ss47)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c157_race : raceOK c157_sw.rr = true := raceOK_of_split c157_sw.rr _ _ c157_sf c157_ss (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c157_swok : swOK c157_sw = true := by decide +kernel

theorem c157_full : certOK c157_sw.rr.pc.1 c157_sw.rr.pc.2 = true ∧ raceOK c157_sw.rr = true ∧ swOK c157_sw = true :=
  ⟨c157_cert, c157_race, c157_swok⟩

end Formal.Cells.BigCertPS
