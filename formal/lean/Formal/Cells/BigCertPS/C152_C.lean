import Formal.Cells.BigCertPS.C152_R0
import Formal.Cells.BigCertPS.C152_R1
import Formal.Cells.BigCertPS.C152_R2
import Formal.Cells.BigCertPS.C152_R3
import Formal.Cells.BigCertPS.C152_R4
import Formal.Cells.BigCertPS.C152_R5
import Formal.Cells.BigCertPS.C152_R6
import Formal.Cells.BigCertPS.C152_R7
import Formal.Cells.BigCertPS.C152_R8
import Formal.Cells.BigCertPS.C152_R9

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertRaceAll Formal.Cells.CertSwitchAll Formal.Cells.CertSplit Formal.Cells.CertMarginPS Formal.Cells.RaceCornersPS

theorem c152_krow : (List.range' 0 c152.2.length).all (fun i => krowOK (c152.2.getD i default).r) = true := (all_range'_append _ 0 109 14 (all_range'_append _ 0 92 17 (all_range'_append _ 0 79 13 (all_range'_append _ 0 66 13 (all_range'_append _ 0 59 7 (all_range'_append _ 0 55 4 (all_range'_append _ 0 53 2 (all_range'_append _ 0 39 14 (all_range'_append _ 0 37 2 c152_k0 c152_k1) c152_k2) c152_k3) c152_k4) c152_k5) c152_k6) c152_k7) c152_k8) c152_k9)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c152_labs : (List.range c152.2.length).all (fun i => labOK c152.1 c152.2 i (c152.2.getD i default)) = true := by decide +kernel

theorem c152_cert : certOK c152.1 c152.2 = true := certOK_of_split _ _ c152_krow c152_labs

theorem c152_sf : ((List.range' 0 c152.2.length).map fun i => sFmin ((c152.2.getD i default).r.arcs (pathPin (c152.2.getD i default)))).sum = 29448 := (sum_block _ 0 109 14 _ _ (sum_block _ 0 92 17 _ _ (sum_block _ 0 79 13 _ _ (sum_block _ 0 66 13 _ _ (sum_block _ 0 59 7 _ _ (sum_block _ 0 55 4 _ _ (sum_block _ 0 53 2 _ _ (sum_block _ 0 39 14 _ _ (sum_block _ 0 37 2 _ _ c152_sf0 c152_sf1) c152_sf2) c152_sf3) c152_sf4) c152_sf5) c152_sf6) c152_sf7) c152_sf8) c152_sf9)

theorem c152_ss : ((List.range' 0 c152.2.length).map fun i => sSmin ((c152.2.getD i default).r.arcs (pathPin (c152.2.getD i default)))).sum = 73159 := (sum_block _ 0 109 14 _ _ (sum_block _ 0 92 17 _ _ (sum_block _ 0 79 13 _ _ (sum_block _ 0 66 13 _ _ (sum_block _ 0 59 7 _ _ (sum_block _ 0 55 4 _ _ (sum_block _ 0 53 2 _ _ (sum_block _ 0 39 14 _ _ (sum_block _ 0 37 2 _ _ c152_ss0 c152_ss1) c152_ss2) c152_ss3) c152_ss4) c152_ss5) c152_ss6) c152_ss7) c152_ss8) c152_ss9)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c152_race : raceOK c152_sw.rr = true := raceOK_of_split c152_sw.rr _ _ c152_sf c152_ss (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c152_swok : swOK c152_sw = true := by decide +kernel

theorem c152_full : certOK c152_sw.rr.pc.1 c152_sw.rr.pc.2 = true ∧ raceOK c152_sw.rr = true ∧ swOK c152_sw = true :=
  ⟨c152_cert, c152_race, c152_swok⟩

end Formal.Cells.BigCertPS
