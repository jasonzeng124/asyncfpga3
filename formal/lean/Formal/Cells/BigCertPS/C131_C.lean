import Formal.Cells.BigCertPS.C131_R0
import Formal.Cells.BigCertPS.C131_R1
import Formal.Cells.BigCertPS.C131_R2
import Formal.Cells.BigCertPS.C131_R3
import Formal.Cells.BigCertPS.C131_R4

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertRaceAll Formal.Cells.CertSwitchAll Formal.Cells.CertSplit Formal.Cells.CertMarginPS Formal.Cells.RaceCornersPS

theorem c131_krow : (List.range' 0 c131.2.length).all (fun i => krowOK (c131.2.getD i default).r) = true := (all_range'_append _ 0 38 9 (all_range'_append _ 0 34 4 (all_range'_append _ 0 31 3 (all_range'_append _ 0 10 21 c131_k0 c131_k1) c131_k2) c131_k3) c131_k4)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c131_labs : (List.range c131.2.length).all (fun i => labOK c131.1 c131.2 i (c131.2.getD i default)) = true := by decide +kernel

theorem c131_cert : certOK c131.1 c131.2 = true := certOK_of_split _ _ c131_krow c131_labs

theorem c131_sf : ((List.range' 0 c131.2.length).map fun i => sFmin ((c131.2.getD i default).r.arcs (pathPin (c131.2.getD i default)))).sum = 13675 := (sum_block _ 0 38 9 _ _ (sum_block _ 0 34 4 _ _ (sum_block _ 0 31 3 _ _ (sum_block _ 0 10 21 _ _ c131_sf0 c131_sf1) c131_sf2) c131_sf3) c131_sf4)

theorem c131_ss : ((List.range' 0 c131.2.length).map fun i => sSmin ((c131.2.getD i default).r.arcs (pathPin (c131.2.getD i default)))).sum = 33621 := (sum_block _ 0 38 9 _ _ (sum_block _ 0 34 4 _ _ (sum_block _ 0 31 3 _ _ (sum_block _ 0 10 21 _ _ c131_ss0 c131_ss1) c131_ss2) c131_ss3) c131_ss4)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c131_race : raceOK c131_sw.rr = true := raceOK_of_split c131_sw.rr _ _ c131_sf c131_ss (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c131_swok : swOK c131_sw = true := by decide +kernel

theorem c131_full : certOK c131_sw.rr.pc.1 c131_sw.rr.pc.2 = true ∧ raceOK c131_sw.rr = true ∧ swOK c131_sw = true :=
  ⟨c131_cert, c131_race, c131_swok⟩

end Formal.Cells.BigCertPS
