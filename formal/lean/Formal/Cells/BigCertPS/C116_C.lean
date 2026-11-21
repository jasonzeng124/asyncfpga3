import Formal.Cells.BigCertPS.C116_R0
import Formal.Cells.BigCertPS.C116_R1
import Formal.Cells.BigCertPS.C116_R2
import Formal.Cells.BigCertPS.C116_R3
import Formal.Cells.BigCertPS.C116_R4

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertRaceAll Formal.Cells.CertSwitchAll Formal.Cells.CertSplit Formal.Cells.CertMarginPS Formal.Cells.RaceCornersPS

theorem c116_krow : (List.range' 0 c116.2.length).all (fun i => krowOK (c116.2.getD i default).r) = true := (all_range'_append _ 0 36 1 (all_range'_append _ 0 32 4 (all_range'_append _ 0 29 3 (all_range'_append _ 0 13 16 c116_k0 c116_k1) c116_k2) c116_k3) c116_k4)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c116_labs : (List.range c116.2.length).all (fun i => labOK c116.1 c116.2 i (c116.2.getD i default)) = true := by decide +kernel

theorem c116_cert : certOK c116.1 c116.2 = true := certOK_of_split _ _ c116_krow c116_labs

theorem c116_sf : ((List.range' 0 c116.2.length).map fun i => sFmin ((c116.2.getD i default).r.arcs (pathPin (c116.2.getD i default)))).sum = 11311 := (sum_block _ 0 36 1 _ _ (sum_block _ 0 32 4 _ _ (sum_block _ 0 29 3 _ _ (sum_block _ 0 13 16 _ _ c116_sf0 c116_sf1) c116_sf2) c116_sf3) c116_sf4)

theorem c116_ss : ((List.range' 0 c116.2.length).map fun i => sSmin ((c116.2.getD i default).r.arcs (pathPin (c116.2.getD i default)))).sum = 27768 := (sum_block _ 0 36 1 _ _ (sum_block _ 0 32 4 _ _ (sum_block _ 0 29 3 _ _ (sum_block _ 0 13 16 _ _ c116_ss0 c116_ss1) c116_ss2) c116_ss3) c116_ss4)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c116_race : raceOK c116_sw.rr = true := raceOK_of_split c116_sw.rr _ _ c116_sf c116_ss (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c116_swok : swOK c116_sw = true := by decide +kernel

theorem c116_full : certOK c116_sw.rr.pc.1 c116_sw.rr.pc.2 = true ∧ raceOK c116_sw.rr = true ∧ swOK c116_sw = true :=
  ⟨c116_cert, c116_race, c116_swok⟩

end Formal.Cells.BigCertPS
