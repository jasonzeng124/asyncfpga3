import Formal.Cells.BigCertPS.C136_R0
import Formal.Cells.BigCertPS.C136_R1
import Formal.Cells.BigCertPS.C136_R2
import Formal.Cells.BigCertPS.C136_R3

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertRaceAll Formal.Cells.CertSwitchAll Formal.Cells.CertSplit Formal.Cells.CertMarginPS Formal.Cells.RaceCornersPS

theorem c136_krow : (List.range' 0 c136.2.length).all (fun i => krowOK (c136.2.getD i default).r) = true := (all_range'_append _ 0 94 6 (all_range'_append _ 0 53 41 (all_range'_append _ 0 35 18 c136_k0 c136_k1) c136_k2) c136_k3)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c136_labs : (List.range c136.2.length).all (fun i => labOK c136.1 c136.2 i (c136.2.getD i default)) = true := by decide +kernel

theorem c136_cert : certOK c136.1 c136.2 = true := certOK_of_split _ _ c136_krow c136_labs

theorem c136_sf : ((List.range' 0 c136.2.length).map fun i => sFmin ((c136.2.getD i default).r.arcs (pathPin (c136.2.getD i default)))).sum = 22351 := (sum_block _ 0 94 6 _ _ (sum_block _ 0 53 41 _ _ (sum_block _ 0 35 18 _ _ c136_sf0 c136_sf1) c136_sf2) c136_sf3)

theorem c136_ss : ((List.range' 0 c136.2.length).map fun i => sSmin ((c136.2.getD i default).r.arcs (pathPin (c136.2.getD i default)))).sum = 55820 := (sum_block _ 0 94 6 _ _ (sum_block _ 0 53 41 _ _ (sum_block _ 0 35 18 _ _ c136_ss0 c136_ss1) c136_ss2) c136_ss3)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c136_race : raceOK c136_sw.rr = true := raceOK_of_split c136_sw.rr _ _ c136_sf c136_ss (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c136_swok : swOK c136_sw = true := by decide +kernel

theorem c136_full : certOK c136_sw.rr.pc.1 c136_sw.rr.pc.2 = true ∧ raceOK c136_sw.rr = true ∧ swOK c136_sw = true :=
  ⟨c136_cert, c136_race, c136_swok⟩

end Formal.Cells.BigCertPS
