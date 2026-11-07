import Formal.Cells.BigCertPS.C145_R0
import Formal.Cells.BigCertPS.C145_R1
import Formal.Cells.BigCertPS.C145_R2
import Formal.Cells.BigCertPS.C145_R3
import Formal.Cells.BigCertPS.C145_R4
import Formal.Cells.BigCertPS.C145_R5
import Formal.Cells.BigCertPS.C145_R6

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertRaceAll Formal.Cells.CertSwitchAll Formal.Cells.CertSplit Formal.Cells.CertMarginPS Formal.Cells.RaceCornersPS

theorem c145_krow : (List.range' 0 c145.2.length).all (fun i => krowOK (c145.2.getD i default).r) = true := (all_range'_append _ 0 38 3 (all_range'_append _ 0 35 3 (all_range'_append _ 0 32 3 (all_range'_append _ 0 29 3 (all_range'_append _ 0 7 22 (all_range'_append _ 0 1 6 c145_k0 c145_k1) c145_k2) c145_k3) c145_k4) c145_k5) c145_k6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c145_labs : (List.range c145.2.length).all (fun i => labOK c145.1 c145.2 i (c145.2.getD i default)) = true := by decide +kernel

theorem c145_cert : certOK c145.1 c145.2 = true := certOK_of_split _ _ c145_krow c145_labs

theorem c145_sf : ((List.range' 0 c145.2.length).map fun i => sFmin ((c145.2.getD i default).r.arcs (pathPin (c145.2.getD i default)))).sum = 13056 := (sum_block _ 0 38 3 _ _ (sum_block _ 0 35 3 _ _ (sum_block _ 0 32 3 _ _ (sum_block _ 0 29 3 _ _ (sum_block _ 0 7 22 _ _ (sum_block _ 0 1 6 _ _ c145_sf0 c145_sf1) c145_sf2) c145_sf3) c145_sf4) c145_sf5) c145_sf6)

theorem c145_ss : ((List.range' 0 c145.2.length).map fun i => sSmin ((c145.2.getD i default).r.arcs (pathPin (c145.2.getD i default)))).sum = 32340 := (sum_block _ 0 38 3 _ _ (sum_block _ 0 35 3 _ _ (sum_block _ 0 32 3 _ _ (sum_block _ 0 29 3 _ _ (sum_block _ 0 7 22 _ _ (sum_block _ 0 1 6 _ _ c145_ss0 c145_ss1) c145_ss2) c145_ss3) c145_ss4) c145_ss5) c145_ss6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c145_race : raceOK c145_sw.rr = true := raceOK_of_split c145_sw.rr _ _ c145_sf c145_ss (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c145_swok : swOK c145_sw = true := by decide +kernel

theorem c145_full : certOK c145_sw.rr.pc.1 c145_sw.rr.pc.2 = true ∧ raceOK c145_sw.rr = true ∧ swOK c145_sw = true :=
  ⟨c145_cert, c145_race, c145_swok⟩

end Formal.Cells.BigCertPS
