import Formal.Cells.BigCertPS.C107_R0
import Formal.Cells.BigCertPS.C107_R1
import Formal.Cells.BigCertPS.C107_R2
import Formal.Cells.BigCertPS.C107_R3
import Formal.Cells.BigCertPS.C107_R4
import Formal.Cells.BigCertPS.C107_R5
import Formal.Cells.BigCertPS.C107_R6

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertRaceAll Formal.Cells.CertSwitchAll Formal.Cells.CertSplit Formal.Cells.CertMarginPS Formal.Cells.RaceCornersPS

theorem c107_krow : (List.range' 0 c107.2.length).all (fun i => krowOK (c107.2.getD i default).r) = true := (all_range'_append _ 0 39 4 (all_range'_append _ 0 36 3 (all_range'_append _ 0 33 3 (all_range'_append _ 0 30 3 (all_range'_append _ 0 8 22 (all_range'_append _ 0 2 6 c107_k0 c107_k1) c107_k2) c107_k3) c107_k4) c107_k5) c107_k6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c107_labs : (List.range c107.2.length).all (fun i => labOK c107.1 c107.2 i (c107.2.getD i default)) = true := by decide +kernel

theorem c107_cert : certOK c107.1 c107.2 = true := certOK_of_split _ _ c107_krow c107_labs

theorem c107_sf : ((List.range' 0 c107.2.length).map fun i => sFmin ((c107.2.getD i default).r.arcs (pathPin (c107.2.getD i default)))).sum = 13628 := (sum_block _ 0 39 4 _ _ (sum_block _ 0 36 3 _ _ (sum_block _ 0 33 3 _ _ (sum_block _ 0 30 3 _ _ (sum_block _ 0 8 22 _ _ (sum_block _ 0 2 6 _ _ c107_sf0 c107_sf1) c107_sf2) c107_sf3) c107_sf4) c107_sf5) c107_sf6)

theorem c107_ss : ((List.range' 0 c107.2.length).map fun i => sSmin ((c107.2.getD i default).r.arcs (pathPin (c107.2.getD i default)))).sum = 33810 := (sum_block _ 0 39 4 _ _ (sum_block _ 0 36 3 _ _ (sum_block _ 0 33 3 _ _ (sum_block _ 0 30 3 _ _ (sum_block _ 0 8 22 _ _ (sum_block _ 0 2 6 _ _ c107_ss0 c107_ss1) c107_ss2) c107_ss3) c107_ss4) c107_ss5) c107_ss6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c107_race : raceOK c107_sw.rr = true := raceOK_of_split c107_sw.rr _ _ c107_sf c107_ss (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c107_swok : swOK c107_sw = true := by decide +kernel

theorem c107_full : certOK c107_sw.rr.pc.1 c107_sw.rr.pc.2 = true ∧ raceOK c107_sw.rr = true ∧ swOK c107_sw = true :=
  ⟨c107_cert, c107_race, c107_swok⟩

end Formal.Cells.BigCertPS
