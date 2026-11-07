import Formal.Cells.BigCertPS.C139_R0
import Formal.Cells.BigCertPS.C139_R1
import Formal.Cells.BigCertPS.C139_R2
import Formal.Cells.BigCertPS.C139_R3
import Formal.Cells.BigCertPS.C139_R4
import Formal.Cells.BigCertPS.C139_R5
import Formal.Cells.BigCertPS.C139_R6

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertRaceAll Formal.Cells.CertSwitchAll Formal.Cells.CertSplit Formal.Cells.CertMarginPS Formal.Cells.RaceCornersPS

theorem c139_krow : (List.range' 0 c139.2.length).all (fun i => krowOK (c139.2.getD i default).r) = true := (all_range'_append _ 0 46 1 (all_range'_append _ 0 37 9 (all_range'_append _ 0 34 3 (all_range'_append _ 0 31 3 (all_range'_append _ 0 28 3 (all_range'_append _ 0 6 22 c139_k0 c139_k1) c139_k2) c139_k3) c139_k4) c139_k5) c139_k6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c139_labs : (List.range c139.2.length).all (fun i => labOK c139.1 c139.2 i (c139.2.getD i default)) = true := by decide +kernel

theorem c139_cert : certOK c139.1 c139.2 = true := certOK_of_split _ _ c139_krow c139_labs

theorem c139_sf : ((List.range' 0 c139.2.length).map fun i => sFmin ((c139.2.getD i default).r.arcs (pathPin (c139.2.getD i default)))).sum = 14023 := (sum_block _ 0 46 1 _ _ (sum_block _ 0 37 9 _ _ (sum_block _ 0 34 3 _ _ (sum_block _ 0 31 3 _ _ (sum_block _ 0 28 3 _ _ (sum_block _ 0 6 22 _ _ c139_sf0 c139_sf1) c139_sf2) c139_sf3) c139_sf4) c139_sf5) c139_sf6)

theorem c139_ss : ((List.range' 0 c139.2.length).map fun i => sSmin ((c139.2.getD i default).r.arcs (pathPin (c139.2.getD i default)))).sum = 34806 := (sum_block _ 0 46 1 _ _ (sum_block _ 0 37 9 _ _ (sum_block _ 0 34 3 _ _ (sum_block _ 0 31 3 _ _ (sum_block _ 0 28 3 _ _ (sum_block _ 0 6 22 _ _ c139_ss0 c139_ss1) c139_ss2) c139_ss3) c139_ss4) c139_ss5) c139_ss6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c139_race : raceOK c139_sw.rr = true := raceOK_of_split c139_sw.rr _ _ c139_sf c139_ss (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c139_swok : swOK c139_sw = true := by decide +kernel

theorem c139_full : certOK c139_sw.rr.pc.1 c139_sw.rr.pc.2 = true ∧ raceOK c139_sw.rr = true ∧ swOK c139_sw = true :=
  ⟨c139_cert, c139_race, c139_swok⟩

end Formal.Cells.BigCertPS
