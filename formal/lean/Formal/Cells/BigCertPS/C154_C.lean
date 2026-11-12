import Formal.Cells.BigCertPS.C154_R0
import Formal.Cells.BigCertPS.C154_R1
import Formal.Cells.BigCertPS.C154_R2
import Formal.Cells.BigCertPS.C154_R3
import Formal.Cells.BigCertPS.C154_R4

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertRaceAll Formal.Cells.CertSwitchAll Formal.Cells.CertSplit Formal.Cells.CertMarginPS Formal.Cells.RaceCornersPS

theorem c154_krow : (List.range' 0 c154.2.length).all (fun i => krowOK (c154.2.getD i default).r) = true := (all_range'_append _ 0 62 19 (all_range'_append _ 0 51 11 (all_range'_append _ 0 49 2 (all_range'_append _ 0 34 15 c154_k0 c154_k1) c154_k2) c154_k3) c154_k4)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c154_labs : (List.range c154.2.length).all (fun i => labOK c154.1 c154.2 i (c154.2.getD i default)) = true := by decide +kernel

theorem c154_cert : certOK c154.1 c154.2 = true := certOK_of_split _ _ c154_krow c154_labs

theorem c154_sf : ((List.range' 0 c154.2.length).map fun i => sFmin ((c154.2.getD i default).r.arcs (pathPin (c154.2.getD i default)))).sum = 20704 := (sum_block _ 0 62 19 _ _ (sum_block _ 0 51 11 _ _ (sum_block _ 0 49 2 _ _ (sum_block _ 0 34 15 _ _ c154_sf0 c154_sf1) c154_sf2) c154_sf3) c154_sf4)

theorem c154_ss : ((List.range' 0 c154.2.length).map fun i => sSmin ((c154.2.getD i default).r.arcs (pathPin (c154.2.getD i default)))).sum = 51076 := (sum_block _ 0 62 19 _ _ (sum_block _ 0 51 11 _ _ (sum_block _ 0 49 2 _ _ (sum_block _ 0 34 15 _ _ c154_ss0 c154_ss1) c154_ss2) c154_ss3) c154_ss4)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c154_race : raceOK c154_sw.rr = true := raceOK_of_split c154_sw.rr _ _ c154_sf c154_ss (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c154_swok : swOK c154_sw = true := by decide +kernel

theorem c154_full : certOK c154_sw.rr.pc.1 c154_sw.rr.pc.2 = true ∧ raceOK c154_sw.rr = true ∧ swOK c154_sw = true :=
  ⟨c154_cert, c154_race, c154_swok⟩

end Formal.Cells.BigCertPS
