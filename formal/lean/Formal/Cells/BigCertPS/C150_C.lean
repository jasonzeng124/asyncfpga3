import Formal.Cells.BigCertPS.C150_R0
import Formal.Cells.BigCertPS.C150_R1
import Formal.Cells.BigCertPS.C150_R2
import Formal.Cells.BigCertPS.C150_R3

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertRaceAll Formal.Cells.CertSwitchAll Formal.Cells.CertSplit Formal.Cells.CertMarginPS Formal.Cells.RaceCornersPS

theorem c150_krow : (List.range' 0 c150.2.length).all (fun i => krowOK (c150.2.getD i default).r) = true := (all_range'_append _ 0 98 4 (all_range'_append _ 0 93 5 (all_range'_append _ 0 52 41 c150_k0 c150_k1) c150_k2) c150_k3)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c150_labs : (List.range c150.2.length).all (fun i => labOK c150.1 c150.2 i (c150.2.getD i default)) = true := by decide +kernel

theorem c150_cert : certOK c150.1 c150.2 = true := certOK_of_split _ _ c150_krow c150_labs

theorem c150_sf : ((List.range' 0 c150.2.length).map fun i => sFmin ((c150.2.getD i default).r.arcs (pathPin (c150.2.getD i default)))).sum = 23583 := (sum_block _ 0 98 4 _ _ (sum_block _ 0 93 5 _ _ (sum_block _ 0 52 41 _ _ c150_sf0 c150_sf1) c150_sf2) c150_sf3)

theorem c150_ss : ((List.range' 0 c150.2.length).map fun i => sSmin ((c150.2.getD i default).r.arcs (pathPin (c150.2.getD i default)))).sum = 58872 := (sum_block _ 0 98 4 _ _ (sum_block _ 0 93 5 _ _ (sum_block _ 0 52 41 _ _ c150_ss0 c150_ss1) c150_ss2) c150_ss3)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c150_race : raceOK c150_sw.rr = true := raceOK_of_split c150_sw.rr _ _ c150_sf c150_ss (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c150_swok : swOK c150_sw = true := by decide +kernel

theorem c150_full : certOK c150_sw.rr.pc.1 c150_sw.rr.pc.2 = true ∧ raceOK c150_sw.rr = true ∧ swOK c150_sw = true :=
  ⟨c150_cert, c150_race, c150_swok⟩

end Formal.Cells.BigCertPS
