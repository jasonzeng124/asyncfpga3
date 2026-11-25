import Formal.Cells.BigCertPS.C146_R0
import Formal.Cells.BigCertPS.C146_R1
import Formal.Cells.BigCertPS.C146_R2
import Formal.Cells.BigCertPS.C146_R3
import Formal.Cells.BigCertPS.C146_R4
import Formal.Cells.BigCertPS.C146_R5

namespace Formal.Cells.BigCertPS
open Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.CertRaceAll Formal.Cells.CertSwitchAll Formal.Cells.CertSplit Formal.Cells.CertMarginPS Formal.Cells.RaceCornersPS

theorem c146_krow : (List.range' 0 c146.2.length).all (fun i => krowOK (c146.2.getD i default).r) = true := (all_range'_append _ 0 39 1 (all_range'_append _ 0 37 2 (all_range'_append _ 0 33 4 (all_range'_append _ 0 30 3 (all_range'_append _ 0 9 21 c146_k0 c146_k1) c146_k2) c146_k3) c146_k4) c146_k5)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c146_labs : (List.range c146.2.length).all (fun i => labOK c146.1 c146.2 i (c146.2.getD i default)) = true := by decide +kernel

theorem c146_cert : certOK c146.1 c146.2 = true := certOK_of_split _ _ c146_krow c146_labs

theorem c146_sf : ((List.range' 0 c146.2.length).map fun i => sFmin ((c146.2.getD i default).r.arcs (pathPin (c146.2.getD i default)))).sum = 12688 := (sum_block _ 0 39 1 _ _ (sum_block _ 0 37 2 _ _ (sum_block _ 0 33 4 _ _ (sum_block _ 0 30 3 _ _ (sum_block _ 0 9 21 _ _ c146_sf0 c146_sf1) c146_sf2) c146_sf3) c146_sf4) c146_sf5)

theorem c146_ss : ((List.range' 0 c146.2.length).map fun i => sSmin ((c146.2.getD i default).r.arcs (pathPin (c146.2.getD i default)))).sum = 31084 := (sum_block _ 0 39 1 _ _ (sum_block _ 0 37 2 _ _ (sum_block _ 0 33 4 _ _ (sum_block _ 0 30 3 _ _ (sum_block _ 0 9 21 _ _ c146_ss0 c146_ss1) c146_ss2) c146_ss3) c146_ss4) c146_ss5)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c146_race : raceOK c146_sw.rr = true := raceOK_of_split c146_sw.rr _ _ c146_sf c146_ss (by decide +kernel)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem c146_swok : swOK c146_sw = true := by decide +kernel

theorem c146_full : certOK c146_sw.rr.pc.1 c146_sw.rr.pc.2 = true ∧ raceOK c146_sw.rr = true ∧ swOK c146_sw = true :=
  ⟨c146_cert, c146_race, c146_swok⟩

end Formal.Cells.BigCertPS
