import Formal.Cells.RaceAllPS
import Formal.Cells.RaceAllPS2
import Formal.Cells.BigCertPS

/-!
# Formal.Cells.RaceAllTarget — 181 storage nodes of THE target switch cleanly, one corner, every behaviour

Shard B, 2026-11-07. The three certificate batches (`RaceAllPS`: 135 rows, `RaceAllPS2`: 23, `BigCertPS`: 23) in one
statement, `CertSwitchAll.target_switches_of` over their concatenation: for every behaviour of THE circuit with
g = 1 and κ ≤ 83/200, at one corner c for all 181 rows, each row's storage node, once its local premises hold from
`sT` to `e'` (see `CertSwitchAll.target_switches_of` and `notes/B-for-C-S4.md`), is at its new value on all of
`[sT, e']`. Not covered: 4 RaceTablePS rows (power-up episodes); the premises.
-/

namespace Formal.Cells.RaceAllTarget
open Formal.Cells.CertPS Formal.Cells.CertRaceAll Formal.Cells.CertSwitchAll

def allSws : List SwRow := RaceAllPS.sws ++ RaceAllPS2.sws ++ BigCertPS.sws

theorem allSws_full : ∀ s ∈ allSws, certOK s.rr.pc.1 s.rr.pc.2 = true ∧ raceOK s.rr = true ∧ swOK s = true := by
  simp only [allSws, List.forall_mem_append]
  exact ⟨⟨RaceAllPS.sws_full, RaceAllPS2.sws_full⟩, BigCertPS.sws_full⟩

/-- **181 storage nodes of THE target switch cleanly in every behaviour** (one corner; g = 1, κ ≤ 83/200). -/
theorem target_switches_181 : type_of% (@target_switches_of allSws allSws_full) :=
  @target_switches_of allSws allSws_full

end Formal.Cells.RaceAllTarget
