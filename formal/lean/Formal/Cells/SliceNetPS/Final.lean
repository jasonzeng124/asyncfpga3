import Formal.Cells.SliceNetPS.Main
import Formal.Cells.StartBoundPS.Main

/-!
# Formal.Cells.SliceNetPS.Final — the read hypotheses on THE target's slice net, with no netlist premise
(shard B, 2026-11-10)

**Proved.** `target_reads_slice_H`: for every sane `p` and every behaviour of THE theorem's circuit there is a
corner `c ∈ [0,1]` such that for every slice `[c1, c2] ∋ c` with `c2 ≤ 1` and every `t0 ≥ 2·H`, where
`H = ⌈(1+κ)g⌉ · 33,002` ps, there are read times meeting `TBehX`'s `rd` (with this `H`), `mono` and `geq` on
THE target's slice net `tnPS p c1 c2`. Also `tnPS_lo1` (κ < 1, `0 ≤ c1`): every kept pin's lower bound ≥ 1.

**Not shown here:** `TBehX`'s `quiet` and `env` fields; any certificate on `tnPS`.
-/

namespace Formal.Cells.SliceNetPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecSettle Formal.Net.CViewPS Formal.Cells.StartBound
  Formal.Cells.StartBoundPS

theorem target_reads_slice_H {p : DelayPar} (hp : Sane p) {x : Beh} (hb : Behaves p (circuit net boundary) x) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ (c1 c2 : ℚ) (t0 : Nat), c1 ≤ c → c ≤ c2 → c2 ≤ 1 → 2 * (mOf p * HB) ≤ t0 →
      ∃ r : Nat → Nat → Nat → Nat,
        (∀ v w t, (tnPS p c1 c2).gate v = true → w ∈ (tnPS p c1 c2).pins v → t0 < t →
          (tnPS p c1 c2).lo v w ≤ t - r v w t ∧ t - r v w t ≤ (tnPS p c1 c2).hi v w ∧ r v w t ≤ t ∧
          t0 ≤ r v w t + mOf p * HB) ∧
        (∀ v w t t', (tnPS p c1 c2).gate v = true → w ∈ (tnPS p c1 c2).pins v → t0 < t → t ≤ t' →
          r v w t ≤ r v w t') ∧
        (∀ v t, (tnPS p c1 c2).gate v = true → t0 < t →
          x v t = (tnPS p c1 c2).F v (((tnPS p c1 c2).pins v).map fun w => x w (r v w t))) := by
  obtain ⟨c, hc0, hc1, h⟩ := target_reads_slice hp hb
  refine ⟨c, hc0, hc1, fun c1 c2 t0 h1 h2 hc2 ht0 => h c1 c2 t0 _ h1 h2 hc2 (fun w hw => startPS_le hp hw)
    (fun w hw => ?_)⟩
  have := startPS_le hp hw
  omega

end Formal.Cells.SliceNetPS
