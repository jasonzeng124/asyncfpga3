import Formal.Target.FrontierRunt
import Formal.Target.CexRuntD60.Refute

/-!
# Formal.Target.FrontierRunt40 — a wider runt filter (w = 40 ps) buys little margin

Shard A, 2026-11-07.

**Problem, plainly.** The headline statement (H_RUNT(20 ps)) is false from κ = 11/25 at g = 1 (`FrontierRunt`). If the
fabric filters wider pulses, say 40 ps, how much more scatter can THE target take?

**Proved.** `not_seqRunt40_above60`: with `CexRuntD60.not_netCorrectSeqRunt40` (the same race, with the adversary's
slow arcs 40 ps below the top of their window so that a 40 ps filter can act), `NetCorrectSeqRunt w` on THE target is
false for every `w ≤ 40`, every `g ≥ 1`, every `κ ≥ 15/25`, `T ≥ 88`, any `su`, `Δo ≤ 3000`, reset 400 ns.

**Not shown.** Anything for w > 40; any point where the statement holds (simulation: this adversary is correct at
κ = 0.52 with w = 40).
-/

namespace Formal.Target.FrontierRunt40
open Formal.Target Formal.Target.DecodedPS Formal.Target.FrontierRunt

theorem not_seqRunt40_above60 {w : Nat} (hw : w ≤ 40) {p : DelayPar} (hg : 1 ≤ p.g) (hk : 15 / 25 ≤ p.κ)
    (T su Δo : Nat) (hT : 88 ≤ T) (hΔ : Δo ≤ 3000) :
    ¬ NetCorrectSeqRunt w net boundary arbs p T 400000 su Δo := by
  intro h
  have hle : (Formal.Target.CexRuntD.pP 15).LE p := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Formal.Target.CexRuntD.pP] <;> norm_num <;> linarith
  exact Formal.Target.CexRuntD60.not_netCorrectSeqRunt40 T su Δo hT hΔ
    (seqRuntOn_anti_p hle (seqRuntOn_anti_w hw h))

end Formal.Target.FrontierRunt40
