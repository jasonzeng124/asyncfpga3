import Formal.Target.FrontierRunt
import Formal.Target.CexRunt44.AnyR

/-!
# Formal.Target.FrontierRuntR — the headline refutation for every reset length (shard A, 2026-11-07)

**Proved.** `not_seqRunt_le20_above44_R`: on THE target, `NetCorrectSeqRunt w` is false for every runt width
`w ≤ 20`, every guard `g ≥ 1`, every scatter `κ ≥ 11/25`, every reset length `R ≥ 400 ns`, every `T ≥ 123`, every
`su` and every `Δo ≤ 3000`. (`CexRunt44.AnyR.not_netCorrectSeqRunt20_R` with `FrontierRunt`'s monotonicity in
(g, κ) and w.) So the board's long reset does not change the verdict.
-/

namespace Formal.Target.FrontierRuntR
open Formal.Target Formal.Target.DecodedPS Formal.Target.FrontierRunt

theorem not_seqRunt_le20_above44_R {w : Nat} (hw : w ≤ 20) {p : DelayPar} (hg : 1 ≤ p.g) (hk : 11 / 25 ≤ p.κ)
    (R T su Δo : Nat) (hR : 400000 ≤ R) (hT : 123 ≤ T) (hΔ : Δo ≤ 3000) :
    ¬ NetCorrectSeqRunt w net boundary arbs p T R su Δo := by
  intro h
  have hle : (Formal.Target.CexRuntP.pP 11).LE p := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Formal.Target.CexRuntP.pP] <;> norm_num <;> linarith
  exact Formal.Target.CexRunt44.AnyR.not_netCorrectSeqRunt20_R R T su Δo hR hT hΔ
    (seqRuntOn_anti_p hle (seqRuntOn_anti_w hw h))

end Formal.Target.FrontierRuntR
