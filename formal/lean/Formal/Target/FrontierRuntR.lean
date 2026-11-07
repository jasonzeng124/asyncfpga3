import Formal.Target.FrontierRunt
import Formal.Target.CexRunt44.AnyR
import Formal.Target.CexRuntG16.AnyR
import Formal.Target.CexRuntD60.AnyR
import Formal.Target.FrontierRunt40

/-!
# Formal.Target.FrontierRuntR — the headline refutation for every reset length (shard A, 2026-11-07)

**Proved.** `not_seqRunt_le20_above44_R`: on THE target, `NetCorrectSeqRunt w` is false for every runt width
`w ≤ 20`, every guard `g ≥ 1`, every scatter `κ ≥ 11/25`, every reset length `R ≥ 400 ns`, every `T ≥ 123`, every
`su` and every `Δo ≤ 3000`. (`CexRunt44.AnyR.not_netCorrectSeqRunt20_R` with `FrontierRunt`'s monotonicity in
(g, κ) and w.) So the board's long reset does not change the verdict. Likewise on the guard axis
(`not_seqRunt_le20_aboveG16_R`: every g ≥ 8/5, κ ≥ 0) and for the wider filter (`not_seqRunt40_above60_R`: every
w ≤ 40, κ ≥ 15/25), each for every R ≥ 400 ns.
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

theorem not_seqRunt_le20_aboveG16_R {w : Nat} (hw : w ≤ 20) {p : DelayPar} (hg : 8 / 5 ≤ p.g) (hk : 0 ≤ p.κ)
    (R T su Δo : Nat) (hR : 400000 ≤ R) (hT : 137 ≤ T) (hΔ : Δo ≤ 3000) :
    ¬ NetCorrectSeqRunt w net boundary arbs p T R su Δo := by
  intro h
  have hle : (Formal.Target.CexRuntG.pG 8 5).LE p := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Formal.Target.CexRuntG.pG] <;> norm_num <;> linarith
  exact Formal.Target.CexRuntG16.AnyR.not_netCorrectSeqRunt20_R R T su Δo hR hT hΔ
    (seqRuntOn_anti_p hle (seqRuntOn_anti_w hw h))

theorem not_seqRunt40_above60_R {w : Nat} (hw : w ≤ 40) {p : DelayPar} (hg : 1 ≤ p.g) (hk : 15 / 25 ≤ p.κ)
    (R T su Δo : Nat) (hR : 400000 ≤ R) (hT : 88 ≤ T) (hΔ : Δo ≤ 3000) :
    ¬ NetCorrectSeqRunt w net boundary arbs p T R su Δo := by
  intro h
  have hle : (Formal.Target.CexRuntD.pP 15).LE p := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Formal.Target.CexRuntD.pP] <;> norm_num <;> linarith
  exact Formal.Target.CexRuntD60.AnyR.not_netCorrectSeqRunt40_R R T su Δo hR hT hΔ
    (seqRuntOn_anti_p hle (seqRuntOn_anti_w hw h))

end Formal.Target.FrontierRuntR
