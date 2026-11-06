import Formal.Target.SpecMono
import Formal.Net.CexPS.Refute

/-!
# Formal.Target.FrontierPS — where THE theorem's (g, κ) margin can lie on THE target

Shard A, 2026-11-06. **Plainly:** shard C's Lean counterexample (`CexPS.not_netCorrectSeq`, g = 1, κ = 21/25) carries,
by the down-set property (`SpecMono.seq_anti_p`), to every guard `g ≥ 1` and every scatter `21/25 ≤ κ ≤ 1`: THE
sequential statement is false there, for every arbiter bound `T ≥ 36`, every `su` and every `Δo ≤ 3000`, reset 400 ns
(`not_seq_above`). So the owner's (g, κ) frontier lies inside `κ < 21/25` for every `g ≥ 1` (without runt filtering).
Not shown: any point where the statement HOLDS (no positive result for n ≥ 1 exists); other reset lengths.
-/

namespace Formal.Target.FrontierPS
open Formal.Target Formal.Target.DecodedPS

theorem not_seq_above {p : DelayPar} (hg : 1 ≤ p.g) (hk : 21 / 25 ≤ p.κ) (T su Δo : Nat) (hT : 36 ≤ T)
    (hΔ : Δo ≤ 3000) : ¬ NetCorrectSeq net boundary arbs p T 400000 su Δo := by
  intro h
  have hle : Formal.Net.CexPS.pK.LE p := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Formal.Net.CexPS.pK] <;> norm_num <;> linarith
  exact Formal.Net.CexPS.not_netCorrectSeq T su Δo hT hΔ (seq_anti_p hle h)

end Formal.Target.FrontierPS
