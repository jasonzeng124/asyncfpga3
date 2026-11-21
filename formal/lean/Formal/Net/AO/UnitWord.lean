import Formal.Net.AO.TimedUnit
import Formal.Net.Compute.Word

/-!
# From the timed unit theorems' word form to `UnitFact` (shard C, 2026-11-15; piece 3, step 1)

**Problem, plainly.** The timed unit theorems of THE target (`Net/Compute/PS/<Unit>T.<unit>_timed_circ`) say: if every
input node of the unit (the nodes of its map `psi`) holds on `[T0, T1]`, then on `[T0 + D, T1]` the output *word*
equals the unit's op of the input *words*. `TimedUnit.UnitProof` wants a `UnitFact` about one output node. For a
1-bit output (every condition the control reads), are these the same?

**Proved.**
* `unitFact_of_word1`: a word-form timed theorem with a 1-bit output `zN` gives `UnitFact x (zN 0) ins Dc
  (fun σ => (G σ).testBit 0)`, for any `ins` listing the held nodes.
* `word_congr`: a word reads only its first `n` bits, so `F` reads only `ins` once every bit node of every input
  word below its width is in `ins` (a decidable per-unit fact).

**Not shown.** The instance for any unit of THE target (it needs the unit's built `_timed_circ` theorem).
-/

namespace Formal.Net.AO
open Formal.Net.Compute

theorem word_congr {f g : Nat → Bool} : ∀ n, (∀ k, k < n → f k = g k) → word f n = word g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [word]
    rw [word_congr n (fun k hk => h k (by omega)), h n (by omega)]

theorem word1_testBit0 (f : Nat → Bool) : (word f 1).testBit 0 = f 0 := by
  rw [testBit_word]; simp

/-- **A 1-bit word-form timed unit theorem is a `UnitFact`.** `ins` lists the held input nodes. -/
theorem unitFact_of_word1 {α : Type} {x : α → Nat → Bool} {zN : Nat → α} {ins : List α} {Dc : Nat}
    {G : (α → Bool) → Nat}
    (hT : ∀ T0 T1, (∀ u ∈ ins, ∀ t, T0 ≤ t → t ≤ T1 → x u t = x u T0) →
      ∀ t, T0 + Dc ≤ t → t ≤ T1 → word ((fun w => x w t) ∘ zN) 1 = G (fun w => x w t)) :
    UnitFact x (zN 0) ins Dc (fun σ => (G σ).testBit 0) := by
  intro T0 T1 hh t h1 h2
  have := congrArg (fun n => n.testBit 0) (hT T0 T1 hh t h1 h2)
  simp only [word1_testBit0, Function.comp] at this
  exact this

end Formal.Net.AO
