import Formal.Core.Discretize
/-!
# WIP: discretisation soundness, open items (NOT proved; `sorry` marked)

Companion of `Formal/Core/Discretize.lean`, notes in
`formal/notes/A-discretize.md`. Nothing here is claimed.
-/

namespace Formal.Core.Discretize.Wip

open Formal.Core Formal.Core.Discretize

/-- W1 (blocked only by Mathlib build): `invariant_everywhere` without the
Archimedean side condition. Proof: `∃ T, t ≤ T q` is `exists_nat_ge (t/q)`
from `Mathlib.Algebra.Order.Archimedean.Real.Basic` (requested in
`Wip/REQUESTS.txt`). -/
theorem invariant_everywhere' {α : Type*} {q : ℝ} (hq : 0 < q) {z : ℝ → α}
    (hsep : Sep q z) (hrest : AtRest z) (Inv : α → Prop)
    (hinv : ∀ k : ℕ, Inv (z ((k : ℝ) * q))) (t : ℝ) : Inv (z t) := by
  sorry -- W1

/-- W2: the upper bound must be rounded UP (`H = ⌈hi/q⌉`): with `q = 1`,
`hi = 3/2`, a step at `3/5` delayed by `3/2` lands at `2.1`, sampled two
steps after its input sample at 1 ... (mirror of `lo_round_down_needed`;
pick the step so that the sampled delay is `⌈hi/q⌉`). Statement: -/
theorem hi_round_up_needed :
    ∃ x : ℝ → Bool, Sep 1 x ∧ AtRest x ∧
      DelayPure.Chan (3/2) (3/2) x (fun s => x (s - 3/2)) ∧
      ¬ TraceDiscrete.Transport 0 1 (sample 1 x) (sample 1 (fun s => x (s - 3/2))) := by
  sorry -- W2: x = step at 3/5: x(1) = 1, y(2) = x(1/2) = 0, y(3) = 1, delay 2 > 1

/-- Ternary (Kleene) value of a signal on grid cell `k`: definite iff
constant on `[k q, (k+1) q]`. -/
def Hull (q : ℝ) (x : ℝ → Bool) (k : ℕ) (v : Bool) : Prop :=
  ∃ t, (k : ℝ) * q ≤ t ∧ t ≤ ((k : ℝ) + 1) * q ∧ x t = v

/-- W3 (the sound discretisation WITHOUT H-sep, circuit level). For a
channel, `chan_sample_hull` proves the point form. The circuit form needs the
OUTPUT hull too: every value `y` takes on output cell `k` is a value `x`
takes on some input cell between `f k` and `f (k+1)` (σ is monotone and maps
the output cell into `[σ(kq), σ((k+1)q)]`). With the Kleene gate extension
being monotone, this gives: every continuous circuit behaviour is covered by
a behaviour of the discrete Kleene circuit whose channels carry cell hulls,
widened by one step. That would let shard B's Kleene arbiter proofs
(`ArbKleene`) cover the sub-quantum runt, which `tie_counterexample` shows the
Boolean discretisation cannot. Statement (one channel): -/
theorem chan_hull_out {q lo hi : ℝ} {L H : ℕ} (hq : 0 < q)
    (hL : (L : ℝ) * q ≤ lo) (hH : hi ≤ (H : ℝ) * q)
    {x y : ℝ → Bool} (hc : DelayPure.Chan lo hi x y) (hrest : AtRest x) :
    ∃ f : ℕ → ℕ, TraceDiscrete.Warp L (H + 1) f ∧
      ∀ k v, Hull q y k v → ∃ m, f k ≤ m ∧ m ≤ f (k + 1) ∧ Hull q x m v := by
  sorry -- W3

end Formal.Core.Discretize.Wip
