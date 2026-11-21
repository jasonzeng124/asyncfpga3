import Formal.Net.GcdHwNat

/-!
# The bdc gcd_hw graph computes `Nat.gcd`, and every run of it finishes (probe C-8k)

Core Lean only. Combines C-8i's `gcd_hw_graph_computes_gcdC` (the dataflow
graph bdc emits for gcd_hw, imported from bdc's own code, ends every complete
run with the C function's result) with C-8k's `gcdC_fuel` (the C function is
`Nat.gcd` on `[0, 2^31)^2` and terminates there).

* `gcd_hw_graph_computes_gcd`: for `a, b < 2^31`, a complete run exists, and
  EVERY complete run (any schedule, any arbitration of the 8 multi-input
  control_merges) ends in the store with exactly `[Nat.gcd a b]` on `out0`,
  the end token on `end`, and nothing else.
* Liveness at token level (no fairness assumption needed):
  - `gcd_hw_graph_bounded`: every run from the initial store has at most `N`
    firings, for one `N` depending on `a, b`;
  - `gcd_hw_graph_no_infinite_run`: there is no infinite firing sequence;
  - `gcd_hw_graph_live`: every partial run (any prefix of any schedule) can be
    extended to the final store, and every maximal run IS complete and ends
    there (`gcd_hw_graph_maximal`). So "complete run" in the main theorem is
    not vacuous, and no schedule deadlocks or livelocks.

Hypotheses: the token-level ones of C-8i (unbounded FIFO channels,
H_SOURCE_ETERNAL for the 4 source chains; H_ONE_INVOCATION is proved from the
initial store, not assumed). The input range `a, b < 2^31` (non-negative i32)
is a hypothesis of the statement, not a model assumption: for negative i32
patterns the C loop (and so, by C-8i, the graph) can run forever.
-/

namespace Formal.Net.GcdHw.Gcd

open Formal.Net.Kahn Formal.Net.GcdHw

/-- Initial store: one token each on `a`, `b`, `start` (see `init_store`). -/
abbrev init (a b : Nat) : Store Nat Nat := St T0 [a, b]
/-- Final store: `[r]` on `out0`, the end token, nothing else (see `final_store`). -/
abbrev final (r : Nat) : Store Nat Nat := St T1 [r]

theorem gcdC_some {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    gcdC (fuelBound a b) a b = some (Nat.gcd a b) := gcdC_fuel ha hb (Nat.le_refl _)

/-- **The imported gcd_hw graph computes `Nat.gcd` on non-negative i32 inputs.**
Some schedule completes; every complete run, on every schedule and every
control_merge arbitration, ends in `final (Nat.gcd a b)`, i.e. with exactly
`[Nat.gcd a b]` on `out0`; and no run is longer than a complete one. -/
theorem gcd_hw_graph_computes_gcd {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    (∃ n, Run (step G) (init a b) n (final (Nat.gcd a b))) ∧
    (∀ m t, Run (step G) (init a b) m t → Terminal (step G) t →
      t = final (Nat.gcd a b) ∧ t chOut = [Nat.gcd a b] ∧ t chEnd = [0]) ∧
    (∃ n, ∀ m u, Run (step G) (init a b) m u → m ≤ n) := by
  obtain ⟨h1, h2, h3⟩ := gcd_hw_graph_computes_gcdC (gcdC_some ha hb)
  refine ⟨h1, fun m t ht hT => ?_, h3⟩
  have e := h2 m t ht hT
  subst e
  exact ⟨rfl, (final_store _).1, (final_store _).2⟩

theorem closedG : Closed (step G) (Inv spine) := closed_of_check spine rules spine_nodup spine_ok

theorem diamondG : DiamondOn (step G) (Inv spine) :=
  wfOn_diamond (wfOn_of_check spine rules spine_nodup ins_ok outs_ok)

/-- Liveness, prefix form: every partial run from the initial store, whatever
the schedule and arbitration so far, can be completed, and every completion
ends in `final (Nat.gcd a b)`. -/
theorem gcd_hw_graph_live {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    ∀ m u, Run (step G) (init a b) m u →
      ∃ k, Run (step G) u k (final (Nat.gcd a b)) ∧
        ∀ k' t, Run (step G) u k' t → Terminal (step G) t → t = final (Nat.gcd a b) ∧ k' = k := by
  intro m u hu
  obtain ⟨n, hn⟩ := reach_gcdC (gcdC_some ha hb)
  have hT := final_terminal (Nat.gcd a b)
  obtain ⟨_, hk⟩ := prefix_run closedG diamondG hu hn hT (init_inv a b)
  refine ⟨n - m, hk, fun k' t hk' ht => ?_⟩
  have := (determinate spine rules spine_nodup ins_ok outs_ok spine_ok (init_inv a b)
    hn hT (run_trans hu hk') ht)
  exact ⟨this.1, by omega⟩

/-- Bounded: one bound on the length of every run from the initial store. -/
theorem gcd_hw_graph_bounded {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    ∃ N, ∀ m u, Run (step G) (init a b) m u → m ≤ N :=
  (gcd_hw_graph_computes_gcd ha hb).2.2

theorem run_of_seq {σ : Nat → Store Nat Nat}
    (hσ : ∀ i, ∃ l, step G (σ i) l = some (σ (i + 1))) : ∀ i, Run (step G) (σ 0) i (σ i) := by
  intro i; induction i with
  | zero => exact Run.refl _
  | succ i ih =>
    obtain ⟨l, hl⟩ := hσ i
    exact run_trans ih (Run.cons l hl (Run.refl _))

/-- No infinite run: there is no infinite sequence of firings from the initial
store, on any schedule. -/
theorem gcd_hw_graph_no_infinite_run {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    ¬ ∃ σ : Nat → Store Nat Nat, σ 0 = init a b ∧ ∀ i, ∃ l, step G (σ i) l = some (σ (i + 1)) := by
  rintro ⟨σ, h0, hσ⟩
  obtain ⟨N, hN⟩ := gcd_hw_graph_bounded ha hb
  have := hN (N + 1) (σ (N + 1)) (h0 ▸ run_of_seq hσ (N + 1))
  omega

/-- Every maximal run (one that stops because nothing is enabled) is complete
and ends with `[Nat.gcd a b]` on `out0`; together with
`gcd_hw_graph_no_infinite_run`, every maximal execution is finite and correct. -/
theorem gcd_hw_graph_maximal {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    {m : Nat} {t : Store Nat Nat} (hr : Run (step G) (init a b) m t)
    (hmax : ∀ l, step G t l = none) : t chOut = [Nat.gcd a b] :=
  ((gcd_hw_graph_computes_gcd ha hb).2.1 m t hr hmax).2.1

end Formal.Net.GcdHw.Gcd
