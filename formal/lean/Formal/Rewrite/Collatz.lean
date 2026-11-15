import Formal.Rewrite.AutoCollatzPreeq2
import Formal.Net.AutoCollatz
import Formal.Rewrite.Diverge

/-!
# Formal.Rewrite.Collatz — research's collatz (32-bit) loop-test rewrite: before and after agree (shard A, 2026-11-15)

**Problem, plainly.** Does the handshake graph of `research/data/fifteen/collatz_preeq2.mlir` (loop test `n == 2`)
return what the original graph (`cloud/fixtures/frontend/collatz/comp/handshake_transformed.mlir`, test `n' == 1`)
returns, for every 32-bit input?

**Proved** (`same`): the two cfront transcriptions are the same function (`kC_same`, by `rfl`: cfront read the same C
for both), so on every input on which the C returns `r`, C's `AutoCollatz.auto_computes` (original graph) and
`AutoCollatzPreeq2.auto_computes` (rewritten graph; its rewrite obligations closed by `Eq2.collatz_eq2`) give: both
graphs have complete runs ending with `[r]`, and every complete run of either ends there.

`same_div`: on inputs on which the C never returns (e.g. `n = 0`, negative cycles), neither graph ever completes a
run. So the two graphs agree on every input. **Not covered:** gates, delays, cells.
-/

namespace Formal.Rewrite.Collatz.Orig
open Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.Auto Formal.Net.CollatzHw Formal.Net.AutoCollatz

theorem pick_some (σ : List Nat) : P.pick 0 σ ≠ none := by
  unfold CProg.pick
  cases h : isT ((P.tests.getD 0 (.lit 0)).eval σ) <;> simp [P, ce0, ce1, List.find?]

theorem edgeN {F : List (E × Bool)} {sched : List Nat} {sig : List E} {Ti Tj : List (List E)}
    (hl : Ti.length = N) (h : execL (symVI F) rules Ti sched = some (Tj.map (List.map (E.subst sig))))
    (hs : 1 ≤ sched.length) (env : List Nat) (hF : FactsOK env F) :
    ∃ n, 1 ≤ n ∧ Run (step G) (St Ti env) n (St Tj (sig.map (E.eval env))) := by
  have := sym_run bounded_ok hl sched h env hF
  rw [lmap_subst] at this
  exact ⟨_, hs, this⟩

theorem hGN : ∀ g ∈ GE, ∀ env : List Nat, isT (g.fact.eval env) = g.br →
    ∃ n, 1 ≤ n ∧ Run (step G) (Tm g.src env) n (Tm g.dst (g.sig.map (E.eval env))) := by
  intro g hg env hf
  simp only [GE, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact edgeN (Ti := T0) (Tj := T1) lenT0 seg0 (by decide) env (fact1 hf)
  · exact edgeN (Ti := T0) (Tj := T2) lenT0 seg1 (by decide) env (fact1 hf)
  · exact edgeN (Ti := T2) (Tj := T1) lenT2 seg2 (by decide) env (fact1 hf)
  · exact edgeN (Ti := T2) (Tj := T2) lenT2 seg3 (by decide) env (fact1 hf)

/-- Where the C never returns, this graph never completes a run. -/
theorem diverges {n₀ : Nat} (h : ∀ fuel, kC fuel n₀ = none) :
    ∀ m t, Run (step G) (St T0 [n₀]) m t → ¬ Terminal (step G) t := by
  intro m t ht hT
  have hK : ∀ k ∈ K, ∀ σ, P.pick (L.getD k 0) σ ≠ none := by
    intro k hk σ
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> exact pick_some σ
  obtain ⟨n, hn, u, hu⟩ := Formal.Rewrite.Diverge.sim_div Tm (fun a n b => Run (step G) a n b) (fun a => Run.refl a)
    (fun h1 h2 => run_trans h1 h2) P L K ρ Is 1 GE M hGN cover hM hK (m + 1) 0 (P.entry.map (E.eval [n₀]))
    (by decide) (hI0 n₀) (fun f => h f)
  rw [hin n₀] at hu
  have := no_longer spine rules spine_nodup ins_ok outs_ok spine_ok (init_inv n₀) ht hT hu
  omega

end Formal.Rewrite.Collatz.Orig

namespace Formal.Rewrite.Collatz.Preeq2
open Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.Auto Formal.Rewrite.CollatzPreeq2Hw Formal.Rewrite.AutoCollatzPreeq2

theorem pick_some (σ : List Nat) : P.pick 0 σ ≠ none := by
  unfold CProg.pick
  cases h : isT ((P.tests.getD 0 (.lit 0)).eval σ) <;> simp [P, ce0, ce1, List.find?]

theorem edgeN {F : List (E × Bool)} {sched : List Nat} {sig : List E} {Ti Tj : List (List E)}
    (hl : Ti.length = N) (h : execL (symVI F) rules Ti sched = some (Tj.map (List.map (E.subst sig))))
    (hs : 1 ≤ sched.length) (env : List Nat) (hF : FactsOK env F) :
    ∃ n, 1 ≤ n ∧ Run (step G) (St Ti env) n (St Tj (sig.map (E.eval env))) := by
  have := sym_run bounded_ok hl sched h env hF
  rw [lmap_subst] at this
  exact ⟨_, hs, this⟩

theorem hGN : ∀ g ∈ GE, ∀ env : List Nat, isT (g.fact.eval env) = g.br →
    ∃ n, 1 ≤ n ∧ Run (step G) (Tm g.src env) n (Tm g.dst (g.sig.map (E.eval env))) := by
  intro g hg env hf
  simp only [GE, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact edgeN (Ti := T0) (Tj := T1) lenT0 seg0 (by decide) env (fact1 hf)
  · exact edgeN (Ti := T0) (Tj := T2) lenT0 seg1 (by decide) env (fact1 hf)
  · exact edgeN (Ti := T2) (Tj := T1) lenT2 seg2 (by decide) env (fact1 hf)
  · exact edgeN (Ti := T2) (Tj := T2) lenT2 seg3 (by decide) env (fact1 hf)

/-- Where the C never returns, this graph never completes a run. -/
theorem diverges {n₀ : Nat} (h : ∀ fuel, kC fuel n₀ = none) :
    ∀ m t, Run (step G) (St T0 [n₀]) m t → ¬ Terminal (step G) t := by
  intro m t ht hT
  have hK : ∀ k ∈ K, ∀ σ, P.pick (L.getD k 0) σ ≠ none := by
    intro k hk σ
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> exact pick_some σ
  obtain ⟨n, hn, u, hu⟩ := Formal.Rewrite.Diverge.sim_div Tm (fun a n b => Run (step G) a n b) (fun a => Run.refl a)
    (fun h1 h2 => run_trans h1 h2) P L K ρ Is 1 GE M hGN cover hM hK (m + 1) 0 (P.entry.map (E.eval [n₀]))
    (by decide) (hI0 n₀) (fun f => h f)
  rw [hin n₀] at hu
  have := no_longer spine rules spine_nodup ins_ok outs_ok spine_ok (init_inv n₀) ht hT hu
  omega

end Formal.Rewrite.Collatz.Preeq2

namespace Formal.Rewrite.Collatz
open Formal.Net.Kahn Formal.Net.GcdHw

theorem kC_same : Formal.Rewrite.AutoCollatzPreeq2.kC = Formal.Net.AutoCollatz.kC := rfl

theorem same {fuel n₀ r : Nat} (h : Formal.Net.AutoCollatz.kC fuel n₀ = some r) :
    ((∃ n, Run (step Formal.Net.AutoCollatz.G) (Formal.Net.AutoCollatz.St Formal.Net.CollatzHw.T0 [n₀]) n
        (Formal.Net.AutoCollatz.St Formal.Net.CollatzHw.T1 [r])) ∧
      ∀ m t, Run (step Formal.Net.AutoCollatz.G) (Formal.Net.AutoCollatz.St Formal.Net.CollatzHw.T0 [n₀]) m t →
        Terminal (step Formal.Net.AutoCollatz.G) t → t = Formal.Net.AutoCollatz.St Formal.Net.CollatzHw.T1 [r]) ∧
    ((∃ n, Run (step Formal.Rewrite.AutoCollatzPreeq2.G)
        (Formal.Rewrite.AutoCollatzPreeq2.St Formal.Rewrite.CollatzPreeq2Hw.T0 [n₀]) n
        (Formal.Rewrite.AutoCollatzPreeq2.St Formal.Rewrite.CollatzPreeq2Hw.T1 [r])) ∧
      ∀ m t, Run (step Formal.Rewrite.AutoCollatzPreeq2.G)
        (Formal.Rewrite.AutoCollatzPreeq2.St Formal.Rewrite.CollatzPreeq2Hw.T0 [n₀]) m t →
        Terminal (step Formal.Rewrite.AutoCollatzPreeq2.G) t →
        t = Formal.Rewrite.AutoCollatzPreeq2.St Formal.Rewrite.CollatzPreeq2Hw.T1 [r]) := by
  have h' : Formal.Rewrite.AutoCollatzPreeq2.kC fuel n₀ = some r := by rw [kC_same]; exact h
  exact ⟨⟨(Formal.Net.AutoCollatz.auto_computes h).1, (Formal.Net.AutoCollatz.auto_computes h).2.1⟩,
    ⟨(Formal.Rewrite.AutoCollatzPreeq2.auto_computes h').1, (Formal.Rewrite.AutoCollatzPreeq2.auto_computes h').2.1⟩⟩


/-- **Where the C never returns, neither graph ever completes a run.** With `same`: the original and the rewritten
collatz graphs agree on EVERY 32-bit input. -/
theorem same_div {n₀ : Nat} (h : ∀ fuel, Formal.Net.AutoCollatz.kC fuel n₀ = none) :
    (∀ m t, Run (step Formal.Net.AutoCollatz.G) (Formal.Net.AutoCollatz.St Formal.Net.CollatzHw.T0 [n₀]) m t →
      ¬ Terminal (step Formal.Net.AutoCollatz.G) t) ∧
    (∀ m t, Run (step Formal.Rewrite.AutoCollatzPreeq2.G)
      (Formal.Rewrite.AutoCollatzPreeq2.St Formal.Rewrite.CollatzPreeq2Hw.T0 [n₀]) m t →
      ¬ Terminal (step Formal.Rewrite.AutoCollatzPreeq2.G) t) :=
  ⟨Orig.diverges h, Preeq2.diverges (fun f => by rw [kC_same]; exact h f)⟩

end Formal.Rewrite.Collatz
