import Formal.Net.AutoLib

/-!
# Formal.Rewrite.Diverge — where the C never returns, the graph runs for ever (shard A, 2026-11-15)

**Problem, plainly.** C's `Auto.sim_call` says: if the C transcription returns `r`, the graph reaches the store with
`[r]`. It says nothing on inputs where the C loops for ever (collatz: `n = 0`, negative cycles). To call two graphs
equivalent on EVERY input we also need: when the C never returns, the graph has arbitrarily long runs (so, being
determinate, it never reaches a terminal store either).

**Proved** (`sim_div`, generic, same correspondence data as `sim_call`): if every graph edge takes at least one
firing, every C test point the correspondence uses has an outgoing C edge for every state (`hpick`), and the C
never returns from a matched state, then from the matched graph state there are runs of every length `≥ N`, for
every `N`.
-/

namespace Formal.Rewrite.Diverge
open Formal.Net.GcdHw Formal.Net.Auto

theorem sim_div {α : Type} (Tm : Nat → List Nat → α) (RunN : α → Nat → α → Prop)
    (refl : ∀ a, RunN a 0 a)
    (trans : ∀ {a b c : α} {m n : Nat}, RunN a m b → RunN b n c → RunN a (m + n) c)
    (P : CProg) (L K : List Nat) (ρ : List (List E)) (Is : List (List (E × E))) (fin : Nat)
    (GE : List GEdge) (M : List Match)
    (hG : ∀ g ∈ GE, ∀ env : List Nat, isT (g.fact.eval env) = g.br →
      ∃ n, 1 ≤ n ∧ RunN (Tm g.src env) n (Tm g.dst (g.sig.map (E.eval env))))
    (hC : Cover P L K fin GE M = true)
    (hM : ∀ m ∈ M, MatchSem P ρ Is m)
    (hpick : ∀ k ∈ K, ∀ σ, P.pick (L.getD k 0) σ ≠ none) :
    ∀ N k σ, k ∈ K → InvH (Is.getD k []) σ → (∀ f, P.run f (L.getD k 0) σ = none) →
      ∃ n, N ≤ n ∧ ∃ u, RunN (Tm k ((ρ.getD k []).map (E.eval σ))) n u := by
  unfold Cover at hC
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    List.any_eq_true, beq_iff_eq] at hC
  obtain ⟨hcov, hms⟩ := hC
  intro N
  induction N with
  | zero => intro k σ _ _ _; exact ⟨0, Nat.le_refl 0, _, refl _⟩
  | succ N ih =>
    intro k σ hk hI hdiv
    cases hp : P.pick (L.getD k 0) σ with
    | none => exact absurd hp (hpick k hk σ)
    | some ce =>
      obtain ⟨hce, hsrc, hb⟩ := pick_spec hp
      have hcv := hcov k hk ce hce
      rcases hcv with hne | ⟨m, hmM, hmk, hmce⟩
      · exact absurd hsrc hne
      subst hmk hmce
      have hmo := hms m hmM
      obtain ⟨⟨⟨hgin, hgs⟩, hcs⟩, hdst⟩ := hmo
      have hgin' : m.g ∈ GE := List.contains_iff_mem.mp hgin
      have sem := hM m hmM σ hI (by rw [hsrc]; exact hb)
      obtain ⟨n0, hn0, step⟩ := hG m.g hgin' _ sem.1
      rw [hgs, sem.2.1] at step
      have hI' := sem.2.2
      unfold target at step
      unfold tinv at hI'
      cases hd : m.ce.dst with
      | none =>
        have h1 := hdiv 1
        simp only [CProg.run, hp, hd] at h1
        cases h1
      | some q =>
        simp only [hd, Bool.and_eq_true, beq_iff_eq] at step hdst hI'
        obtain ⟨hk', hq⟩ := hdst
        have hk'' : m.g.dst ∈ K := List.contains_iff_mem.mp hk'
        have hdiv' : ∀ f, P.run f (L.getD m.g.dst 0) (m.ce.upd.map (E.eval σ)) = none := by
          intro f
          have h1 := hdiv (f + 1)
          simp only [CProg.run, hp, hd] at h1
          rw [hq]; exact h1
        obtain ⟨n, hn, u, hu⟩ := ih m.g.dst _ hk'' hI' hdiv'
        exact ⟨n0 + n, by omega, u, trans step hu⟩

end Formal.Rewrite.Diverge
