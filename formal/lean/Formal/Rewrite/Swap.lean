import Formal.Rewrite.IncCmp2Lib

/-!
# Formal.Rewrite.Swap — replacing a compare's function by one that agrees on every reachable input (shard A, 2026-11-18)

**Problem, plainly.** The plain loop test `slt(i, m)` and the corrected one agree whenever `i ≠ INT_MAX` and
`m ≠ INT_MAX`. If those hold for every token that can ever reach the compare, the two graphs behave identically.

**Proved** (`swap_run`, `swap_run_back`, `swap_terminal`): `rs'` equals `rs` except that the two-input compare at label
`C` computes `f2` instead of `f1`; `f1` and `f2` agree on all inputs `a`, `b` with `Q x a` and `Q k b`; and every state
reachable in `rs` from `σ0` satisfies the channel invariant `∀ ch v, v ∈ σ ch → Q ch v`. Then `rs` and `rs'` have
exactly the same runs from `σ0` (same states, same lengths) and the same terminal states.

**Not covered:** proving the invariant (ChanInv.lean); token level only.
-/

namespace Formal.Rewrite.IncCmp

open Formal.Net.Kahn Formal.Net.GcdHw

def SInvS (Q : Nat → Nat → Prop) (σ : Store Nat Nat) : Prop := ∀ ch v, v ∈ σ ch → Q ch v

section Swap

variable {rs rs' : List Rule} {C x k c : Nat} {f1 f2 : E} {Q : Nat → Nat → Prop}

theorem step_swap (hC : rs[C]? = some (.comp [x, k] c f1)) (hC' : rs'[C]? = some (.comp [x, k] c f2))
    (hsame : ∀ l, l ≠ C → rs'[l]? = rs[l]?)
    (hagree : ∀ a b, Q x a → Q k b → f1.eval [a, b] = f2.eval [a, b])
    {σ : Store Nat Nat} (hσ : SInvS Q σ) (l : Nat) : step (graph rs') σ l = step (graph rs) σ l := by
  by_cases hl : l = C
  · subst hl
    rw [step_graph hC', step_graph hC]
    cases hx : σ x with
    | nil => simp [Rule.fire, strictF, heads, hx, Rule.insL]
    | cons a as =>
      cases hk : σ k with
      | nil => simp [Rule.fire, strictF, heads, hx, hk, Rule.insL]
      | cons b bs =>
        have ha : Q x a := hσ x a (by rw [hx]; simp)
        have hb : Q k b := hσ k b (by rw [hk]; simp)
        simp only [Rule.fire, strictF, heads, hx, hk, Rule.out, natVI, Rule.insL]
        simp only [Option.map_some, Option.bind_some, hagree a b ha hb]
  · cases hr : rs[l]? with
    | none => rw [step_graph_none (by rw [hsame l hl, hr]), step_graph_none hr]
    | some r => rw [step_graph (by rw [hsame l hl, hr]), step_graph hr]

variable (hC : rs[C]? = some (.comp [x, k] c f1)) (hC' : rs'[C]? = some (.comp [x, k] c f2))
  (hsame : ∀ l, l ≠ C → rs'[l]? = rs[l]?)
  (hagree : ∀ a b, Q x a → Q k b → f1.eval [a, b] = f2.eval [a, b])
include hC hC' hsame hagree

theorem swap_run {σ0 : Store Nat Nat} (hinv : ∀ m s, Run (step (graph rs)) σ0 m s → SInvS Q s) :
    ∀ {n t}, Run (step (graph rs)) σ0 n t → Run (step (graph rs')) σ0 n t := by
  suffices h : ∀ {s n t}, Run (step (graph rs)) s n t → (∃ m, Run (step (graph rs)) σ0 m s) →
      Run (step (graph rs')) s n t by
    intro n t hr; exact h hr ⟨0, Run.refl _⟩
  intro s n t hr
  induction hr with
  | refl => intro _; exact Run.refl _
  | @cons s s' u k l hl _ ih =>
    intro ⟨m, hm⟩
    refine Run.cons l ?_ (ih ⟨m + 1, run_trans hm (run_one hl)⟩)
    rw [step_swap hC hC' hsame hagree (hinv m s hm) l, hl]

theorem swap_run_back {σ0 : Store Nat Nat} (hinv : ∀ m s, Run (step (graph rs)) σ0 m s → SInvS Q s) :
    ∀ {n t}, Run (step (graph rs')) σ0 n t → Run (step (graph rs)) σ0 n t := by
  suffices h : ∀ {s n t}, Run (step (graph rs')) s n t → (∃ m, Run (step (graph rs)) σ0 m s) →
      Run (step (graph rs)) s n t by
    intro n t hr; exact h hr ⟨0, Run.refl _⟩
  intro s n t hr
  induction hr with
  | refl => intro _; exact Run.refl _
  | @cons s s' u k l hl _ ih =>
    intro ⟨m, hm⟩
    have e : step (graph rs) s l = some s' := by
      rw [← step_swap hC hC' hsame hagree (hinv m s hm) l, hl]
    exact Run.cons l e (ih ⟨m + 1, run_trans hm (run_one e)⟩)

theorem swap_terminal {t : Store Nat Nat} (ht : SInvS Q t) :
    Terminal (step (graph rs')) t ↔ Terminal (step (graph rs)) t := by
  constructor
  · intro h l; rw [← step_swap hC hC' hsame hagree ht l]; exact h l
  · intro h l; rw [step_swap hC hC' hsame hagree ht l]; exact h l

end Swap

end Formal.Rewrite.IncCmp
