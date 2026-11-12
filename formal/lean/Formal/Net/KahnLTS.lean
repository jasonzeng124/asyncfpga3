/-!
# Determinacy of a labelled transition system with the diamond property

Abstract layer under `Formal.Net.Kahn` (probe C-8b). Core Lean only.

A system is `step : S → L → Option S`: firing label `l` in state `s` is either
impossible (`none`) or yields exactly one successor. All nondeterminism is the
choice of WHICH enabled label fires. The diamond property says two distinct
enabled labels do not disable each other and commute in one step each.

Results (all for states satisfying an invariant `Inv` closed under steps, so
the dataflow layer can later use "reachable" or an exclusivity invariant):
* `residual`      a label enabled at `s` is taken by every terminating run.
* `prefix_run`    every run from `s` is a prefix of any terminating run from `s`:
                  it is no longer, and can be completed to the same terminal state.
* `terminal_unique` two terminating runs from one state end in the same state and
                  have the same length (strong determinacy, Kahn at token level).
* `no_divergence` if one run from `s` terminates, every run from `s` has length
                  at most that run's: no schedule can loop forever.
-/

namespace Formal.Net.Kahn

section LTS
variable {S L : Type} (step : S → L → Option S)

/-- `Run step s n t`: `t` is reached from `s` by `n` firings. -/
inductive Run : S → Nat → S → Prop
  | refl (s : S) : Run s 0 s
  | cons {s s' t : S} {n : Nat} (l : L) : step s l = some s' → Run s' n t → Run s (n + 1) t

/-- No label is enabled: the run is complete (quiescent). -/
def Terminal (s : S) : Prop := ∀ l, step s l = none

/-- `Inv` is preserved by every firing. -/
def Closed (Inv : S → Prop) : Prop := ∀ s l s', Inv s → step s l = some s' → Inv s'

/-- One-step diamond on `Inv`-states. -/
def DiamondOn (Inv : S → Prop) : Prop :=
  ∀ s l₁ l₂ s₁ s₂, Inv s → l₁ ≠ l₂ → step s l₁ = some s₁ → step s l₂ = some s₂ →
    ∃ u, step s₁ l₂ = some u ∧ step s₂ l₁ = some u

variable {step}

theorem run_trans {s u t : S} {m n : Nat} (h1 : Run step s m u) (h2 : Run step u n t) :
    Run step s (m + n) t := by
  induction h1 with
  | refl => simpa using h2
  | @cons s s' u' k l hl _ ih =>
    have := Run.cons l hl (ih h2)
    rwa [show k + 1 + n = k + n + 1 by omega]

theorem run_refl_eq {s t : S} (h : s = t) : Run step s 0 t := h ▸ Run.refl s

theorem run_from_terminal {s t : S} {k : Nat} (hr : Run step s k t) (ht : Terminal step s) :
    t = s ∧ k = 0 := by
  cases hr with
  | refl => exact ⟨rfl, rfl⟩
  | cons l hl _ => rw [ht l] at hl; cases hl

variable {Inv : S → Prop}

theorem residual (hC : Closed step Inv) (hD : DiamondOn step Inv) :
    ∀ {s n t}, Run step s n t → Terminal step t → Inv s →
      ∀ {l u}, step s l = some u → ∃ k, n = k + 1 ∧ Run step u k t := by
  intro s n t hr
  induction hr with
  | refl s => intro ht _ l u h; rw [ht l] at h; cases h
  | @cons s s' t n a ha hr ih =>
    intro ht hi l u hl
    by_cases hal : a = l
    · subst hal; rw [ha] at hl; cases hl; exact ⟨n, rfl, hr⟩
    · obtain ⟨v, h1, h2⟩ := hD s a l s' u hi hal ha hl
      obtain ⟨k, hk, hv⟩ := ih ht (hC s a s' hi ha) h1
      subst hk
      exact ⟨k + 1, rfl, Run.cons a h2 hv⟩

theorem prefix_run (hC : Closed step Inv) (hD : DiamondOn step Inv) :
    ∀ {s m u}, Run step s m u → ∀ {n t}, Run step s n t → Terminal step t → Inv s →
      m ≤ n ∧ Run step u (n - m) t := by
  intro s m u hr
  induction hr with
  | refl s => intro n t hn _ _; exact ⟨Nat.zero_le _, by simpa using hn⟩
  | @cons s s' u m l hl _ ih =>
    intro n t hn ht hi
    obtain ⟨k, hk, hk'⟩ := residual hC hD hn ht hi hl
    subst hk
    obtain ⟨h1, h2⟩ := ih hk' ht (hC _ _ _ hi hl)
    exact ⟨by omega, by rwa [show k + 1 - (m + 1) = k - m by omega]⟩

/-- Strong determinacy: two complete firing sequences from one state end in the
same state, after the same number of firings. -/
theorem terminal_unique (hC : Closed step Inv) (hD : DiamondOn step Inv)
    {s t t' : S} {n m : Nat} (hi : Inv s)
    (h1 : Run step s n t) (ht : Terminal step t)
    (h2 : Run step s m t') (ht' : Terminal step t') : t' = t ∧ m = n := by
  obtain ⟨hle, hr⟩ := prefix_run hC hD h2 h1 ht hi
  obtain ⟨h, h0⟩ := run_from_terminal hr ht'
  exact ⟨h.symm, by omega⟩

/-- No divergence: if some run from `s` terminates after `n` firings, no run
from `s` (terminating or not) is longer than `n`. -/
theorem no_divergence (hC : Closed step Inv) (hD : DiamondOn step Inv)
    {s t u : S} {n m : Nat} (hi : Inv s)
    (h1 : Run step s n t) (ht : Terminal step t) (h2 : Run step s m u) : m ≤ n :=
  (prefix_run hC hD h2 h1 ht hi).1

theorem closed_true : Closed step (fun _ => True) := fun _ _ _ _ _ => trivial

end LTS

end Formal.Net.Kahn
