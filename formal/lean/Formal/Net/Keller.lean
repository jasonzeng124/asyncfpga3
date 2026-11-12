/-!
# Keller's theorem for persistent transition systems (shard C, composition)

**Problem, plainly.** THE target's control network, read as an abstract machine (storage nodes as
the state, zero-delay logic, "latches first"; tools/cview/hufsim.py, tools/huff/huffx.cpp), seems to
give the same firings and the same results in every order (simulation). Which property of the
machine makes "one run is enough" true, so that a single checked run (a witness) decides every run?

**Proved (generic, any labelled deterministic transition system).** Let `step a s` be the
(partial, deterministic) effect of move `a` in state `s`, and let `R` be a set of states closed
under every move. Assume the **diamond** on `R`: two different moves enabled in the same state stay
enabled after each other and commute (`Diamond`; for a Boolean network whose moves flip one node
each, this is exactly persistence, see `Diamond` below). Then:
* `absorb`: if a run `l₁` from `s ∈ R` ends in a terminal state `τ` (no move enabled) and a move
  `a` is enabled at `s`, then `a ∈ l₁` and the rest, `l₁.erase a`, takes `step a s` to the same `τ`;
* `keller`: every run `l₂` from `s` can be completed by some `l₃` to a run ending in the same `τ`,
  with `l₂ ++ l₃` a permutation of `l₁`;
* `keller_terminal`: every run that ends in a terminal state ends in `τ` and is a permutation of
  `l₁` (same moves, same number of times, same end state: the end state records the results);
* `keller_bounded`: every run from `s` has length at most `l₁.length` (no infinite run: under any
  schedule the machine terminates, which is liveness of the abstract machine).

**Not shown here.** That THE target's machine has the diamond on its reachable states (that is the
obligation this theorem leaves: persistence, to be shown compositionally or by an invariant), nor
anything about timed behaviours.
-/

namespace Formal.Net.Keller

variable {α σ : Type}

/-- Run a list of moves; `none` as soon as a move is not enabled. -/
def run (step : α → σ → Option σ) : List α → σ → Option σ
  | [], s => some s
  | a :: l, s => (step a s).bind (run step l)

/-- A terminal state: no move is enabled. -/
def Terminal (step : α → σ → Option σ) (s : σ) : Prop := ∀ a, step a s = none

/-- `R` is closed under every move. -/
def Closed (step : α → σ → Option σ) (R : σ → Prop) : Prop :=
  ∀ s a t, R s → step a s = some t → R t

/-- **The diamond on `R`**: two different enabled moves stay enabled after each other and lead to
the same state in either order. -/
def Diamond (step : α → σ → Option σ) (R : σ → Prop) : Prop :=
  ∀ s a b sa sb, R s → a ≠ b → step a s = some sa → step b s = some sb →
    ∃ t, step b sa = some t ∧ step a sb = some t

theorem run_cons {step : α → σ → Option σ} {a : α} {l : List α} {s u : σ} :
    run step (a :: l) s = some u ↔ ∃ t, step a s = some t ∧ run step l t = some u := by
  simp only [run]
  cases h : step a s with
  | none => simp
  | some t => simp

theorem run_append {step : α → σ → Option σ} :
    ∀ (l₁ l₂ : List α) (s u : σ),
      run step (l₁ ++ l₂) s = some u ↔ ∃ t, run step l₁ s = some t ∧ run step l₂ t = some u
  | [], l₂, s, u => by simp [run]
  | a :: l₁, l₂, s, u => by
    rw [List.cons_append, run_cons]
    constructor
    · rintro ⟨t, ht, hr⟩
      obtain ⟨m, hm, hm2⟩ := (run_append l₁ l₂ t u).1 hr
      exact ⟨m, run_cons.2 ⟨t, ht, hm⟩, hm2⟩
    · rintro ⟨m, hm, hm2⟩
      obtain ⟨t, ht, hr⟩ := run_cons.1 hm
      exact ⟨t, ht, (run_append l₁ l₂ t u).2 ⟨m, hr, hm2⟩⟩

theorem closed_run {step : α → σ → Option σ} {R : σ → Prop} (hC : Closed step R) :
    ∀ (l : List α) (s u : σ), R s → run step l s = some u → R u
  | [], s, u, hs, h => by simp [run] at h; exact h ▸ hs
  | a :: l, s, u, hs, h => by
    obtain ⟨t, ht, hr⟩ := run_cons.1 h
    exact closed_run hC l t u (hC s a t hs ht) hr

/-- **One move is absorbed by a terminating run.** -/
theorem absorb [DecidableEq α] {step : α → σ → Option σ} {R : σ → Prop} (hC : Closed step R) (hD : Diamond step R) :
    ∀ (l₁ : List α) (s τ : σ) (a : α) (sa : σ), R s → run step l₁ s = some τ → Terminal step τ →
      step a s = some sa → a ∈ l₁ ∧ run step (l₁.erase a) sa = some τ
  | [], s, τ, a, sa, _, h, hT, ha => by
    simp [run] at h; subst h; rw [hT a] at ha; cases ha
  | b :: l, s, τ, a, sa, hs, h, hT, ha => by
    obtain ⟨sb, hb, hr⟩ := run_cons.1 h
    by_cases hab : b = a
    · subst hab
      rw [hb] at ha; cases ha
      refine ⟨List.mem_cons_self, ?_⟩
      simp only [List.erase_cons_head]; exact hr
    · obtain ⟨t, hbt, hat⟩ := hD s a b sa sb hs (Ne.symm hab) ha hb
      obtain ⟨hmem, hrun⟩ := absorb hC hD l sb τ a t (hC s b sb hs hb) hr hT hat
      refine ⟨List.mem_cons_of_mem _ hmem, ?_⟩
      rw [List.erase_cons_tail (by simpa using hab)]
      exact run_cons.2 ⟨t, hbt, hrun⟩

/-- **Keller's theorem.** Every run from `s` extends to a permutation of a terminating run `l₁`,
ending in the same terminal state. -/
theorem keller [DecidableEq α] {step : α → σ → Option σ} {R : σ → Prop} (hC : Closed step R) (hD : Diamond step R) :
    ∀ (l₂ l₁ : List α) (s τ ρ : σ), R s → run step l₁ s = some τ → Terminal step τ →
      run step l₂ s = some ρ → ∃ l₃, run step l₃ ρ = some τ ∧ (l₂ ++ l₃).Perm l₁
  | [], l₁, s, τ, ρ, _, h1, _, h2 => by
    simp [run] at h2; subst h2; exact ⟨l₁, h1, List.Perm.refl _⟩
  | a :: l, l₁, s, τ, ρ, hs, h1, hT, h2 => by
    obtain ⟨sa, ha, hr⟩ := run_cons.1 h2
    obtain ⟨hmem, hrun⟩ := absorb hC hD l₁ s τ a sa hs h1 hT ha
    obtain ⟨l₃, h3, hp⟩ := keller hC hD l (l₁.erase a) sa τ ρ (hC s a sa hs ha) hrun hT hr
    refine ⟨l₃, h3, ?_⟩
    exact (List.Perm.cons a hp).trans (List.perm_cons_erase hmem).symm

/-- Every terminating run ends in the same state and is a permutation of `l₁`. -/
theorem keller_terminal [DecidableEq α] {step : α → σ → Option σ} {R : σ → Prop} (hC : Closed step R)
    (hD : Diamond step R) (l₁ l₂ : List α) (s τ ρ : σ) (hs : R s) (h1 : run step l₁ s = some τ)
    (hT : Terminal step τ) (h2 : run step l₂ s = some ρ) (hT2 : Terminal step ρ) :
    ρ = τ ∧ l₂.Perm l₁ := by
  obtain ⟨l₃, h3, hp⟩ := keller hC hD l₂ l₁ s τ ρ hs h1 hT h2
  cases l₃ with
  | nil => simp [run] at h3; exact ⟨h3, by simpa using hp⟩
  | cons b l => obtain ⟨t, hb, _⟩ := run_cons.1 h3; rw [hT2 b] at hb; cases hb

/-- **No run is longer than a terminating one** (so under every schedule the system terminates
within `l₁.length` moves). -/
theorem keller_bounded [DecidableEq α] {step : α → σ → Option σ} {R : σ → Prop} (hC : Closed step R)
    (hD : Diamond step R) (l₁ l₂ : List α) (s τ ρ : σ) (hs : R s) (h1 : run step l₁ s = some τ)
    (hT : Terminal step τ) (h2 : run step l₂ s = some ρ) : l₂.length ≤ l₁.length := by
  obtain ⟨l₃, _, hp⟩ := keller hC hD l₂ l₁ s τ ρ hs h1 hT h2
  have := hp.length_eq
  simp at this; omega

/-! ## Boolean networks: the diamond is persistence -/

/-- A Boolean network over nodes `α`: node `i` is excited in `v` when its next-state function
disagrees with its value; a move flips one excited node. -/
def flipStep [DecidableEq α] (F : (α → Bool) → α → Bool) (i : α) (v : α → Bool) : Option (α → Bool) :=
  if F v i ≠ v i then some (fun j => if j = i then !v i else v j) else none

/-- **Persistence** on `R`: firing an excited node never disables another excited node. -/
def Persistent [DecidableEq α] (F : (α → Bool) → α → Bool) (R : (α → Bool) → Prop) : Prop :=
  ∀ v i j, R v → i ≠ j → F v i ≠ v i → F v j ≠ v j →
    F (fun k => if k = j then !v j else v k) i ≠ v i

/-- For a Boolean network, persistence gives the diamond (flips of different nodes commute). -/
theorem diamond_of_persistent [DecidableEq α] (F : (α → Bool) → α → Bool) (R : (α → Bool) → Prop)
    (hP : Persistent F R) : Diamond (flipStep F) R := by
  intro v a b va vb hv hab ha hb
  unfold flipStep at ha hb
  by_cases ea : F v a ≠ v a
  · by_cases eb : F v b ≠ v b
    · rw [ite_eq_left ea] at ha; rw [ite_eq_left eb] at hb
      cases ha; cases hb
      have pa := hP v a b hv hab ea eb
      have pb := hP v b a hv (Ne.symm hab) eb ea
      refine ⟨fun j => if j = a then !v a else if j = b then !v b else v j, ?_, ?_⟩
      · unfold flipStep
        have : F (fun j => if j = a then !v a else v j) b ≠ (if b = a then !v a else v b) := by
          rw [ite_eq_right (Ne.symm hab)]; exact pb
        rw [ite_eq_left this]; congr 1; funext j
        by_cases hja : j = a
        · subst hja; simp [hab]
        · by_cases hjb : j = b
          · subst hjb; simp [hja]
          · simp [hja, hjb]
      · unfold flipStep
        have : F (fun j => if j = b then !v b else v j) a ≠ (if a = b then !v b else v a) := by
          rw [ite_eq_right hab]; exact pa
        rw [ite_eq_left this]; congr 1; funext j
        by_cases hja : j = a
        · subst hja; simp [hab]
        · by_cases hjb : j = b
          · subst hjb; simp [hja]
          · simp [hja, hjb]
    · rw [ite_eq_right eb] at hb; cases hb
  · rw [ite_eq_right ea] at ha; cases ha

end Formal.Net.Keller
