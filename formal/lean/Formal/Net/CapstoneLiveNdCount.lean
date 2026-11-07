import Formal.Net.Handshake

/-!
# Probe C-8z (2): counting lemmas for the firing bound

Generic facts about event counts (`cnt`) used to turn per-channel offer bounds into a bound
on the number of state-changing ticks.

* `follow_rises`: a trace `x` that changes only to the current value of a leader `g`
  (`x (t+1) ≠ x t → x (t+1) = g t`: an SI wire, C-element input, LUT AND-term, ...) rises
  at most as often as `g`, plus one if `g` starts high.
* `and_rises`: `r ∧ q`, where `q` cannot move while `r` stays high, rises only when `r` does.
* `cnt_le_sum`: a marker implied by "some marker of a list fires" is counted at most by the
  sum of the list's counts.
-/

namespace Formal.Net.CapNet.Live.Nd
open Formal.Net Formal.Net.Handshake

def bn (b : Bool) : Nat := if b then 1 else 0

theorem follow_inv (x g : Trace) (hf : ∀ t, x (t + 1) ≠ x t → g t = x (t + 1)) :
    ∀ t, cnt (riseB x) t + bn (g t && !x t) ≤ cnt (riseB g) t + bn (g 0) := by
  intro t
  induction t with
  | zero => cases g 0 <;> cases x 0 <;> simp [cnt, bn]
  | succ t ih =>
    have h := hf t
    simp only [cnt, riseB, bn] at ih ⊢
    by_cases h0 : x t = true <;> by_cases h1 : x (t + 1) = true <;> by_cases h2 : g t = true <;>
      by_cases h3 : g (t + 1) = true <;> simp [h0, h1, h2, h3] at ih h ⊢ <;> omega

/-- **Follower count.** -/
theorem follow_rises (x g : Trace) (hf : ∀ t, x (t + 1) ≠ x t → g t = x (t + 1)) (t : Nat) :
    cnt (riseB x) t ≤ cnt (riseB g) t + bn (g 0) := by
  have := follow_inv x g hf t; omega

theorem cnt_le_of_imp {f f' : Nat → Bool} (h : ∀ u, f u = true → f' u = true) :
    ∀ t, cnt f t ≤ cnt f' t := by
  intro t
  induction t with
  | zero => simp [cnt]
  | succ t ih =>
    simp only [cnt]
    cases hf : f t
    · simp; omega
    · simp [h t hf]; omega

/-- A conjunction `r ∧ q` whose second part is frozen while `r` stays high rises only when
`r` rises. -/
theorem and_rises (r q : Trace) (hq : ∀ t, r t = true → r (t + 1) = true → q (t + 1) = q t)
    (t : Nat) : cnt (riseB (fun u => r u && q u)) t ≤ cnt (riseB r) t := by
  apply cnt_le_of_imp _ t
  intro u hu
  simp only [riseB, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hu ⊢
  obtain ⟨h0, h1, h2⟩ := hu
  refine ⟨?_, h1⟩
  cases hr : r u
  · rfl
  · have := hq u hr h1; rw [hr, ← this, h2] at h0; simp at h0

theorem sum_map_add {α : Type} (L : List α) (f g : α → Nat) :
    (L.map (fun x => f x + g x)).sum = (L.map f).sum + (L.map g).sum := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem one_le_sum {α : Type} {L : List α} {f : α → Nat} {x : α} (hx : x ∈ L) (h : 1 ≤ f x) :
    1 ≤ (L.map f).sum := by
  induction L with
  | nil => cases hx
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have := ih hx; omega

/-- **Union count.** -/
theorem cnt_le_sum {α : Type} (L : List α) (m : α → Nat → Bool) (f : Nat → Bool)
    (h : ∀ u, f u = true → ∃ x ∈ L, m x u = true) :
    ∀ T, cnt f T ≤ (L.map (fun x => cnt (m x) T)).sum := by
  intro T
  induction T with
  | zero => simp [cnt]
  | succ T ih =>
    simp only [cnt]
    rw [sum_map_add L (fun x => cnt (m x) T) (fun x => if m x T = true then 1 else 0)]
    cases hf : f T
    · simp; omega
    · obtain ⟨x, hx, hm⟩ := h T hf
      have := one_le_sum (f := fun x => if m x T = true then 1 else 0) hx (by simp [hm])
      simp; omega

theorem sum_le_const {α : Type} (L : List α) (f : α → Nat) (K : Nat) (h : ∀ x ∈ L, f x ≤ K) :
    (L.map f).sum ≤ L.length * K := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have h1 := h a (List.mem_cons_self ..)
    have h2 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    omega

/-- Transitions of a trace before `t` are at most twice its rises plus one (as 8u's
`trans_le`, restated here to keep this file independent). -/
theorem trans_le' (s : Trace) : ∀ t, cnt (fun u => s u != s (u + 1)) t ≤ 2 * cnt (riseB s) t + 1 := by
  intro t
  have key : ∀ t, cnt (fun u => s u != s (u + 1)) t + (if s t then 1 else 0) =
      2 * cnt (riseB s) t + (if s 0 then 1 else 0) := by
    intro t
    induction t with
    | zero => simp [cnt]
    | succ t ih =>
      simp only [cnt, riseB]
      by_cases hz : s 0 = true <;> by_cases h0 : s t = true <;> by_cases h1 : s (t + 1) = true <;>
        simp [hz, h0, h1] at ih ⊢ <;> omega
  have := key t
  split at this <;> split at this <;> omega

end Formal.Net.CapNet.Live.Nd
