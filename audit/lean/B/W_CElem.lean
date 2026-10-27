import Formal.Cells.CElemFn
import Formal.Cells.CElemTiming
/-! Audit (shard B): non-vacuity witnesses for CElemTiming headline theorems. -/
open Formal.Cells Formal.Cells.CElemTiming

namespace AuditB.CElem

/-- square wave: low on [0,4) mod 8, high on [4,8) mod 8 -/
def a : Trace := fun t => decide (4 ≤ t % 8)
def rst : Trace := fun _ => false
def O : Trace := fun t => a (t - 1)
def qp : Trace := fun t => O (t - 1)
def V : Nat → Bool := fun k => decide (k % 2 = 0)
def c : Nat → Nat := fun k => 4 * k + 4

theorem exc_aa (x q : Bool) : exc INIT_c2 x x q false = x := by
  cases x <;> cases q <;> decide

/-- The loop relation of the REAL bd_c2 INIT holds for these traces, dl = dw = 1. -/
theorem loop : Loop INIT_c2 a a rst O qp 1 1 1 1 where
  H_LUT := by
    intro t ht
    refine ⟨t - 1, by omega, by omega, ?_⟩
    simp only [rst, exc_aa]; rfl
  H_FB := by
    intro t ht
    exact ⟨t - 1, by omega, by omega, rfl⟩
  H_LOOP_POS := by decide

theorem a_phase (k s : Nat) (h1 : c k ≤ s) (h2 : s < c (k + 1)) : a s = V k := by
  simp only [a, V, c] at *
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk
  · have : 4 ≤ s % 8 := by omega
    simp [this, hk]
  · have : ¬ (4 ≤ s % 8) := by omega
    simp [this, hk]

/-- **Non-vacuity of `c2_four_phase`**: every hypothesis holds simultaneously
for concrete non-constant traces (infinitely many phases), E = 1. -/
theorem four_phase_hyps :
    Loop INIT_c2 a a rst O qp 1 1 1 1 ∧
    (∀ k, V (k + 1) = !V k) ∧
    (∀ k, c k < c (k + 1)) ∧
    (∀ k, a (c k) = V k ∧ a (c k) = V k) ∧
    (∀ k s, c k ≤ s → s < c (k + 1) → a s = V k ∨ a s = V k) ∧
    (∀ s, c 0 ≤ s → rst s = false) ∧
    (∀ k s, c k ≤ s → (a s ≠ V k ∨ a s ≠ V k) → ∃ u, c k ≤ u ∧ u + 1 ≤ s ∧ O u = V k) ∧
    (1 + 1 ≤ 1 + 1) ∧
    (∀ u, c 0 ≤ u → u < c 0 + 1 → O u = !V 0) := by
  refine ⟨loop, ?_, ?_, ?_, ?_, ?_, ?_, by decide, ?_⟩
  · intro k; simp only [V]
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk
    · have : ¬ ((k+1) % 2 = 0) := by omega
      simp [hk, this]
    · have : ((k+1) % 2 = 0) := by omega
      simp [hk, this]
  · intro k; simp [c]
  · intro k; have := a_phase k (c k) (Nat.le_refl _) (by simp [c]); exact ⟨this, this⟩
  · intro k s h1 h2; exact Or.inl (a_phase k s h1 h2)
  · intro s _; rfl
  · intro k s h1 hne
    have hs : c (k + 1) ≤ s := by
      apply Classical.byContradiction; intro hlt
      have := a_phase k s h1 (by omega)
      rcases hne with h | h <;> exact h this
    refine ⟨c k + 1, by omega, by simp [c] at hs ⊢; omega, ?_⟩
    show a (c k + 1 - 1) = V k
    rw [show c k + 1 - 1 = c k by omega]
    exact a_phase k (c k) (Nat.le_refl _) (by simp [c])
  · intro u h1 h2
    have : u = 4 := by simp [c] at h1 h2; omega
    subst this; decide

/-- ... and the theorem then gives a non-trivial conclusion on this instance. -/
theorem four_phase_applies :
    ∀ k, (∀ t, c k + 1 ≤ t → t + 1 ≤ c (k + 1) + 1 → O t = V k) :=
  fun k => (c2_four_phase loop V c 1 four_phase_hyps.2.1 four_phase_hyps.2.2.1
    four_phase_hyps.2.2.2.1 four_phase_hyps.2.2.2.2.1 four_phase_hyps.2.2.2.2.2.1
    four_phase_hyps.2.2.2.2.2.2.1 (by decide) four_phase_hyps.2.2.2.2.2.2.2.2 k).1

/-- **Non-vacuity of `c2_follow_hold`** (v = 1, window [4, 7]). -/
theorem follow_hold_hyps :
    (∀ s, 4 ≤ s → s < 4 + (1 + 1) → a s = true ∧ a s = true ∧ rst s = false) ∧
    (∀ s, 4 ≤ s → s ≤ 7 → rst s = false) ∧
    (∀ s, 4 ≤ s → s ≤ 7 → a s = true ∨ a s = true) := by
  refine ⟨?_, fun _ _ _ => rfl, ?_⟩
  · intro s h1 h2; have : s = 4 ∨ s = 5 := by omega
    rcases this with rfl | rfl <;> decide
  · intro s h1 h2; left
    have : s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> decide

/-- **Dropping H_PULSE breaks `c2_follow_hold`** (tightness): the runt traces
(dl = dw = 1, pulse width 1 < D = 2) satisfy Loop, H_NORST and H_NOT_BOTH
(v = 1, a = 1 always) on [t0, t2] = [5, 100], yet O is false at 5 + 2 + 1. -/
theorem drop_pulse_cex :
    Loop INIT_c2 aR (bR 1 5) rstR (OR 1 1 1 5) (qpR 1 1 1 5) 1 1 1 1 ∧
    (∀ s, 5 ≤ s → s ≤ 100 → rstR s = false) ∧
    (∀ s, 5 ≤ s → s ≤ 100 → aR s = true ∨ bR 1 5 s = true) ∧
    ¬ (∀ t, 5 + 1 ≤ t → t ≤ 100 + 1 → OR 1 1 1 5 t = true) := by
  refine ⟨runt_loop 1 1 1 5 (by decide) (by decide), fun _ _ _ => rfl,
    fun _ _ _ => Or.inl rfl, ?_⟩
  intro h
  have := h 7 (by decide) (by decide)
  revert this; decide

/-! ### H_ENV_LATENCY is necessary (not only sufficient) for `c2_four_phase`.
Counter-model: dl = 1, dw = 2 (fixed), E = 1, so `dlmax + dwmax = 3 > 2 = dlmin + E`.
Rising phase at 8m+4 (a = b = 1), the environment drops `a` one tick after it saw
O = 1, before the ack has gone round the feedback wire: O glitches low at 8m+7,
inside the window where the theorem promises O = 1. Every OTHER hypothesis holds. -/
def a2 : Trace := fun t => decide (t % 8 = 4 ∨ t % 8 = 5)
def b2 : Trace := fun t => decide (t % 8 = 4 ∨ t % 8 = 5 ∨ t % 8 = 6)
def O2 : Trace := fun t => decide (t % 8 = 5 ∨ t % 8 = 6)
def qp2 : Trace := fun t => O2 (t - 2)
def c2' : Nat → Nat := fun k => 8 * (k / 2) + 4 + 3 * (k % 2)

theorem loop2 : Loop INIT_c2 a2 b2 rst O2 qp2 1 1 2 2 where
  H_LUT := by
    intro t ht
    refine ⟨t - 1, by omega, by omega, ?_⟩
    simp only [rst, c2_eq, a2, b2, qp2, O2]
    have h8 : (t - 1) % 8 = 0 ∨ (t - 1) % 8 = 1 ∨ (t - 1) % 8 = 2 ∨ (t - 1) % 8 = 3 ∨
      (t - 1) % 8 = 4 ∨ (t - 1) % 8 = 5 ∨ (t - 1) % 8 = 6 ∨ (t - 1) % 8 = 7 := by omega
    rcases h8 with h | h | h | h | h | h | h | h <;>
    · have e1 : t % 8 = ((t - 1) % 8 + 1) % 8 := by omega
      by_cases hs : t - 1 < 2
      · have e2 : t - 1 - 2 = 0 := by omega
        rw [e1, e2, h]; simp <;> omega
      · have e2 : (t - 1 - 2) % 8 = ((t - 1) % 8 + 6) % 8 := by omega
        rw [e1, e2, h]; simp
  H_FB := by intro t ht; exact ⟨t - 2, by omega, by omega, rfl⟩
  H_LOOP_POS := by decide

theorem drop_env_latency_cex :
    Loop INIT_c2 a2 b2 rst O2 qp2 1 1 2 2 ∧
    (∀ k, V (k + 1) = !V k) ∧
    (∀ k, c2' k < c2' (k + 1)) ∧
    (∀ k, a2 (c2' k) = V k ∧ b2 (c2' k) = V k) ∧
    (∀ k s, c2' k ≤ s → s < c2' (k + 1) → a2 s = V k ∨ b2 s = V k) ∧
    (∀ s, c2' 0 ≤ s → rst s = false) ∧
    (∀ k s, c2' k ≤ s → (a2 s ≠ V k ∨ b2 s ≠ V k) → ∃ u, c2' k ≤ u ∧ u + 1 ≤ s ∧ O2 u = V k) ∧
    ¬ (1 + 2 ≤ 1 + 1) ∧
    (∀ u, c2' 0 ≤ u → u < c2' 0 + 1 → O2 u = !V 0) ∧
    -- the conclusion of c2_four_phase fails at k = 0, t = 7:
    (c2' 0 + 1 ≤ 7 ∧ 7 + 1 ≤ c2' 1 + 1 ∧ O2 7 ≠ V 0) := by
  refine ⟨loop2, four_phase_hyps.2.1, ?_, ?_, ?_, fun _ _ => rfl, ?_, by decide, ?_, by decide⟩
  · intro k; simp only [c2']; omega
  · intro k; simp only [c2', a2, b2, V]
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk <;> simp [hk] <;> omega
  · intro k s h1 h2; simp only [c2', a2, b2, V] at *
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk
    · right; simp [hk]; omega
    · left; simp [hk]; omega
  · intro k s h1 hne
    simp only [c2', V] at *
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk
    · refine ⟨8 * (k / 2) + 5, by omega, ?_, ?_⟩
      · rcases hne with h | h <;> (simp [a2, b2, hk] at h; omega)
      · simp [O2, hk] <;> omega
    · refine ⟨8 * (k / 2) + 7, by omega, ?_, ?_⟩
      · rcases hne with h | h <;> (simp [a2, b2, hk] at h; omega)
      · simp [O2, hk] <;> omega
  · intro u h1 h2; have : u = 4 := by simp [c2'] at h1 h2; omega
    subst this; decide

end AuditB.CElem
