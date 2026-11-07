import Formal.Net.Bridge
import Formal.Net.Handshake

/-!
# Probe C-8u (1): a ranking theorem for liveness under bounded delays

O5 (circuit liveness of gcd_hw) needs a progress principle that uses only the UPPER delay
bound of every gate and no fairness. This file proves one, generically.

## The abstract principle (`rank_live`)

A system is any trace `s : Nat → σ` of global states, with
* a change marker `chB : Nat → Bool` (`chB u = false` → `s (u+1) = s u`), counted by `cnt`;
* a quiescence predicate `Quiet : σ → Prop` ("no gate is excited");
* a goal `P : Nat → Prop` (e.g. "out0 has offered a token").

Hypotheses, each named:
* **H_FROZEN_QUIET** (what H_BOUNDED_DELAY gives): a state that stays unchanged for `H + 1`
  consecutive ticks is quiescent. For an inertial gate network with every upper bound
  `≤ H` this is a theorem (`timed_frozen_quiet` below): an excited gate whose inputs do not
  move must fire within its `hi`.
* **H_NO_DEADLOCK**: while the goal has not been reached, the state is not quiescent.
* **H_FIRING_BOUND N**: while the goal has not been reached, at most `N` steps change the
  state.

Conclusion: the goal is reached by `(N + 1) * (H + 1)`. Proof: each window of `H + 1` ticks
before the goal contains a change step (H_FROZEN_QUIET + H_NO_DEADLOCK); `N + 1` windows
would need `N + 1` change steps.

No persistence, no fairness and no SI serialisation are used: an excited gate whose
excitation is withdrawn is fine, because withdrawing it needs another change.

## The gate-network instance (`timed_rank_live`)

For a `Bridge.Net` timed trace (every gate an inertial channel `[lo i, hi i]`, `hi i ≤ H`):
H_FROZEN_QUIET is proved (`timed_frozen_quiet`), the change marker is "some node changes"
(`chB_timed`), and the bound reads `(N + 1) * (H + 1)` where `N` bounds the number of
ticks at which some node changes before the goal (at most the number of node transitions).

`timed_rank_unit` is the non-vacuity check: a 2-gate buffer chain at unit delay meets
every hypothesis, and the theorem's bound (here `N = 2`, `H = 1`: 6) is respected (the goal
is reached at `t = 2`).

## What this does NOT give

The two network-specific obligations, H_NO_DEADLOCK and H_FIRING_BOUND, are NOT proved
here for gcd_hw. See `CapstoneLiveArb` (arbiters never need unbounded arbitration time, so
the arbiter grants satisfy H_FROZEN_QUIET), `CapstoneLiveSpine` (the spine part of
H_FIRING_BOUND) and `formal/notes/C-8u-live.md` for what remains.
-/

namespace Formal.Net.CapNet.Live
open Formal.Net Formal.Net.Handshake

/-! ## 1. The abstract ranking theorem -/

theorem cnt_add_le (f : Nat → Bool) {a v b : Nat} (hav : a ≤ v) (hvb : v < b) (hv : f v = true) :
    cnt f a + 1 ≤ cnt f b := by
  have h1 := cnt_mono f hav
  have h2 := cnt_succ_of (f := f) hv
  have h3 := cnt_mono f (show v + 1 ≤ b by omega)
  omega

/-- If no step in `[t, u)` is marked, the state at `u` is the state at `t`. -/
theorem const_of_unmarked {σ : Type} {s : Nat → σ} {chB : Nat → Bool}
    (hch : ∀ u, chB u = false → s (u + 1) = s u) {t : Nat} :
    ∀ u, t ≤ u → (∀ v, t ≤ v → v < u → chB v = false) → s u = s t := by
  intro u htu hno
  induction u with
  | zero => have : t = 0 := by omega
            subst this; rfl
  | succ u ih =>
    rcases Nat.eq_or_lt_of_le htu with e | hlt
    · rw [e]
    · rw [hch u (hno u (by omega) (by omega))]
      exact ih (by omega) (fun v h1 h2 => hno v h1 (by omega))

/-- One window: from a non-quiescent state, a marked step occurs within `H + 1` ticks. -/
theorem window_change {σ : Type} {s : Nat → σ} {Quiet : σ → Prop} {chB : Nat → Bool} {H : Nat}
    (hch : ∀ u, chB u = false → s (u + 1) = s u)
    (H_FROZEN_QUIET : ∀ t, (∀ u, t ≤ u → u ≤ t + H → s u = s t) → Quiet (s t))
    {t : Nat} (hq : ¬ Quiet (s t)) :
    ∃ v, t ≤ v ∧ v < t + H + 1 ∧ chB v = true := by
  apply Classical.byContradiction
  intro hno
  apply hq
  apply H_FROZEN_QUIET
  intro u h1 h2
  apply const_of_unmarked hch u h1
  intro v hv1 hv2
  cases hc : chB v
  · rfl
  · exact absurd ⟨v, hv1, by omega, hc⟩ hno

/-- **The ranking theorem.** Under H_FROZEN_QUIET (bounded delay), H_NO_DEADLOCK and
H_FIRING_BOUND `N`, the goal holds by `(N + 1) * (H + 1)`. -/
theorem rank_live {σ : Type} (s : Nat → σ) (Quiet : σ → Prop) (P : Nat → Prop)
    (chB : Nat → Bool) (H N : Nat)
    (hch : ∀ u, chB u = false → s (u + 1) = s u)
    (H_FROZEN_QUIET : ∀ t, (∀ u, t ≤ u → u ≤ t + H → s u = s t) → Quiet (s t))
    (H_NO_DEADLOCK : ∀ t, ¬ P t → ¬ Quiet (s t))
    (H_FIRING_BOUND : ∀ T, (∀ t, t ≤ T → ¬ P t) → cnt chB T ≤ N) :
    ∃ t, t ≤ (N + 1) * (H + 1) ∧ P t := by
  apply Classical.byContradiction
  intro hno
  have hnp : ∀ t, t ≤ (N + 1) * (H + 1) → ¬ P t := fun t h hp => hno ⟨t, h, hp⟩
  have key : ∀ k, k ≤ N + 1 → k ≤ cnt chB (k * (H + 1)) := by
    intro k
    induction k with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      have hle : k * (H + 1) ≤ (N + 1) * (H + 1) := Nat.mul_le_mul_right _ (by omega)
      obtain ⟨v, hv1, hv2, hv⟩ :=
        window_change hch H_FROZEN_QUIET (H_NO_DEADLOCK _ (hnp _ hle))
      have := cnt_add_le chB hv1 (show v < (k + 1) * (H + 1) by rw [Nat.succ_mul]; omega) hv
      omega
  have h1 := key (N + 1) (Nat.le_refl _)
  have h2 := H_FIRING_BOUND ((N + 1) * (H + 1)) hnp
  omega

/-! ## 2. Gate networks under bounded inertial delays -/

section Timed
open Formal.Net.Bridge
variable {N : Bridge.Net} {lo hi : Nat → Nat} {x : Nat → State}

/-- Quiescent: no gate is excited. -/
def QuietS (N : Bridge.Net) (s : State) : Prop := ∀ i, i < N.n → N.f i s = s i

/-- Change marker of a timed trace: some gate node changes at `u → u+1`. -/
def chT (N : Bridge.Net) (x : Nat → State) (u : Nat) : Bool := !(chg N x u).isEmpty

theorem chT_false (hx : Timed N lo hi x) {u : Nat} (h : chT N x u = false) : x (u + 1) = x u := by
  rw [← final_chg hx u]
  simp only [chT, Bool.not_eq_false', List.isEmpty_iff] at h
  rw [h]; rfl

/-- **H_FROZEN_QUIET, proved for inertial gate networks.** If the state does not change on
`[t, t + H]` and every gate's upper bound is `≤ H`, no gate is excited at `t`. -/
theorem timed_frozen_quiet (hx : Timed N lo hi x) {H : Nat} (hH : ∀ i, i < N.n → hi i ≤ H)
    {t : Nat} (hfz : ∀ u, t ≤ u → u ≤ t + H → x u = x t) : QuietS N (x t) := by
  intro i hi'
  have g := (hx.gate i hi').settle (t + hi i) (by omega) (by
    intro u h1 h2
    show N.f i (x u) = N.f i (x (t + hi i - hi i))
    rw [hfz u (by omega) (by have := hH i hi'; omega), show t + hi i - hi i = t by omega])
  have e := hfz (t + hi i) (by omega) (by have := hH i hi'; omega)
  rw [e] at g
  exact g.symm

/-- **The ranking theorem for gate networks.** Every gate inertial with upper bound `≤ H`
(H_BOUNDED_DELAY); H_NO_DEADLOCK: before the goal some gate is excited; H_FIRING_BOUND:
before the goal at most `M` ticks change some node. Then the goal holds by
`(M + 1) * (H + 1)`. -/
theorem timed_rank_live (hx : Timed N lo hi x) (H M : Nat) (P : Nat → Prop)
    (H_BOUNDED_DELAY : ∀ i, i < N.n → hi i ≤ H)
    (H_NO_DEADLOCK : ∀ t, ¬ P t → ∃ i, i < N.n ∧ N.f i (x t) ≠ x t i)
    (H_FIRING_BOUND : ∀ T, (∀ t, t ≤ T → ¬ P t) → cnt (chT N x) T ≤ M) :
    ∃ t, t ≤ (M + 1) * (H + 1) ∧ P t :=
  rank_live x (QuietS N) P (chT N x) H M (fun _ h => chT_false hx h)
    (fun _ hfz => timed_frozen_quiet hx H_BOUNDED_DELAY hfz)
    (fun t hp hq => by
      obtain ⟨i, hi', he⟩ := H_NO_DEADLOCK t hp
      exact he (hq i hi'))
    H_FIRING_BOUND

/-! ## 3. Non-vacuity: a two-gate buffer chain at unit delay -/

/-- Gate 0 is the constant `true` (an offered request), gate 1 copies gate 0. -/
def buf2 : Bridge.Net := ⟨2, fun i s => if i = 0 then true else s 0⟩

def x0 : State := fun _ => false

theorem buf2_trace : ∀ t, 2 ≤ t → unitTrace buf2 x0 t = unitTrace buf2 x0 2 := by
  intro t ht
  induction t with
  | zero => omega
  | succ t ih =>
    rcases Nat.eq_or_lt_of_le ht with e | hlt
    · rw [← e]
    · have := ih (by omega)
      show stepAll buf2 (unitTrace buf2 x0 t) = _
      rw [this]
      funext j
      simp only [stepAll, unitTrace, buf2]
      by_cases hj : j < 2
      · by_cases h0 : j = 0 <;> simp [h0, hj]
      · simp [hj]

/-- The theorem applies (with `M = 2`, `H = 1`, goal "node 1 is high") and is not
vacuous: every hypothesis holds of the unit-delay run, and the goal is reached at 2. -/
theorem timed_rank_unit :
    ∃ t, t ≤ (2 + 1) * (1 + 1) ∧ unitTrace buf2 x0 t 1 = true := by
  apply timed_rank_live (unit_timed buf2 x0) 1 2 (fun t => unitTrace buf2 x0 t 1 = true)
    (fun _ _ => Nat.le_refl _)
  · intro t hp
    match t, hp with
    | 0, _ => exact ⟨0, by decide, by simp [unitTrace, buf2, x0]⟩
    | 1, _ => exact ⟨1, by decide, by simp [unitTrace, stepAll, buf2, x0]⟩
    | t + 2, hp => exact absurd (by rw [buf2_trace (t + 2) (by omega)]; rfl) hp
  · intro T hT
    have h2 := hT 2
    -- the goal holds at 2, so `T < 2`
    have : T < 2 := by
      apply Classical.byContradiction
      intro h
      exact h2 (by omega) (by rfl)
    match T, this with
    | 0, _ => decide
    | 1, _ => simp only [cnt]; split <;> omega

/-- The goal is reached exactly at 2 in this run (the bound 6 is not tight; it is a bound). -/
theorem timed_rank_unit_at : unitTrace buf2 x0 2 1 = true ∧ unitTrace buf2 x0 1 1 = false := by
  constructor <;> rfl

end Timed

end Formal.Net.CapNet.Live
