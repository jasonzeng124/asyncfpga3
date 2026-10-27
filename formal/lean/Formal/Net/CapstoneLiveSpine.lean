import Formal.Net.CapstoneCut

/-!
# Probe C-8u (3): the spine part of H_FIRING_BOUND for gcd_hw

`CapstoneLiveRank.rank_live` needs a bound on the number of state changes before the goal.
For the 67 spine channels of gcd_hw (the path of the single control token: 8r's `spL`) this
bound follows from 8r's invariant `Inv` (the circuit's spine offer counts are the walk's
visit counts after some `p` steps) once the walk is known to END.

**H_WALK_ENDS `L`** (`(walk σ L).cur = none`): the walk of the control token over the circuit
spine, steered by the token run's values, stops after `L` steps. Like H_WALK it is a property
of the token run alone, decidable per input `(a, b)`. `Wip/C8r/walkcheck.py` checks that the
walk ends on its 32 vectors (up to 821 steps); it is not proved in Lean for all inputs.

Results:
* `walk_stuck`: an ended walk never moves again; `W_mono`: visit counts only grow.
* **`gcd_hw_spine_offers_bounded`**: under H_CELLS, H_BUNDLE, H_START_ONCE, H_WALK and
  H_WALK_ENDS `L`, at every time every spine channel has offered at most
  `(walk σ L).W c ≤ L` tokens; so its request makes at most `2 L` transitions.
* `gcd_hw_spine_done`: once the circuit's spine counts equal the ended walk's, no spine
  request ever rises again (the control token has left the spine).

What this does NOT bound: the non-spine channels (data paths, the free-running `a`/`b`
sources, condition joins). For them H_FIRING_BOUND is open (C-8u-live.md).
-/

namespace Formal.Net.CapNet.Live
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapSafe (Good)

section walk
variable (σ : Fin NC → Nat → Nat)

theorem walk_stuck {L : Nat} (hL : (walk σ L).cur = none) : ∀ q, L ≤ q → walk σ q = walk σ L := by
  intro q hq
  induction q with
  | zero => have : L = 0 := by omega
            subst this; rfl
  | succ q ih =>
    rcases Nat.eq_or_lt_of_le hq with e | hlt
    · rw [e]
    · have e := ih (by omega)
      show wstep σ (walk σ q) = _
      rw [e]; unfold wstep; rw [hL]

theorem W_mono (c : Fin NC) {p q : Nat} (h : p ≤ q) : (walk σ p).W c ≤ (walk σ q).W c := by
  rw [W_eq, W_eq]; exact cnt_mono _ h

theorem W_le (c : Fin NC) (p : Nat) : (walk σ p).W c ≤ p := by
  rw [W_eq]
  induction p with
  | zero => exact Nat.le_refl _
  | succ p ih => rw [cnt_succ']; unfold bn; split <;> omega

/-- Every visit count reached at any `p` is bounded by the ended walk's. -/
theorem W_le_end {L : Nat} (hL : (walk σ L).cur = none) (c : Fin NC) (p : Nat) :
    (walk σ p).W c ≤ (walk σ L).W c := by
  rcases Nat.le_total p L with h | h
  · exact W_mono σ c h
  · rw [walk_stuck σ hL p h]; exact Nat.le_refl _

end walk

/-- Transitions of a trace before `t` are at most twice its rises plus one. -/
theorem trans_le (s : Trace) : ∀ t, cnt (fun u => s u != s (u + 1)) t ≤ 2 * cnt (riseB s) t + 1 := by
  intro t
  -- transitions = rises + falls, and falls = rises + [s 0] - [s t]
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

/-- **The spine's offers are bounded by the ended walk.** -/
theorem gcd_hw_spine_offers_bounded (a b L : Nat) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1)
    (y : CapSafe.TS) (hy : Good a b y) (H_WALK : WalkOK (σY a b y) (omOf a b y))
    (H_WALK_ENDS : (walk (σY a b y) L).cur = none) :
    ∀ c, sp c = true → ∀ t,
      cnt (riseB (ch c).req) t ≤ (walk (σY a b y) L).W c ∧ (walk (σY a b y) L).W c ≤ L ∧
      cnt (fun u => (ch c).req u != (ch c).req (u + 1)) t ≤ 2 * L + 1 := by
  intro c hc t
  obtain ⟨p, hp⟩ := (main hy H_CELLS H_BUNDLE H_START_ONCE H_WALK t).1
  have h1 : cnt (riseB (ch c).req) t ≤ (walk (σY a b y) L).W c := by
    rw [hp c hc]; exact W_le_end _ H_WALK_ENDS c p
  have h2 := W_le (σY a b y) c L
  refine ⟨h1, h2, ?_⟩
  have := trans_le (ch c).req t
  omega

/-- **After the walk has ended, the spine is silent.** If at `t` the circuit's spine counts
equal the ended walk's, no spine request rises at any later time. -/
theorem gcd_hw_spine_done (a b L : Nat) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1)
    (y : CapSafe.TS) (hy : Good a b y) (H_WALK : WalkOK (σY a b y) (omOf a b y))
    (H_WALK_ENDS : (walk (σY a b y) L).cur = none) {t : Nat}
    (hat : ∀ c, sp c = true → cnt (riseB (ch c).req) t = (walk (σY a b y) L).W c) :
    ∀ c, sp c = true → ∀ t', t ≤ t' → riseB (ch c).req t' = false := by
  intro c hc t' htt'
  cases hr : riseB (ch c).req t'
  · rfl
  · have hb := (gcd_hw_spine_offers_bounded a b L ch H_CELLS H_BUNDLE H_START_ONCE y hy H_WALK
      H_WALK_ENDS c hc (t' + 1)).1
    have hm := cnt_mono (riseB (ch c).req) htt'
    have e1 := cnt_succ_of hr
    have e2 := hat c hc
    omega

end Formal.Net.CapNet.Live
