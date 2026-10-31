import Formal.Cells.ConstraintsFastFall
open Formal.Core.LutList

/-!
# Necessity2Delay: `bd_delay #(.FASTFALL(1))` flush conditions

Probe Bsx2 (shard B). Rows `bd_delay[FASTFALL].flush_per_stage` and
`bd_delay[FASTFALL].flush_uniform` were "sufficient".

Model: ConstraintsFastFall's `FastLineP` (window channels, Kleene closure of
the REAL INITs `2'h2` head and `4'h8` side stages, per-stage hop and tap
windows), taps on the line's own input (`tap = s 0`, the non-gated
`bd_delay`), `a = s 0` low on `[Fa, Ta - 1]`.

## Results

* `FlushClaim slack`: `slow_not_early_ps` (tap = s 0) with every
  H_FLUSH_STAGE weakened by `slack` ticks. `flush0 : FlushClaim 0` (the
  existing theorem). `flush1_false : ¬ FlushClaim 1`: the counter-line
  `N = 2` (head hop 1, chain hop 1 -> 2 of 3, tap hops 1; every delay a
  fixed transport inside its point window, i.e. one corner), `a` low on
  [10, 11], rises at 12. H_FLUSH_STAGE 1 reads `11 + 3 ≤ 12 + 1`: violated
  by exactly 1. Stage 1's last `1` is still on the 3-tick hop when the tap
  re-enables stage 2, so `z = s 2` is HIGH at 13 although the conclusion
  requires it low on [11, 15] (the matched rise is 16). So the per-stage form
  is **necessary at the boundary** (one tick, one parameter point).
* `uniform_not_necessary`: the uniform H_FLUSH `2 hi + thi ≤ (T - F) + tlo`
  is NOT necessary: at chain [1, 3], taps [1, 1], low phase [0, 4], N = 3 it
  fails while every line in the model still meets the conclusion (by
  `slow_not_early_ps`, via `flush_stage_strictly_weaker`), and such a line
  exists (`uw_line`, transport, non-vacuity). Exact replacement:
  `flush_per_stage`.

NOT covered: FASTRISE (`ack_flush`), the gated line (`bd_delay_gated` has
its own taps; the same counter-line shape applies but is not instantiated).
-/

namespace Formal.Cells.Necessity2Delay
open Formal.Cells Formal.Cells.Bundling Formal.Cells.ConstraintsFastFall

/-- `slow_not_early_ps` for `bd_delay #(.FASTFALL(1))` (taps on `s 0`) with
H_FLUSH_STAGE weakened by `slack`. -/
def FlushClaim (slack : Nat) : Prop :=
  ∀ (s : Nat → Sig) (N : Nat) (lo hi tlo thi : Nat → Nat) (Fa Ta : Nat),
    FastLineP s (s 0) N lo hi tlo thi FF_SIDE false →
    StableOn (s 0) false Fa (Ta - 1) →
    (∀ i, 1 ≤ i → i < N → fallBound hi thi Fa Fa i + hi i ≤ Ta + tlo i + slack) →
    ∀ i, 1 ≤ i → i ≤ N → StableOn (s i) false (fallBound hi thi Fa Fa i) (Ta + Lo lo i - 1)

theorem flush0 : FlushClaim 0 := by
  intro s N lo hi tlo thi Fa Ta L ha H
  exact slow_not_early_ps L Fa Ta Fa Ta ha ha H

/-! ## The counter-line (Bundling's `fgS` transport traces, N = 2) -/

def clo : Nat → Nat := fun i => if i = 0 then 1 else 3
def ctl : Nat → Nat := fun _ => 1

theorem cline : FastLineP fgS (fgS 0) 2 clo clo ctl ctl FF_SIDE false := by
  refine fastfall_lineP fgS 2 clo clo ctl ctl (fun _ => Nat.le_refl _) (fun _ => Nat.le_refl _)
    ?_ ?_
  · exact transport_gate BUF [(fgA, 1, 1, 1)] fgS1 (by simp)
      (fun t => by show fgA (t - 1) = lutB BUF [fgA (t - 1)]; rw [buf_bin])
  · intro i h1 h2
    have : i = 1 := by omega
    subst this
    exact transport_gate FF_SIDE [(fgS1, 3, 3, 3), (fgA, 1, 1, 1)] fgS2 (by simp)
      (fun t => by
        show (fgS1 (t - 3) && fgA (t - 1)) = lutB FF_SIDE [fgS1 (t - 3), fgA (t - 1)]
        rw [ff_bin])

/-- H_FLUSH_STAGE 1 fails by exactly one tick: `fallBound 1 + hi 1 = 14 = 12 + 1 + 1`. -/
theorem cline_viol : fallBound clo ctl 10 10 1 + clo 1 = 12 + ctl 1 + 1 := by decide

/-- ... and z = s 2 is high at 13, inside the window [11, 15] the conclusion
requires it low on. -/
theorem cline_early : fgS 2 13 = true ∧ fallBound clo ctl 10 10 2 = 11 ∧
    12 + Lo clo 2 - 1 = 15 := by decide

theorem flush1_false : ¬ FlushClaim 1 := by
  intro h
  have hs := h fgS 2 clo clo ctl ctl 10 12 cline
    (fun t h1 h2 => by
      have : t = 10 ∨ t = 11 := by omega
      rcases this with rfl | rfl <;> decide)
    (fun i h1 h2 => by
      have : i = 1 := by omega
      subst this; decide)
    2 (by omega) (by omega) 13 (by decide) (by decide)
  rw [cline_early.1] at hs; exact absurd hs (by decide)

/-! ## The uniform form is not necessary -/

/-- A transport line at chain [1, 3], taps [1, 1] (hops 3, taps 1), a low
on [0, 4]: non-vacuity of the parameter point below. -/
def uA : Sig := fun t => decide (5 ≤ t)
def uS1 : Sig := fun t => uA (t - 3)
def uS2 : Sig := fun t => uS1 (t - 3) && uA (t - 1)
def uS3 : Sig := fun t => uS2 (t - 3) && uA (t - 1)
def uS : Nat → Sig
  | 0 => uA
  | 1 => uS1
  | 2 => uS2
  | _ => uS3

theorem uw_line : FastLineP uS (uS 0) 3 (fun _ => 1) (fun _ => 3) (fun _ => 1) (fun _ => 1)
    FF_SIDE false := by
  refine fastfall_lineP uS 3 _ _ _ _ (fun _ => by decide) (fun _ => Nat.le_refl _) ?_ ?_
  · exact transport_gate BUF [(uA, 3, 1, 3)] uS1 (by simp)
      (fun t => by show uA (t - 3) = lutB BUF [uA (t - 3)]; rw [buf_bin])
  · intro i h1 h2
    have hi : i = 1 ∨ i = 2 := by omega
    rcases hi with rfl | rfl
    · exact transport_gate FF_SIDE [(uS1, 3, 1, 3), (uA, 1, 1, 1)] uS2 (by simp)
        (fun t => by
          show (uS1 (t - 3) && uA (t - 1)) = lutB FF_SIDE [uS1 (t - 3), uA (t - 1)]
          rw [ff_bin])
    · exact transport_gate FF_SIDE [(uS2, 3, 1, 3), (uA, 1, 1, 1)] uS3 (by simp)
        (fun t => by
          show (uS2 (t - 3) && uA (t - 1)) = lutB FF_SIDE [uS2 (t - 3), uA (t - 1)]
          rw [ff_bin])

/-- **H_FLUSH (uniform) is not necessary.** At chain [1, 3], taps [1, 1],
`a` low on [0, 4] (`F = 0`, `T = 5`), N = 3: H_FLUSH fails, yet EVERY line of
the model with these windows meets the conclusion (no stage rises before the
matched `T + Lo i`), and such a line exists. -/
theorem uniform_not_necessary :
    ¬ (2 * 3 + 1 ≤ (5 - 0) + 1) ∧
    (∀ s : Nat → Sig,
      FastLineP s (s 0) 3 (fun _ => 1) (fun _ => 3) (fun _ => 1) (fun _ => 1) FF_SIDE false →
      StableOn (s 0) false 0 4 →
      ∀ i, 1 ≤ i → i ≤ 3 →
        StableOn (s i) false (fallBound (fun _ => 3) (fun _ => 1) 0 0 i)
          (5 + Lo (fun _ => 1) i - 1)) ∧
    FastLineP uS (uS 0) 3 (fun _ => 1) (fun _ => 3) (fun _ => 1) (fun _ => 1) FF_SIDE false ∧
    StableOn (uS 0) false 0 4 := by
  refine ⟨flush_stage_strictly_weaker.1, fun s L ha => ?_, uw_line, ?_⟩
  · exact slow_not_early_ps L 0 5 0 5 ha ha flush_stage_strictly_weaker.2
  · intro t h1 h2
    show decide (5 ≤ t) = false
    simp; omega

end Formal.Cells.Necessity2Delay
