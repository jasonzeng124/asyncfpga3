import Formal.Cells.RaceStaticPS
import Mathlib.Tactic.Linarith

/-!
# Formal.Cells.RaceCornersPS — gcd_ps's tightest race at every corner at once

Shard B, THE goal, S3. Builds on `RaceStaticPS` (whose margin is at corner 1/2 only).

## Problem, plainly
`Spec.Behaves` lets the die sit at any corner `c ∈ [0, 1]`. For storage node gate 120808 of THE target (the link
controller C-element `ulink_n_falseResult_85.many.stage[0].u.ctl.u.u`), is its tightest episode's causal path
(36 arcs, `racePath`) at least as slow as its feedback loop (7 arcs, `raceLoop`) for EVERY corner and EVERY
admissible delay assignment, at g = 1 and some κ?

## Results
* `sum_lower`, `sum_upper`: for any arc list and any delays admissible at `(g = 1, κ, c)`, the delays' sum lies
  between `(1-κ)·lerp(Σ FAST_MIN, Σ SLOW_MIN, c)` and `(1+κ)·lerp(Σ FAST_MAX, Σ SLOW_MAX, c)` (rationals, no
  rounding). Both bounds are linear in `c`.
* `race_all_corners`: at κ = 0.415 (= 83/200), for every corner `c ≥ 0` (so every `c ∈ [0, 1]`) and every admissible delays, the loop's total
  delay is at most the path's. (Sums: path Σ FAST_MIN 1073, Σ SLOW_MIN 2798; loop Σ FAST_MAX 441, Σ SLOW_MAX 1082;
  the margin is smallest at c = 0: 0.585·1073 − 1.415·441 ≈ 3.7 ps.)
* `race_fails_c0`: at κ = 0.425 and corner 0 the integer window ends already let the loop exceed the path
  (`Ua1Static.lo/hi` sums). So for this episode the corner-uniform κ margin lies in [0.415, 0.425).
Simulation agrees: at corner 0 the per-pin adversary is clean at κ = 0.419 and latches a runt at 0.425.

## Not covered
As in `RaceStaticPS`: that this path is what ends the episode in every behaviour (causality), other nodes and
episodes (the scan is simulation), the dynamics. g = 1 only.
-/

namespace Formal.Cells.RaceCornersPS
open Formal.Target Formal.Cells.RaceStaticPS

def sFmin (es : List Arc) : Nat := (es.map Arc.fmin).sum
def sSmin (es : List Arc) : Nat := (es.map Arc.smin).sum
def sFmax (es : List Arc) : Nat := (es.map Arc.fmax).sum
def sSmax (es : List Arc) : Nat := (es.map Arc.smax).sum

theorem sum_lower {p : DelayPar} (hg : p.g = 1) {c : ℚ} :
    ∀ (es : List Arc) (ds : List Nat), List.Forall₂ (fun e d => Adm p c e d) es ds →
      (1 - p.κ) * ((1 - c) * (sFmin es : ℚ) + c * (sSmin es : ℚ)) ≤ ((ds.sum : Nat) : ℚ)
  | [], [], _ => by simp [sFmin, sSmin]
  | e :: es, d :: ds, h => by
    obtain ⟨h1, h2⟩ := List.forall₂_cons.mp h
    have ih := sum_lower hg es ds h2
    have ha := h1.1
    rw [hg, div_one] at ha
    unfold lerp at ha
    simp only [sFmin, sSmin, List.map_cons, List.sum_cons, Nat.cast_add] at ih ⊢
    linarith [ha, ih]

theorem sum_upper {p : DelayPar} (hg : p.g = 1) {c : ℚ} :
    ∀ (es : List Arc) (ds : List Nat), List.Forall₂ (fun e d => Adm p c e d) es ds →
      ((ds.sum : Nat) : ℚ) ≤ (1 + p.κ) * ((1 - c) * (sFmax es : ℚ) + c * (sSmax es : ℚ))
  | [], [], _ => by simp [sFmax, sSmax]
  | e :: es, d :: ds, h => by
    obtain ⟨h1, h2⟩ := List.forall₂_cons.mp h
    have ih := sum_upper hg es ds h2
    have ha := h1.2
    rw [hg, mul_one] at ha
    unfold lerp at ha
    simp only [sFmax, sSmax, List.map_cons, List.sum_cons, Nat.cast_add] at ih ⊢
    linarith [ha, ih]

theorem path_sums : sFmin racePath = 1073 ∧ sSmin racePath = 2798 := by decide +kernel
theorem loop_sums : sFmax raceLoop = 441 ∧ sSmax raceLoop = 1082 := by decide +kernel

/-- **At κ = 0.415, at every corner, every admissible delay assignment makes the episode's causal path at least
as slow as the node's feedback loop** (g = 1). -/
theorem race_all_corners {p : DelayPar} (hg : p.g = 1) (hκ : p.κ = 83 / 200) {c : ℚ} (hc0 : 0 ≤ c)
    {dp dl : List Nat}
    (hp : List.Forall₂ (fun e d => Adm p c e d) racePath dp)
    (hl : List.Forall₂ (fun e d => Adm p c e d) raceLoop dl) : dl.sum ≤ dp.sum := by
  have h1 := sum_lower hg racePath dp hp
  have h2 := sum_upper hg raceLoop dl hl
  rw [path_sums.1, path_sums.2] at h1
  rw [loop_sums.1, loop_sums.2] at h2
  rw [hκ] at h1 h2
  have h3 : ((dl.sum : Nat) : ℚ) ≤ ((dp.sum : Nat) : ℚ) := by
    have : (1 + 83 / 200 : ℚ) * ((1 - c) * ((441 : Nat) : ℚ) + c * ((1082 : Nat) : ℚ)) ≤
        (1 - 83 / 200) * ((1 - c) * ((1073 : Nat) : ℚ) + c * ((2798 : Nat) : ℚ)) := by
      push_cast; linarith
    linarith
  exact_mod_cast h3

/-- At κ = 0.425, corner 0, the integer window ends let the loop exceed the path. -/
theorem race_fails_c0 : pathLo 1 (17/40) 0 < loopHi 1 (17/40) 0 := by decide +kernel

end Formal.Cells.RaceCornersPS
