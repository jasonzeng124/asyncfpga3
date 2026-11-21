import Formal.Cells.RaceCornersPS

/-!
# Formal.Cells.RaceTablePS — every recorded acknowledgement race of THE target, at every corner

Shard B, THE goal, S3. GENERATED (the table) by tools-B/ps/gen_racetab_ps.py from tools-B/ps/racetab.py output.

## Problem, plainly
For each storage node of gcd_ps whose tightest simulated flipping episode is ended by an acknowledgement of its own
flip (a causal path from its output back to one of its pins, every hop a necessary input in that run), is that
path at least as slow as the node's feedback loop, for EVERY corner and EVERY admissible delay, at g = 1, κ = 0.415?

## Results
* `race_ok_of_sums` (generic): two integer inequalities on a row's arc sums
  (`283·ΣFAST_MAX(loop) ≤ 117·ΣFAST_MIN(path)` and the same with SLOW) imply, at g = 1, κ = 83/200, for every
  corner `c ∈ [0,1]` and every admissible delays, loop total ≤ path total.
* `table_ok`: every row of `raceTable` satisfies them (kernel `decide`).
* `table_race_free`: hence the conclusion for every row.

## Not covered
The rows are GENERATED data (arcs copied from the lean2json rebuild of `Formal/Target/NetPS`; only the binding row
is tied to `DecodedPS.net` by `TargetLinkPS`); which episodes exist in every behaviour (the table is what 32
simulated vectors exercised, corner 0.5 dumps); that these paths end the episodes in every behaviour (necessity
was checked in the simulated runs only; with shard C's speed-independence finding that is the expected shape);
episodes not ended by the node's own flip (data latches: C's relative-timing family).
-/

namespace Formal.Cells.RaceTablePS
open Formal.Target Formal.Cells.RaceCornersPS

theorem race_ok_of_sums {p : DelayPar} (hg : p.g = 1) (hκ : p.κ = 83 / 200) {path loop : List Arc}
    (h1 : 283 * sFmax loop ≤ 117 * sFmin path) (h2 : 283 * sSmax loop ≤ 117 * sSmin path)
    {c : ℚ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {dp dl : List Nat}
    (hp : List.Forall₂ (fun e d => Adm p c e d) path dp)
    (hl : List.Forall₂ (fun e d => Adm p c e d) loop dl) : dl.sum ≤ dp.sum := by
  have l := sum_lower hg path dp hp
  have u := sum_upper hg loop dl hl
  rw [hκ] at l u
  have q1 : (283 : ℚ) * (sFmax loop : ℚ) ≤ 117 * (sFmin path : ℚ) := by exact_mod_cast h1
  have q2 : (283 : ℚ) * (sSmax loop : ℚ) ≤ 117 * (sSmin path : ℚ) := by exact_mod_cast h2
  have a1 := mul_le_mul_of_nonneg_left q1 (by linarith : (0 : ℚ) ≤ 1 - c)
  have a2 := mul_le_mul_of_nonneg_left q2 hc0
  have h3 : ((dl.sum : Nat) : ℚ) ≤ ((dp.sum : Nat) : ℚ) := by nlinarith
  exact_mod_cast h3

/-- A row: storage node gate index, its episode path arcs and feedback-loop arcs. -/
structure Row where
  gate : Nat
  path : List Arc
  loop : List Arc

def rowOK (r : Row) : Bool :=
  283 * sFmax r.loop ≤ 117 * sFmin r.path && 283 * sSmax r.loop ≤ 117 * sSmin r.path

