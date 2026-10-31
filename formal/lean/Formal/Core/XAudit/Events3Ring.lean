import Formal.Core.XAudit.Events3

/-!
# Formal.Core.XAudit.Events3Ring — a loop whose body is an if-then-else (E5 instance)

Probe A-events3. The control ring of A-events (`ring3`: three `bd_c2n`
stages, stage `j` = `C(c_{j-1}, ¬c_{j+1})`, reset `(1, 0, 0)`) with the request
from stage 1 to stage 2 STEERED by a data-dependent select into two arms
(then / else) and merged by an OR before stage 2: the shape of a loop body
`if (s) then … else …` (gcd's `a > b ? a - b : b - a`), where each arm has its
own bundling delay.

Bands (ILLUSTRATIVE slow corner, steps of 10 ps, as `designs/slow_corner.bands.json`):
LUT [9, 13], route [36, 44], own feedback [27, 33].
* then-arm: route → steer AND (LUT) → route → OR (LUT) → route = [126, 158];
* else-arm: the same plus one `bd_delay` LUT1 + route = [171, 215].

`ring_safe`: for EVERY select sequence `sel` and every behaviour in which the
select seen by each arm's AND gate is that transaction's branch while the
request is high (`SelOK`, the bundling hypothesis), every stage is its reset
value flipped `M t j` times at every time (no X, no glitch, no lost or
duplicated token), the arms carry `filt sel b` of stage 1's count
(per-branch counters, conserving it), and each stage fires at most once per
135 steps in every window.

`skew_neg`: with a longer else-arm (three `bd_delay` stages, [261, 329]) the
skew certificate fails: the arm skew 203 exceeds the one-token cycle through
stage 1 used as certificate (180). This shows the check CAN fail; it does not
show the circuit fails: in this ring stage 1 cannot fire again before the
slow arm's event has reached stage 2, and the simulation
(`events3/choice_sim.py --else 3`) is clean (0/50). `Skew` is sufficient,
not necessary (it uses the merged band `[min lo, max hi]`, not per-arm
causality): a precision loss, recorded in `formal/notes/A-events3.md`. The
circuit-level negative controls are the bundling violation (`Events3.steer_neg`;
simulation 50/50 broken) and slow feedback (`slowfb_neg`; simulation 50/50).
-/

namespace Formal.Core.XAudit.Events3.Ring

open Formal.Core.TraceDiscrete (Sig)
open Formal.Core.XAudit.Events (ph)
open Formal.Core.XAudit.Events2

def net : CNet 3 where
  v := fun j => decide (j.val = 0)
  ar := fun _ => 2
  ar_pos := fun _ => by decide
  src := fun j p => if p.val = 1 then j + 1 else j - 1
  inv := fun _ _ => false
  neg := fun _ p => p.val == 1

/-- Stage 2's request pin (pin 0, reading stage 1) is the choice pin. -/
def ch (sel : Nat → Bool) : Choice net where
  kind := fun j p => j.val == 2 && p.val == 0
  sel := fun _ _ => sel

/-- The bands; `elseX` = number of extra `bd_delay` LUT1 + route stages on the else-arm. -/
def bands (elseX : Nat) : Bands3 net where
  loF := fun _ => 9
  hiF := fun _ => 13
  loA := fun j p a => if j.val == 2 && p.val == 0 then (if a then 126 + 45 * elseX else 126) else 36
  hiA := fun j p a => if j.val == 2 && p.val == 0 then (if a then 158 + 57 * elseX else 158) else 44
  loQ := fun _ => 27
  hiQ := fun _ => 33

/-- Back walks (one arc each, as in ring3). -/
def back : (j : Fin 3) → Fin (net.ar j) → List (Arc net) := fun j p =>
  if p.val = 1 then [⟨j + 1, (0 : Fin 2)⟩] else [⟨j - 1, (1 : Fin 2)⟩]

/-- Skew certificate: the one-token cycle stage 1 → 2 → 1 (through the choice pin). -/
def sk : (j : Fin 3) → Fin (net.ar j) → List (Arc net) := fun _ _ =>
  [⟨1, (1 : Fin 2)⟩, ⟨2, (0 : Fin 2)⟩]

/-- The checks do not depend on the select sequence (only `kind` enters
them): decide them for one sequence, transfer by definitional unfolding. -/
abbrev sel0 : Nat → Bool := fun _ => false

theorem backOK0 : Back ((bands 1).toB (ch sel0)) back := by
  unfold Back; decide +kernel

theorem backOK (sel : Nat → Bool) : Back ((bands 1).toB (ch sel)) back := backOK0

theorem choiceOK0 : ChoiceOK (ch sel0) := by
  unfold ChoiceOK; decide +kernel

theorem choiceOK (sel : Nat → Bool) : ChoiceOK (ch sel) := choiceOK0

theorem skewOK0 : Skew (ch sel0) (bands 1) sk := by
  unfold Skew; decide +kernel

theorem skewOK (sel : Nat → Bool) : Skew (ch sel) (bands 1) sk := skewOK0

/-- The b-pin cycle (one token): stage j fires at most once per its `wLo`. -/
def crit (j : Fin 3) : List (Arc net) := [⟨j, (1 : Fin 2)⟩, ⟨j + 1, (1 : Fin 2)⟩, ⟨j + 2, (1 : Fin 2)⟩]

theorem crit_ok0 : ∀ j, walkOK net j j (crit j) = true ∧ wTok net (crit j) = 1 ∧
    wLo ((bands 1).toB (ch sel0)) (crit j) = 135 := by
  decide +kernel

theorem crit_ok (sel : Nat → Bool) : ∀ j, walkOK net j j (crit j) = true ∧ wTok net (crit j) = 1 ∧
    wLo ((bands 1).toB (ch sel)) (crit j) = 135 := crit_ok0

/-- **A loop with an if-then-else body, every select sequence, all time.** -/
theorem ring_safe (sel : Nat → Bool) (x : Beh3 net (ch sel) (bands 1)) (hsel : x.SelOK) :
    (∀ t j, x.c j t = ph (net.v j) (x.M t j)) ∧
    (∀ t j, x.M (t + 135) j ≤ x.M t j + 1) ∧
    (∀ n, filt sel false n + filt sel true n = n) := by
  refine ⟨x.safe (backOK sel) (choiceOK sel) (skewOK sel) hsel, fun t j => ?_, filt_add sel⟩
  have := x.cycle_le (crit j) j (crit_ok sel j).1 t
  rw [(crit_ok sel j).2.1, (crit_ok sel j).2.2] at this; exact this

/-- NEGATIVE CONTROL (of the check, see the header: conservative here): three
delay stages on the else-arm. The skew (329 − 126 = 203 steps) exceeds the
certificate cycle (180 steps): `Skew` fails. -/
theorem skew_neg0 : ¬ Skew (ch sel0) (bands 3) sk := by
  unfold Skew; decide +kernel

theorem skew_neg (sel : Nat → Bool) : ¬ Skew (ch sel) (bands 3) sk := skew_neg0

/-- NEGATIVE CONTROL: slow own feedback breaks `Back` on the merged bands too. -/
theorem slowfb_neg : ¬ Back { ((bands 1).toB (ch sel0)) with hiQ := fun _ => 150 } back := by
  unfold Back; decide +kernel

end Formal.Core.XAudit.Events3.Ring
