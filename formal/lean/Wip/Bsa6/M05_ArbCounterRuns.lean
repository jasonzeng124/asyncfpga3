-- MUTANT M05_ArbCounterRuns of Formal/Cells/ArbCounterRuns.lean: boundary record D1S with smin 171 -> 170 (the violating value) (must FAIL)
import Formal.Cells.OnGcdArb
import Formal.Cells.ArbCorners

/-!
# Probe Bcr (part 1): constructed violating runs for `bd_arbiter.rt1` and `bd_arbcell.handover_overlap`

Shard B, 2026-10-29. Core Lean (no Mathlib). Note: `formal/notes/B-arb-counter-runs.md`.

The label rule of `cell_constraints.json` (`conventions.exactness`, Bj10) asks, for a
necessity label, an iff or a CONSTRUCTED violating run. The two rows here had only
counter-lemmas over supplied runs (`ArbHeldTimed.rt1_counter_minserver` takes `Run` and
`Scn` as hypotheses; `ArbHandover.overlap_exists_r2_to_r1` takes a `Cell` trace). This file
builds the runs and feeds them to those lemmas, so each result is a closed theorem.

## rt1 (7h, client 1 releases, client 2 waits)

`D1V` is a 7h delay record INSIDE the independent box of the routed arbiter
`gd_merge9_uarb1` (seed d; `OnGcdArb.BoxReal1` between its FMIN and SMAX rows, at the box's
worst point `mix1`, server-free margin `m1 = -395`), with every route and arc NONZERO:
ustate's O6 arc 124 ps (SMAX), A0's route to ustate 100 ps, and a server answering in
`smin = 170` ps, so the server-side sum `smin + wa0s + qf = 394` misses the need 395 by
exactly 1 ps. `W1V` is a run of 7h's gate relations (`Run`: the real INITs through
`FS`/`FR`/`FG1`/`FG2`/`CE`, the rise-fast OR channel per LUT, the server relation, every
`t ∈ ℤ`), meeting the handover scenario `Scn` for every horizon past A0's re-rise. On it
`rt1_counter_minserver` gives both grants high at 1634 (a 1 ps overlap). The slack-0
companion `D1S`/`W1S` (`smin = 171`, all else equal) satisfies RT1 and `rt1_exclusion`
holds on its run.

## handover_overlap (7e, bare `bd_arbcell`, r2 → r1)

For EVERY arc record `A` and every `t0`, `hoTrace A t0` is a `Cell` trace of the handover
scenario (`ho_cell`, no hypothesis beyond 7e's `Arcs`). Hence the 7e statements become
statements about an existing run: `ho_overlap_iff` (an overlap exists on the constructed run
iff `qr + w + g1r_q < g2f`). At the SLOW_MAX corner with q routing `w = 20` ps and an O6
rise/fall asymmetry `d6 = o5q + w + 1 = 171` ps (H_RF_ASYM, unmeasured), the constructed run
has exactly 1 ps of overlap (`ho_counter_run`, via `ArbCorners.overlap_C`); at `d6 = 170`
none (`ho_boundary_run`).

**Assumed:** 7h's and 7e's gate models unchanged (imported, not restated); C-10j's routed
rows for `gd_merge9_uarb1` (UNTRUSTED extraction, as in `OnGcdArb`). The traces were
produced by an untrusted simulation (`/tmp/claude-0/probes/Bcr/sim.py`, scratch) and are
CHECKED here against every gate relation for all `t ∈ ℤ`.
**Proved:** the runs exist and violate the conclusions.
**NOT covered:** the rt1 counter-record's fields outside the box (A0 route to ustate,
ustate's O6 arc, the server) are free choices, not routed numbers; RT1's second (structural)
disjunct fails at the routed numbers by 75 ps, not by 1 (`g1fq = 120`, `g2r = 45`). The
handover counter-run needs a rise/fall asymmetry of 171 ps; at every consistent corner the
overlap is 0 (`ArbCorners.corner_no_overlap`), so this run is not a physical claim about the
board.
-/

namespace Formal.Cells.ArbCounterRuns
open Formal.Cells Formal.Cells.ArbHeldTimed Formal.Cells.ArbHeldTimed2 Formal.Cells.OnGcdArb
open Formal.Timing.RuntAck Formal.Timing.RuntAck.Inst

/-- Every route, arc and the server minimum of a 7h record is strictly positive. -/
def AllPos (D : Dl) : Prop :=
  0 < D.wr1s ∧ 0 < D.wr2s ∧ 0 < D.wr1g ∧ 0 < D.wr2g ∧ 0 < D.wfb ∧ 0 < D.wa0s ∧ 0 < D.wq ∧
  0 < D.wg1 ∧ 0 < D.wa01 ∧ 0 < D.wfa1 ∧ 0 < D.wg2 ∧ 0 < D.wa02 ∧ 0 < D.wfa2 ∧ 0 < D.qr ∧
  0 < D.qf ∧ 0 < D.Rr1 ∧ 0 < D.Rf1 ∧ 0 < D.Rr2 ∧ 0 < D.Rf2 ∧ 0 < D.Rrq ∧ 0 < D.Rfq ∧
  0 < D.g1r1 ∧ 0 < D.g1f1 ∧ 0 < D.g1r2 ∧ 0 < D.g1f2 ∧ 0 < D.g1rq ∧ 0 < D.g1fq ∧ 0 < D.g2r ∧
  0 < D.g2f ∧ 0 < D.c1r ∧ 0 < D.c1f ∧ 0 < D.c2r ∧ 0 < D.c2f ∧ 0 < D.smin

/-! ## rt1: the routed box of `gd_merge9_uarb1`, slack −1 and slack 0 -/

/-- The box ends: FMIN and SMAX rows of `gd_merge9_uarb1` (C-10j). -/
def lo9 : Q := ofRows gd_merge9_uarb1_FMIN_c1 gd_merge9_uarb1_FMIN_c2
def hi9 : Q := ofRows gd_merge9_uarb1_SMAX_c1 gd_merge9_uarb1_SMAX_c2

theorem box9 : lo9.le hi9 = true ∧ (mix1 lo9 hi9).m1 = -395 := by decide

/- The records (generated): box worst point on RT1's seven terms (wr1s 76, wr1g 482,
g1f1 153, Rf1 48, wq 71, g2r 45, g1fq 120), every other arc at its own pin's value inside
[FMIN, SMAX] or a free nonzero choice, rise = fall on every arc. `D1V`: smin 170 (slack −1);
`D1S`: smin 171 (slack 0). Traces: client 1 holds (A0 rose at 0), drops r1 at 1000; client 2
waits for ever; the server answers both edges in exactly smin. -/

def D1V : Dl where
  wr1s := 76
  wr2s := 218
  wr1g := 482
  wr2g := 210
  wfb := 50
  wa0s := 100
  wq := 71
  wg1 := 100
  wa01 := 100
  wfa1 := 50
  wg2 := 100
  wa02 := 100
  wfa2 := 50
  qr := 124
  qf := 124
  Rr1 := 48
  Rf1 := 48
  Rr2 := 44
  Rf2 := 44
  Rrq := 43
  Rfq := 43
  g1r1 := 153
  g1f1 := 153
  g1r2 := 42
  g1f2 := 42
  g1rq := 120
  g1fq := 120
  g2r := 45
  g2f := 45
  c1r := 45
  c1f := 45
  c2r := 45
  c2f := 45
  smin := 170
  H_NONNEG := by decide
  H_RISE_LE_FALL := by decide
  H_LOOP_POS := by decide

def W1V : Sigs where
  r1 := fun t => decide (t < 1000)
  r2 := fun _ => true
  q := fun t => decide (t < 1518)
  R0 := fun t => decide (t < 1124) || decide (1611 ≤ t)
  g1 := fun t => decide (t < 1635)
  g2 := fun t => decide (1634 ≤ t)
  A0 := fun t => (decide (0 ≤ t) && decide (t < 1294)) || decide (1781 ≤ t)
  A1 := fun t => decide (t < 1780)
  A2 := fun t => decide (1926 ≤ t)

theorem W1V_run : Run D1V W1V where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [W1V, D1V, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [W1V, D1V, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [W1V, D1V, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [W1V, D1V, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [W1V, D1V, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [W1V, D1V, CE_eq]; omega
  H_SRV := by
    intro t h
    have ht : t = 0 ∨ t = 1294 ∨ t = 1781 :=
      Classical.byContradiction fun hc => h (by rw [Bool.eq_iff_iff]; simp [W1V]; omega)
    refine ⟨t - 170, by simp [D1V], by rw [Bool.eq_iff_iff]; simp [W1V]; omega, ?_⟩
    intro v h1 h2
    rw [Bool.eq_iff_iff]; simp [W1V]; omega

def D1S : Dl where
  wr1s := 76
  wr2s := 218
  wr1g := 482
  wr2g := 210
  wfb := 50
  wa0s := 100
  wq := 71
  wg1 := 100
  wa01 := 100
  wfa1 := 50
  wg2 := 100
  wa02 := 100
  wfa2 := 50
  qr := 124
  qf := 124
  Rr1 := 48
  Rf1 := 48
  Rr2 := 44
  Rf2 := 44
  Rrq := 43
  Rfq := 43
  g1r1 := 153
  g1f1 := 153
  g1r2 := 42
  g1f2 := 42
  g1rq := 120
  g1fq := 120
  g2r := 45
  g2f := 45
  c1r := 45
  c1f := 45
  c2r := 45
  c2f := 45
  smin := 170
  H_NONNEG := by decide
  H_RISE_LE_FALL := by decide
  H_LOOP_POS := by decide

def W1S : Sigs where
  r1 := fun t => decide (t < 1000)
  r2 := fun _ => true
  q := fun t => decide (t < 1519)
  R0 := fun t => decide (t < 1124) || decide (1612 ≤ t)
  g1 := fun t => decide (t < 1635)
  g2 := fun t => decide (1635 ≤ t)
  A0 := fun t => (decide (0 ≤ t) && decide (t < 1295)) || decide (1783 ≤ t)
  A1 := fun t => decide (t < 1780)
  A2 := fun t => decide (1928 ≤ t)

theorem W1S_run : Run D1S W1S where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [W1S, D1S, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [W1S, D1S, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [W1S, D1S, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [W1S, D1S, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [W1S, D1S, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [W1S, D1S, CE_eq]; omega
  H_SRV := by
    intro t h
    have ht : t = 0 ∨ t = 1295 ∨ t = 1783 :=
      Classical.byContradiction fun hc => h (by rw [Bool.eq_iff_iff]; simp [W1S]; omega)
    refine ⟨t - 171, by simp [D1S], by rw [Bool.eq_iff_iff]; simp [W1S]; omega, ?_⟩
    intro v h1 h2
    rw [Bool.eq_iff_iff]; simp [W1S]; omega

theorem W1V_scn (Hz : Int) (hz : 1781 < Hz) : Scn D1V W1V 1000 0 1294 1781 Hz where
  H_ORDER := by omega
  H_r1 := fun _ _ => rfl
  H_r2 := fun _ _ => rfl
  H_A0 := by intro t h1 _; rw [Bool.eq_iff_iff]; simp [W1V]; omega
  H_A0_prev := by decide
  H_q_init := by intro t h; simp [W1V]; omega
  H_A1_init := by intro t h; simp [W1V]; omega
  H_A2_init := by intro t h; simp [W1V]; omega
  H_SETTLED := by decide

theorem W1S_scn (Hz : Int) (hz : 1783 < Hz) : Scn D1S W1S 1000 0 1295 1783 Hz where
  H_ORDER := by omega
  H_r1 := fun _ _ => rfl
  H_r2 := fun _ _ => rfl
  H_A0 := by intro t h1 _; rw [Bool.eq_iff_iff]; simp [W1S]; omega
  H_A0_prev := by decide
  H_q_init := by intro t h; simp [W1S]; omega
  H_A1_init := by intro t h; simp [W1S]; omega
  H_A2_init := by intro t h; simp [W1S]; omega
  H_SETTLED := by decide

theorem D1V_box : BoxReal1 lo9 hi9 0 0 D1V := by unfold BoxReal1; decide
theorem D1S_box : BoxReal1 lo9 hi9 0 0 D1S := by unfold BoxReal1; decide

/-- RT1's race disjunct misses by exactly 1 ps; the structural disjunct fails too. -/
theorem D1V_slack : D1V.wr1g + D1V.g1f1 =
    D1V.wr1s + D1V.Rf1 + D1V.smin + D1V.wa0s + D1V.qf + D1V.wq + D1V.g2r + 1 ∧
    D1V.g2r < D1V.g1fq := by decide
theorem D1V_not_rt1 : ¬ RT1 D1V := by unfold RT1; decide
theorem D1S_rt1 : RT1 D1S := by unfold RT1; decide
theorem D1V_fast : (1294 : Int) = TR D1V 1000 + D1V.smin := by decide

/-- **rt1: constructed violating run (slack −1), inside the routed box.** A 7h record in
the independent box of `gd_merge9_uarb1` (every delay nonzero) misses RT1's race disjunct
by exactly 1 ps (its structural disjunct fails too); `W1V` is a run of the gate relations
for all `t` with a server answering in `smin`, meeting `Scn` for every horizon past 1781;
7h's own `rt1_counter_minserver` gives both grants high at 1634 on it. -/
theorem rt1_counter_run :
    BoxReal1 lo9 hi9 0 0 D1V ∧ AllPos D1V ∧
    D1V.wr1g + D1V.g1f1 =
      D1V.wr1s + D1V.Rf1 + D1V.smin + D1V.wa0s + D1V.qf + D1V.wq + D1V.g2r + 1 ∧
    ¬ RT1 D1V ∧ Run D1V W1V ∧ (∀ Hz, 1781 < Hz → Scn D1V W1V 1000 0 1294 1781 Hz) ∧
    (1294 : Int) = TR D1V 1000 + D1V.smin ∧
    W1V.g1 1634 = true ∧ W1V.g2 1634 = true := by
  have h := rt1_counter_minserver W1V_run (W1V_scn 2000 (by omega)) D1V_fast D1V_not_rt1
    (by decide)
  have e : G2 D1V 1294 = 1634 := by decide
  rw [e] at h
  exact ⟨D1V_box, by unfold AllPos; decide, D1V_slack.1, D1V_not_rt1, W1V_run, W1V_scn,
    D1V_fast, h.1, h.2⟩

/-- **rt1, slack 0 (the other side of the boundary).** Same record with `smin = 171`: RT1
holds, and on the constructed run `rt1_exclusion` gives no overlap below every horizon. -/
theorem rt1_boundary_run :
    BoxReal1 lo9 hi9 0 0 D1S ∧ AllPos D1S ∧
    D1S.wr1g + D1S.g1f1 = D1S.wr1s + D1S.Rf1 + D1S.smin + D1S.wa0s + D1S.qf + D1S.wq + D1S.g2r ∧
    RT1 D1S ∧ Run D1S W1S ∧ (∀ Hz, 1783 < Hz → Scn D1S W1S 1000 0 1295 1783 Hz) ∧
    (∀ Hz, 1783 < Hz → ∀ t, t < Hz → (W1S.g1 t && W1S.g2 t) = false) :=
  ⟨D1S_box, by unfold AllPos; decide, by decide, D1S_rt1, W1S_run, W1S_scn,
    fun Hz hz => rt1_exclusion W1S_run (W1S_scn Hz hz) D1S_rt1⟩

/-! ## handover_overlap: a Cell trace for every arc record -/

section Handover
open Formal.Cells.ArbHandover Formal.Cells.ArbCorners

/-- The r2 → r1 handover trace (r1 waits, r2 drops at `t0`) for arc record `A`. -/
def hoR1 : Int → Bool := fun _ => true
def hoR2 (t0 : Int) : Int → Bool := fun t => decide (t < t0)
def hoQ (A : Arcs) (t0 : Int) : Int → Bool := fun t => decide (t0 + A.qr ≤ t)
def hoG1 (A : Arcs) (t0 : Int) : Int → Bool := fun t => decide (t0 + (A.qr + A.w + A.g1r_q) ≤ t)
def hoG2 (A : Arcs) (t0 : Int) : Int → Bool := fun t => decide (t < t0 + A.g2f)

/-- **For every arc record, the handover scenario has a `Cell` trace.** -/
theorem ho_cell (A : Arcs) (t0 : Int) :
    Cell A hoR1 (hoR2 t0) (hoQ A t0) (hoG1 A t0) (hoG2 A t0) := by
  have := A.H_nonneg; have := A.H_rise_le_fall
  refine ⟨?_, ?_, ?_⟩ <;> intro t <;> rw [Bool.eq_iff_iff] <;>
    simp [hoR1, hoR2, hoQ, hoG1, hoG2, stateF_eqn, g1F_eqn, g2F_eqn] <;> omega

theorem ho_init (A : Arcs) (t0 : Int) : ∀ t, t < t0 → hoQ A t0 t = false := by
  have := A.H_nonneg
  intro t ht; simp [hoQ]; omega

/-- **The 7e condition is exact on constructed runs**: for every arc record, the
constructed handover run has an overlap iff `qr + w + g1r_q < g2f`. -/
theorem ho_overlap_iff (A : Arcs) (t0 : Int) :
    (∃ t, (hoG1 A t0 t && hoG2 A t0 t) = true) ↔ A.qr + A.w + A.g1r_q < A.g2f := by
  constructor
  · rintro ⟨t, ht⟩
    have := (overlap_r2_to_r1 A t0 _ _ _ _ _ (ho_cell A t0) (fun _ => rfl) (fun _ => rfl)
      (ho_init A t0) t).1 ht
    omega
  · intro h
    have := overlap_exists_r2_to_r1 A t0 _ _ _ _ _ (ho_cell A t0) (fun _ => rfl) (fun _ => rfl)
      (ho_init A t0) h
    exact ⟨t0 + (A.qr + A.w + A.g1r_q), by rw [this.1, this.2]; rfl⟩

/-- The asymmetry 1 ps past the boundary at SLOW_MAX with `w = 20`: `d6 = o5q + w + 1`. -/
def rfV : RF := ⟨171, 0, 0, by decide⟩
def rfS : RF := ⟨170, 0, 0, by decide⟩
def arcsV : Arcs := arcsC slowMax rfV 20 20 (by decide) (by decide)
def arcsS : Arcs := arcsC slowMax rfS 20 20 (by decide) (by decide)

/-- **handover_overlap: constructed violating run.** At SLOW_MAX (every arc from the
SLOW_MAX column), q routing `w = wfb = 20` ps, O6 rise/fall asymmetry `d6 = 171`
(= `o5q + w + 1`, 1 ps past the no-overlap boundary): the constructed `Cell` trace has both
grants high at `t0 + 294` and exactly 1 ps of overlap in every window covering the falling
grant (`overlap_C`). -/
theorem ho_counter_run (t0 : Int) :
    rfV.d6 = slowMax.o5q + 20 + 1 ∧
    Cell arcsV hoR1 (hoR2 t0) (hoQ arcsV t0) (hoG1 arcsV t0) (hoG2 arcsV t0) ∧
    hoG1 arcsV t0 (t0 + 294) = true ∧ hoG2 arcsV t0 (t0 + 294) = true ∧
    ∀ n : Nat, 295 ≤ n →
      (countTrue (fun t => hoG1 arcsV t0 t && hoG2 arcsV t0 t) t0 n : Int) = 1 := by
  refine ⟨by decide, ho_cell _ _, ?_, ?_, ?_⟩
  · have := overlap_exists_r2_to_r1 arcsV t0 _ _ _ _ _ (ho_cell arcsV t0) (fun _ => rfl)
      (fun _ => rfl) (ho_init arcsV t0) (by decide)
    exact this.1
  · have := overlap_exists_r2_to_r1 arcsV t0 _ _ _ _ _ (ho_cell arcsV t0) (fun _ => rfl)
      (fun _ => rfl) (ho_init arcsV t0) (by decide)
    exact this.2
  · intro n hn
    have := overlap_C slowMax rfV 20 20 (by decide) (by decide) t0 _ _ _ _ _ (ho_cell arcsV t0)
      (fun _ => rfl) (fun _ => rfl) (ho_init arcsV t0) n (by simp [slowMax, Corner.of, O6, rfV]; omega)
    rw [this]; decide

/-- **handover_overlap, boundary**: at `d6 = o5q + w = 170` the constructed run has no
overlap at any instant. -/
theorem ho_boundary_run (t0 : Int) :
    rfS.d6 = slowMax.o5q + 20 ∧
    Cell arcsS hoR1 (hoR2 t0) (hoQ arcsS t0) (hoG1 arcsS t0) (hoG2 arcsS t0) ∧
    ∀ t, (hoG1 arcsS t0 t && hoG2 arcsS t0 t) = false :=
  ⟨by decide, ho_cell _ _, no_overlap_r2_to_r1 arcsS t0 _ _ _ _ _ (ho_cell arcsS t0)
    (fun _ => rfl) (fun _ => rfl) (ho_init arcsS t0) (by decide)⟩

end Handover

end Formal.Cells.ArbCounterRuns
