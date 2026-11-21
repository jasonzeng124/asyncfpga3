import Formal.Cells.ArbCounterRuns
import Formal.Cells.ArbAMerge

/-!
# Probe Bcr (part 2): constructed violating runs for the early re-request races

Shard B, 2026-10-29. Core Lean. Note: `formal/notes/B-arb-counter-runs.md`.

`ArbAMerge`'s counter-lemmas `cex_Q`, `cex_R`, `cex_G` (fall view), `cex_R2`, `cex_G2`
quantify over runs at slack −1; only `cexG_run` (race G, rise view) had a run. Here each
gets a CONSTRUCTED from-reset run (every signal low before 0, q = 1), with every route,
arc, the server minimum and the z line nonzero (`AllPos`, `0 < dz`), on which:
* the gate relations `Run` hold for all `t ∈ ℤ` (real INITs, rise-fast OR channel, server
  relation; traces from the untrusted `/tmp/claude-0/probes/Bcr/sim.py`, CHECKED here);
* the window scenario `E1` / `E2` holds on `[12, 100)`, with H_M (`MB`), the z line
  (`ZLine`, `z = R0` delayed by `dz`) and the run-form tick rows `Rows1` / `Rows2`;
* every other hypothesis of `e_fields` / `f_fields` holds: the two other races (run form),
  H_HOLDQ, RT1 / RT1b, RT2a, the A0 fork, and the four-phase client at its minimum
  reaction (`u = T1 + 1`);
* the race in question misses by EXACTLY 1 ps in the run form AND in the arc form
  (`Arc1` / `Arc2` field), and the other arc fields hold;
* the existing counter-lemma is applied to the run, so C's field fails on it.

Base record: `ArbMultiToken.Dw` (every route and arc 1 ps, `smin = 3`) with two to five
fields raised to 2 or 3 ps (the searched minimum, `/tmp/claude-0/probes/Bcr/tgt.py`).

Race Q2: `cex_Q2` needs `qr = qf` (no pulse shrinking on q's loop), so q's runt circulates
in ustate's hold loop while both clients request; the run is ended past the horizon by a
four-phase continuation (`rereqQ2_counter_run`). **NOT covered:** the delays are a small-integer grid, not routed numbers; the fall
view of race G needs a q-pin rise/fall difference on ugrant O5 (`g1fq = 2 > g1rq = 1`,
H_RF_ASYM). Race R's run has the z-rise row tight (`G2 + 1 = RR + dz`), as `cex_R` requires.
-/

namespace Formal.Cells.ArbCounterRunsAM
open Formal.Cells Formal.Cells.ArbHeldTimed Formal.Cells.ArbHeldTimed2
open Formal.Cells.ArbMultiToken Formal.Cells.ArbAMerge
open Formal.Cells.ArbCounterRuns (AllPos)

/-- From reset: every signal low before 0, except q (high). -/
def FromReset (s : Sigs) (z : Int → Bool) : Prop :=
  ∀ t, t < 0 → s.r1 t = false ∧ s.r2 t = false ∧ s.q t = true ∧ s.R0 t = false ∧
    s.g1 t = false ∧ s.g2 t = false ∧ s.A0 t = false ∧ s.A1 t = false ∧ s.A2 t = false ∧
    z t = false

/-! ### Q -/

def DQ : Dl where
  wr1s := 1
  wr2s := 1
  wr1g := 1
  wr2g := 1
  wfb := 2
  wa0s := 1
  wq := 1
  wg1 := 1
  wa01 := 1
  wfa1 := 1
  wg2 := 1
  wa02 := 1
  wfa2 := 1
  qr := 1
  qf := 2
  Rr1 := 2
  Rf1 := 2
  Rr2 := 1
  Rf2 := 1
  Rrq := 1
  Rfq := 1
  g1r1 := 1
  g1f1 := 1
  g1r2 := 1
  g1f2 := 1
  g1rq := 1
  g1fq := 1
  g2r := 1
  g2f := 1
  c1r := 1
  c1f := 1
  c2r := 1
  c2f := 1
  smin := 3
  H_NONNEG := by decide
  H_RISE_LE_FALL := by decide
  H_LOOP_POS := by decide

def WQ : Sigs where
  r1 := fun t => (decide (0 ≤ t) && decide (t < 30)) || decide (39 ≤ t)
  r2 := fun t => decide (10 ≤ t)
  q := fun t => decide (t < 39) || (decide (41 ≤ t) && decide (t < 43)) || decide (44 ≤ t)
  R0 := fun t => (decide (3 ≤ t) && decide (t < 33)) || decide (42 ≤ t)
  g1 := fun t => (decide (2 ≤ t) && decide (t < 32)) || (decide (43 ≤ t) && decide (t < 45)) || decide (46 ≤ t)
  g2 := fun t => (decide (41 ≤ t) && decide (t < 43)) || (decide (45 ≤ t) && decide (t < 46))
  A0 := fun t => (decide (6 ≤ t) && decide (t < 36)) || decide (46 ≤ t)
  A1 := fun t => (decide (8 ≤ t) && decide (t < 38)) || decide (48 ≤ t)
  A2 := fun _ => false

theorem WQ_run : Run DQ WQ where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [WQ, DQ, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [WQ, DQ, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [WQ, DQ, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [WQ, DQ, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [WQ, DQ, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [WQ, DQ, CE_eq]; omega
  H_SRV := by
    intro t h
    have ht : t = 6 ∨ t = 36 ∨ t = 46 :=
      Classical.byContradiction fun hc => h (by rw [Bool.eq_iff_iff]; simp [WQ]; omega)
    refine ⟨t - 3, by simp [DQ], by rw [Bool.eq_iff_iff]; simp [WQ]; omega, ?_⟩
    intro v h1 h2
    rw [Bool.eq_iff_iff]; simp [WQ]; omega

def zQ : Int → Bool := fun t => WQ.R0 (t - 1)

/-! ### R -/

def DR : Dl where
  wr1s := 1
  wr2s := 1
  wr1g := 1
  wr2g := 1
  wfb := 1
  wa0s := 1
  wq := 1
  wg1 := 1
  wa01 := 1
  wfa1 := 1
  wg2 := 1
  wa02 := 1
  wfa2 := 1
  qr := 1
  qf := 2
  Rr1 := 1
  Rf1 := 1
  Rr2 := 1
  Rf2 := 1
  Rrq := 2
  Rfq := 2
  g1r1 := 1
  g1f1 := 1
  g1r2 := 1
  g1f2 := 1
  g1rq := 1
  g1fq := 1
  g2r := 2
  g2f := 2
  c1r := 1
  c1f := 1
  c2r := 1
  c2f := 1
  smin := 3
  H_NONNEG := by decide
  H_RISE_LE_FALL := by decide
  H_LOOP_POS := by decide

def WR : Sigs where
  r1 := fun t => (decide (0 ≤ t) && decide (t < 30)) || decide (38 ≤ t)
  r2 := fun t => decide (10 ≤ t)
  q := fun t => decide (t < 38)
  R0 := fun t => (decide (2 ≤ t) && decide (t < 32)) || decide (40 ≤ t)
  g1 := fun t => (decide (2 ≤ t) && decide (t < 32))
  g2 := fun t => decide (41 ≤ t)
  A0 := fun t => (decide (5 ≤ t) && decide (t < 35)) || decide (43 ≤ t)
  A1 := fun t => (decide (7 ≤ t) && decide (t < 37))
  A2 := fun t => decide (45 ≤ t)

theorem WR_run : Run DR WR where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [WR, DR, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [WR, DR, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [WR, DR, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [WR, DR, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [WR, DR, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [WR, DR, CE_eq]; omega
  H_SRV := by
    intro t h
    have ht : t = 5 ∨ t = 35 ∨ t = 43 :=
      Classical.byContradiction fun hc => h (by rw [Bool.eq_iff_iff]; simp [WR]; omega)
    refine ⟨t - 3, by simp [DR], by rw [Bool.eq_iff_iff]; simp [WR]; omega, ?_⟩
    intro v h1 h2
    rw [Bool.eq_iff_iff]; simp [WR]; omega

def zR : Int → Bool := fun t => WR.R0 (t - 1)

/-! ### Gf -/

def DGf : Dl where
  wr1s := 1
  wr2s := 1
  wr1g := 1
  wr2g := 1
  wfb := 1
  wa0s := 1
  wq := 2
  wg1 := 1
  wa01 := 1
  wfa1 := 1
  wg2 := 1
  wa02 := 1
  wfa2 := 1
  qr := 1
  qf := 1
  Rr1 := 1
  Rf1 := 1
  Rr2 := 1
  Rf2 := 1
  Rrq := 1
  Rfq := 1
  g1r1 := 1
  g1f1 := 1
  g1r2 := 1
  g1f2 := 1
  g1rq := 1
  g1fq := 2
  g2r := 1
  g2f := 1
  c1r := 1
  c1f := 1
  c2r := 1
  c2f := 1
  smin := 3
  H_NONNEG := by decide
  H_RISE_LE_FALL := by decide
  H_LOOP_POS := by decide

def WGf : Sigs where
  r1 := fun t => (decide (0 ≤ t) && decide (t < 30)) || decide (38 ≤ t)
  r2 := fun t => decide (10 ≤ t)
  q := fun t => decide (t < 37)
  R0 := fun t => (decide (2 ≤ t) && decide (t < 32)) || decide (39 ≤ t)
  g1 := fun t => (decide (2 ≤ t) && decide (t < 32)) || (decide (40 ≤ t) && decide (t < 41))
  g2 := fun t => decide (40 ≤ t)
  A0 := fun t => (decide (5 ≤ t) && decide (t < 35)) || decide (42 ≤ t)
  A1 := fun t => (decide (7 ≤ t) && decide (t < 37))
  A2 := fun t => decide (44 ≤ t)

theorem WGf_run : Run DGf WGf where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [WGf, DGf, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [WGf, DGf, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [WGf, DGf, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [WGf, DGf, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [WGf, DGf, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [WGf, DGf, CE_eq]; omega
  H_SRV := by
    intro t h
    have ht : t = 5 ∨ t = 35 ∨ t = 42 :=
      Classical.byContradiction fun hc => h (by rw [Bool.eq_iff_iff]; simp [WGf]; omega)
    refine ⟨t - 3, by simp [DGf], by rw [Bool.eq_iff_iff]; simp [WGf]; omega, ?_⟩
    intro v h1 h2
    rw [Bool.eq_iff_iff]; simp [WGf]; omega

def zGf : Int → Bool := fun t => WGf.R0 (t - 2)

/-! ### R2 -/

def DR2 : Dl where
  wr1s := 1
  wr2s := 1
  wr1g := 1
  wr2g := 1
  wfb := 1
  wa0s := 1
  wq := 2
  wg1 := 1
  wa01 := 1
  wfa1 := 1
  wg2 := 1
  wa02 := 1
  wfa2 := 1
  qr := 1
  qf := 1
  Rr1 := 1
  Rf1 := 1
  Rr2 := 1
  Rf2 := 1
  Rrq := 3
  Rfq := 3
  g1r1 := 1
  g1f1 := 1
  g1r2 := 1
  g1f2 := 1
  g1rq := 2
  g1fq := 2
  g2r := 1
  g2f := 1
  c1r := 1
  c1f := 1
  c2r := 1
  c2f := 1
  smin := 3
  H_NONNEG := by decide
  H_RISE_LE_FALL := by decide
  H_LOOP_POS := by decide

def WR2 : Sigs where
  r1 := fun t => decide (10 ≤ t)
  r2 := fun t => (decide (0 ≤ t) && decide (t < 30)) || decide (38 ≤ t)
  q := fun t => decide (t < 2) || decide (37 ≤ t)
  R0 := fun t => (decide (6 ≤ t) && decide (t < 32)) || decide (40 ≤ t)
  g1 := fun t => decide (41 ≤ t)
  g2 := fun t => (decide (5 ≤ t) && decide (t < 32))
  A0 := fun t => (decide (9 ≤ t) && decide (t < 35)) || decide (43 ≤ t)
  A1 := fun t => decide (45 ≤ t)
  A2 := fun t => (decide (11 ≤ t) && decide (t < 37))

theorem WR2_run : Run DR2 WR2 where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [WR2, DR2, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [WR2, DR2, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [WR2, DR2, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [WR2, DR2, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [WR2, DR2, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [WR2, DR2, CE_eq]; omega
  H_SRV := by
    intro t h
    have ht : t = 9 ∨ t = 35 ∨ t = 43 :=
      Classical.byContradiction fun hc => h (by rw [Bool.eq_iff_iff]; simp [WR2]; omega)
    refine ⟨t - 3, by simp [DR2], by rw [Bool.eq_iff_iff]; simp [WR2]; omega, ?_⟩
    intro v h1 h2
    rw [Bool.eq_iff_iff]; simp [WR2]; omega

def zR2 : Int → Bool := fun t => WR2.R0 (t - 1)

/-! ### G2 -/

def DG2 : Dl where
  wr1s := 1
  wr2s := 1
  wr1g := 1
  wr2g := 1
  wfb := 1
  wa0s := 1
  wq := 3
  wg1 := 1
  wa01 := 1
  wfa1 := 1
  wg2 := 1
  wa02 := 1
  wfa2 := 1
  qr := 1
  qf := 1
  Rr1 := 1
  Rf1 := 1
  Rr2 := 1
  Rf2 := 1
  Rrq := 1
  Rfq := 1
  g1r1 := 1
  g1f1 := 1
  g1r2 := 1
  g1f2 := 1
  g1rq := 1
  g1fq := 1
  g2r := 1
  g2f := 1
  c1r := 1
  c1f := 1
  c2r := 1
  c2f := 1
  smin := 3
  H_NONNEG := by decide
  H_RISE_LE_FALL := by decide
  H_LOOP_POS := by decide

def WG2 : Sigs where
  r1 := fun t => decide (10 ≤ t)
  r2 := fun t => (decide (0 ≤ t) && decide (t < 30)) || decide (38 ≤ t)
  q := fun t => decide (t < 2) || decide (37 ≤ t)
  R0 := fun t => (decide (4 ≤ t) && decide (t < 32)) || decide (39 ≤ t)
  g1 := fun t => decide (41 ≤ t)
  g2 := fun t => (decide (6 ≤ t) && decide (t < 32)) || (decide (40 ≤ t) && decide (t < 41))
  A0 := fun t => (decide (7 ≤ t) && decide (t < 35)) || decide (42 ≤ t)
  A1 := fun t => decide (44 ≤ t)
  A2 := fun t => (decide (9 ≤ t) && decide (t < 37))

theorem WG2_run : Run DG2 WG2 where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [WG2, DG2, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [WG2, DG2, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [WG2, DG2, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [WG2, DG2, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [WG2, DG2, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [WG2, DG2, CE_eq]; omega
  H_SRV := by
    intro t h
    have ht : t = 7 ∨ t = 35 ∨ t = 42 :=
      Classical.byContradiction fun hc => h (by rw [Bool.eq_iff_iff]; simp [WG2]; omega)
    refine ⟨t - 3, by simp [DG2], by rw [Bool.eq_iff_iff]; simp [WG2]; omega, ?_⟩
    intro v h1 h2
    rw [Bool.eq_iff_iff]; simp [WG2]; omega

def zG2 : Int → Bool := fun t => WG2.R0 (t - 3)

/-! ### Q2 -/

def DQ2 : Dl where
  wr1s := 1
  wr2s := 1
  wr1g := 1
  wr2g := 1
  wfb := 4
  wa0s := 1
  wq := 1
  wg1 := 1
  wa01 := 1
  wfa1 := 1
  wg2 := 1
  wa02 := 1
  wfa2 := 1
  qr := 1
  qf := 1
  Rr1 := 1
  Rf1 := 1
  Rr2 := 2
  Rf2 := 2
  Rrq := 1
  Rfq := 1
  g1r1 := 1
  g1f1 := 1
  g1r2 := 1
  g1f2 := 1
  g1rq := 1
  g1fq := 1
  g2r := 1
  g2f := 1
  c1r := 1
  c1f := 1
  c2r := 1
  c2f := 2
  smin := 3
  H_NONNEG := by decide
  H_RISE_LE_FALL := by decide
  H_LOOP_POS := by decide

def WQ2 : Sigs where
  r1 := fun t => decide (10 ≤ t)
  r2 := fun t => (decide (0 ≤ t) && decide (t < 30)) || (decide (40 ≤ t) && decide (t < 52))
  q := fun t => decide (t < 2) || (decide (38 ≤ t) && decide (t < 42)) || (decide (43 ≤ t) && decide (t < 47)) || (decide (48 ≤ t) && decide (t < 52)) || (decide (53 ≤ t) && decide (t < 57)) || decide (58 ≤ t)
  R0 := fun t => (decide (7 ≤ t) && decide (t < 33)) || (decide (43 ≤ t) && decide (t < 57)) || (decide (58 ≤ t) && decide (t < 62)) || decide (63 ≤ t)
  g1 := fun t => (decide (40 ≤ t) && decide (t < 44)) || (decide (45 ≤ t) && decide (t < 49)) || (decide (50 ≤ t) && decide (t < 54)) || (decide (55 ≤ t) && decide (t < 59)) || decide (60 ≤ t)
  g2 := fun t => (decide (4 ≤ t) && decide (t < 32)) || (decide (44 ≤ t) && decide (t < 45)) || (decide (49 ≤ t) && decide (t < 50))
  A0 := fun t => (decide (10 ≤ t) && decide (t < 36)) || (decide (46 ≤ t) && decide (t < 60)) || decide (66 ≤ t)
  A1 := fun t => decide (48 ≤ t)
  A2 := fun t => (decide (12 ≤ t) && decide (t < 39)) || (decide (51 ≤ t) && decide (t < 63))

theorem WQ2_run : Run DQ2 WQ2 where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [WQ2, DQ2, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [WQ2, DQ2, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [WQ2, DQ2, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [WQ2, DQ2, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [WQ2, DQ2, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [WQ2, DQ2, CE_eq]; omega
  H_SRV := by
    intro t h
    have ht : t = 10 ∨ t = 36 ∨ t = 46 ∨ t = 60 ∨ t = 66 :=
      Classical.byContradiction fun hc => h (by rw [Bool.eq_iff_iff]; simp [WQ2]; omega)
    refine ⟨t - 3, by simp [DQ2], by rw [Bool.eq_iff_iff]; simp [WQ2]; omega, ?_⟩
    intro v h1 h2
    rw [Bool.eq_iff_iff]; simp [WQ2]; omega

def zQ2 : Int → Bool := fun t => WQ2.R0 (t - 1)

theorem WQ_E : E1 DQ 4 WQ 6 12 30 36 46 39 100 where
  ord := by omega
  r1 := by intro t h1 h2; rw [Bool.eq_iff_iff]; simp [WQ] <;> omega
  r2 := by intro t h1 h2; simp [WQ] <;> omega
  A0 := by intro t h1 h2; rw [Bool.eq_iff_iff]; simp [WQ] <;> omega
  A0p := by decide
  R0a := by intro t h1 h2; simp [WQ] <;> omega
  q0 := by intro t h1 h2; simp [WQ] <;> omega
  A10 := by intro t h1 h2; simp [WQ] <;> omega
  A20 := by intro t h1 h2; simp [WQ] <;> omega
  g10 := by intro t h1 h2; simp [WQ] <;> omega
  g20 := by intro t h1 h2; simp [WQ] <;> omega

theorem DQ_MB : MB DQ 4 := by
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [DQ]

theorem zQ_line : ZLine WQ zQ 1 := fun _ => rfl

theorem DQ_rows : Rows1 DQ 1 30 36 46 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [G1, G2, QB, TR, RR, T1, T2r, DQ] <;> omega

theorem WR_E : E1 DR 3 WR 5 12 30 35 43 38 100 where
  ord := by omega
  r1 := by intro t h1 h2; rw [Bool.eq_iff_iff]; simp [WR] <;> omega
  r2 := by intro t h1 h2; simp [WR] <;> omega
  A0 := by intro t h1 h2; rw [Bool.eq_iff_iff]; simp [WR] <;> omega
  A0p := by decide
  R0a := by intro t h1 h2; simp [WR] <;> omega
  q0 := by intro t h1 h2; simp [WR] <;> omega
  A10 := by intro t h1 h2; simp [WR] <;> omega
  A20 := by intro t h1 h2; simp [WR] <;> omega
  g10 := by intro t h1 h2; simp [WR] <;> omega
  g20 := by intro t h1 h2; simp [WR] <;> omega

theorem DR_MB : MB DR 3 := by
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [DR]

theorem zR_line : ZLine WR zR 1 := fun _ => rfl

theorem DR_rows : Rows1 DR 1 30 35 43 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [G1, G2, QB, TR, RR, T1, T2r, DR] <;> omega

theorem WGf_E : E1 DGf 4 WGf 5 12 30 35 42 38 100 where
  ord := by omega
  r1 := by intro t h1 h2; rw [Bool.eq_iff_iff]; simp [WGf] <;> omega
  r2 := by intro t h1 h2; simp [WGf] <;> omega
  A0 := by intro t h1 h2; rw [Bool.eq_iff_iff]; simp [WGf] <;> omega
  A0p := by decide
  R0a := by intro t h1 h2; simp [WGf] <;> omega
  q0 := by intro t h1 h2; simp [WGf] <;> omega
  A10 := by intro t h1 h2; simp [WGf] <;> omega
  A20 := by intro t h1 h2; simp [WGf] <;> omega
  g10 := by intro t h1 h2; simp [WGf] <;> omega
  g20 := by intro t h1 h2; simp [WGf] <;> omega

theorem DGf_MB : MB DGf 4 := by
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [DGf]

theorem zGf_line : ZLine WGf zGf 2 := fun _ => rfl

theorem DGf_rows : Rows1 DGf 2 30 35 42 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [G1, G2, QB, TR, RR, T1, T2r, DGf] <;> omega

theorem WR2_E : E2 DR2 4 WR2 9 12 30 35 43 38 100 where
  ord := by omega
  r1 := by intro t h1 h2; simp [WR2] <;> omega
  r2 := by intro t h1 h2; rw [Bool.eq_iff_iff]; simp [WR2] <;> omega
  A0 := by intro t h1 h2; rw [Bool.eq_iff_iff]; simp [WR2] <;> omega
  A0p := by decide
  R0a := by intro t h1 h2; simp [WR2] <;> omega
  q0 := by intro t h1 h2; simp [WR2] <;> omega
  A10 := by intro t h1 h2; simp [WR2] <;> omega
  A20 := by intro t h1 h2; simp [WR2] <;> omega
  g10 := by intro t h1 h2; simp [WR2] <;> omega
  g20 := by intro t h1 h2; simp [WR2] <;> omega

theorem DR2_MB : MB DR2 4 := by
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [DR2]

theorem zR2_line : ZLine WR2 zR2 1 := fun _ => rfl

theorem DR2_rows : Rows2 DR2 1 30 35 43 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [G1b, G2b, QBb, TRb, RRb, T1b, T2rb, DR2] <;> omega

theorem WG2_E : E2 DG2 4 WG2 7 12 30 35 42 38 100 where
  ord := by omega
  r1 := by intro t h1 h2; simp [WG2] <;> omega
  r2 := by intro t h1 h2; rw [Bool.eq_iff_iff]; simp [WG2] <;> omega
  A0 := by intro t h1 h2; rw [Bool.eq_iff_iff]; simp [WG2] <;> omega
  A0p := by decide
  R0a := by intro t h1 h2; simp [WG2] <;> omega
  q0 := by intro t h1 h2; simp [WG2] <;> omega
  A10 := by intro t h1 h2; simp [WG2] <;> omega
  A20 := by intro t h1 h2; simp [WG2] <;> omega
  g10 := by intro t h1 h2; simp [WG2] <;> omega
  g20 := by intro t h1 h2; simp [WG2] <;> omega

theorem DG2_MB : MB DG2 4 := by
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [DG2]

theorem zG2_line : ZLine WG2 zG2 3 := fun _ => rfl

theorem DG2_rows : Rows2 DG2 3 30 35 42 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [G1b, G2b, QBb, TRb, RRb, T1b, T2rb, DG2] <;> omega

theorem WQ2_E : E2 DQ2 5 WQ2 10 12 30 36 46 40 52 where
  ord := by omega
  r1 := by intro t h1 h2; simp [WQ2] <;> omega
  r2 := by intro t h1 h2; rw [Bool.eq_iff_iff]; simp [WQ2] <;> omega
  A0 := by intro t h1 h2; rw [Bool.eq_iff_iff]; simp [WQ2] <;> omega
  A0p := by decide
  R0a := by intro t h1 h2; simp [WQ2] <;> omega
  q0 := by intro t h1 h2; simp [WQ2] <;> omega
  A10 := by intro t h1 h2; simp [WQ2] <;> omega
  A20 := by intro t h1 h2; simp [WQ2] <;> omega
  g10 := by intro t h1 h2; simp [WQ2] <;> omega
  g20 := by intro t h1 h2; simp [WQ2] <;> omega

theorem DQ2_MB : MB DQ2 5 := by
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [DQ2]

theorem zQ2_line : ZLine WQ2 zQ2 1 := fun _ => rfl

theorem DQ2_rows : Rows2 DQ2 1 30 36 46 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [G1b, G2b, QBb, TRb, RRb, T1b, T2rb, DQ2] <;> omega

/-! ## Headline theorems -/

/-- **Race Q (rereq_Q), constructed counter-run.** Client 1 releases at 30 and re-requests at
39 = T1 + 1; race Q misses by exactly 1 ps (run form and `Arc1.q`); races R and G, H_HOLDQ,
RT1, RT2a, the A0 fork, H_M, the z line and `Rows1` hold. `cex_Q`: g2 falls while r2 is
high (C's H_ARB2 fails). -/
theorem rereqQ_counter_run :
    Run DQ WQ ∧ MB DQ 4 ∧ E1 DQ 4 WQ 6 12 30 36 46 39 100 ∧ ZLine WQ zQ 1 ∧
    Rows1 DQ 1 30 36 46 ∧ FromReset WQ zQ ∧ AllPos DQ ∧
    RRc DQ 36 39 ∧ RG DQ 36 39 ∧ HQ DQ 36 46 ∧ RT1 DQ ∧ T1 DQ 30 36 + 1 = 39 ∧
    T1 DQ 30 36 + DQ.wfa1 ≤ 46 + DQ.wa01 ∧ 36 + DQ.wa02 ≤ G2 DQ 36 + DQ.wg2 ∧
    39 + DQ.wr1s + 1 = QB DQ 36 + DQ.wfb ∧
    DQ.wa0s + DQ.qf + DQ.wfb = DQ.wa01 + DQ.c1f + 1 + DQ.wr1s + 1 ∧
    DQ.wa0s + DQ.qf + DQ.wfb + DQ.Rrq ≤ DQ.wa01 + DQ.c1f + 1 + DQ.wr1s + DQ.Rr1 ∧
    DQ.wa0s + DQ.qf + DQ.wq + DQ.g1rq ≤ DQ.wa01 + DQ.c1f + 1 + DQ.wr1g + DQ.g1r1 ∧
    DQ.wa0s + DQ.qf + DQ.wq + DQ.g1fq ≤ DQ.wa01 + DQ.c1f + 1 + DQ.wr1g + DQ.g1f1 ∧
    (∃ t, 12 ≤ t ∧ t < 100 ∧ WQ.g2 t = true ∧ WQ.g2 (t + 1) = false ∧ WQ.r2 t = true) :=
  ⟨WQ_run, DQ_MB, WQ_E, zQ_line, DQ_rows, by intro t ht; simp [WQ, zQ]; omega,
    by unfold AllPos; decide,
    by simp [RRc, RR, QB, DQ] <;> omega, by simp [RG, QB, DQ] <;> omega, by simp [HQ, QB, DQ] <;> omega, by simp [RT1, DQ] <;> omega,
    by simp [T1, G1, QB, DQ] <;> omega, by simp [T1, G1, QB, DQ] <;> omega, by simp [G2, QB, DQ] <;> omega,
    by simp [QB, DQ] <;> omega, by simp [DQ] <;> omega, by simp [DQ] <;> omega, by simp [DQ] <;> omega, by simp [DQ] <;> omega,
    cex_Q WQ_run DQ_MB WQ_E (by simp [HQ, QB, DQ] <;> omega) (by simp [QB, DQ] <;> omega) (by simp [DQ] <;> omega)
      (by simp [DQ] <;> omega) (by simp [QB, DQ] <;> omega)⟩

/-- **Race R (rereq_R), constructed counter-run.** Re-request at 38 = T1 + 1; race R misses by
exactly 1 ps (run form and `Arc1.r`), with the z-rise row tight (`G2 + 1 = RR + dz`, as
`cex_R` requires); races Q and G, RT1, RT2a, the A0 fork, H_M and `Rows1` hold (H_HOLDQ
holds too). `cex_R`: z rises while neither grant is high (C's `zr` fails). -/
theorem rereqR_counter_run :
    Run DR WR ∧ MB DR 3 ∧ E1 DR 3 WR 5 12 30 35 43 38 100 ∧ ZLine WR zR 1 ∧
    Rows1 DR 1 30 35 43 ∧ FromReset WR zR ∧ AllPos DR ∧
    RQ DR 35 38 ∧ RG DR 35 38 ∧ HQ DR 35 43 ∧ RT1 DR ∧ T1 DR 30 35 + 1 = 38 ∧
    T1 DR 30 35 + DR.wfa1 ≤ 43 + DR.wa01 ∧ 35 + DR.wa02 ≤ G2 DR 35 + DR.wg2 ∧
    38 + DR.wr1s + DR.Rr1 + 1 = RR DR 35 ∧
    DR.wa0s + DR.qf + DR.wfb + DR.Rrq = DR.wa01 + DR.c1f + 1 + DR.wr1s + DR.Rr1 + 1 ∧
    DR.wa0s + DR.qf + DR.wfb ≤ DR.wa01 + DR.c1f + 1 + DR.wr1s ∧
    DR.wa0s + DR.qf + DR.wq + DR.g1rq ≤ DR.wa01 + DR.c1f + 1 + DR.wr1g + DR.g1r1 ∧
    DR.wa0s + DR.qf + DR.wq + DR.g1fq ≤ DR.wa01 + DR.c1f + 1 + DR.wr1g + DR.g1f1 ∧
    G2 DR 35 + 1 = RR DR 35 + 1 ∧
    (∃ t, 12 + 3 ≤ t ∧ t < 100 ∧ zR t = false ∧ zR (t + 1) = true ∧ (WR.g1 t || WR.g2 t) = false) :=
  ⟨WR_run, DR_MB, WR_E, zR_line, DR_rows, by intro t ht; simp [WR, zR]; omega,
    by unfold AllPos; decide,
    by simp [RQ, QB, DR] <;> omega, by simp [RG, QB, DR] <;> omega, by simp [HQ, QB, DR] <;> omega, by simp [RT1, DR] <;> omega,
    by simp [T1, G1, QB, DR] <;> omega, by simp [T1, G1, QB, DR] <;> omega, by simp [G2, QB, DR] <;> omega,
    by simp [RR, QB, DR] <;> omega, by simp [DR] <;> omega, by simp [DR] <;> omega, by simp [DR] <;> omega, by simp [DR] <;> omega,
    by simp [G2, RR, QB, DR] <;> omega,
    cex_R WR_run DR_MB WR_E (by simp [RQ, QB, DR] <;> omega) (by simp [HQ, QB, DR] <;> omega) (by simp [RG, QB, DR] <;> omega)
      (by simp [RR, QB, DR] <;> omega) (by simp [DR] <;> omega) zR_line (by decide) (by simp [G2, RR, QB, DR] <;> omega)
      (by simp [G1, RR, QB, DR] <;> omega) (by simp [RR, QB, DR] <;> omega)⟩

/-- **Race G, fall view (rereq_G), constructed counter-run.** Re-request at 38 = T1 + 1; G's
fall view misses by exactly 1 ps (run form and `Arc1.gf`) while its rise view holds (slack 0,
and `Arc1.gr`); races Q and R, H_HOLDQ, RT1, RT2a, the A0 fork, H_M and `Rows1` hold.
`cex_G` (fall view): g1 falls while r1 is high (C's H_ARB1 fails). -/
theorem rereqGf_counter_run :
    Run DGf WGf ∧ MB DGf 4 ∧ E1 DGf 4 WGf 5 12 30 35 42 38 100 ∧ ZLine WGf zGf 2 ∧
    Rows1 DGf 2 30 35 42 ∧ FromReset WGf zGf ∧ AllPos DGf ∧
    RQ DGf 35 38 ∧ RRc DGf 35 38 ∧ HQ DGf 35 42 ∧ RT1 DGf ∧ T1 DGf 30 35 + 1 = 38 ∧
    T1 DGf 30 35 + DGf.wfa1 ≤ 42 + DGf.wa01 ∧ 35 + DGf.wa02 ≤ G2 DGf 35 + DGf.wg2 ∧
    QB DGf 35 + DGf.wq + DGf.g1rq ≤ 38 + DGf.wr1g + DGf.g1r1 ∧
    38 + DGf.wr1g + DGf.g1f1 + 1 = QB DGf 35 + DGf.wq + DGf.g1fq ∧
    DGf.wa0s + DGf.qf + DGf.wq + DGf.g1fq = DGf.wa01 + DGf.c1f + 1 + DGf.wr1g + DGf.g1f1 + 1 ∧
    DGf.wa0s + DGf.qf + DGf.wq + DGf.g1rq ≤ DGf.wa01 + DGf.c1f + 1 + DGf.wr1g + DGf.g1r1 ∧
    DGf.wa0s + DGf.qf + DGf.wfb ≤ DGf.wa01 + DGf.c1f + 1 + DGf.wr1s ∧
    DGf.wa0s + DGf.qf + DGf.wfb + DGf.Rrq ≤ DGf.wa01 + DGf.c1f + 1 + DGf.wr1s + DGf.Rr1 ∧
    (∃ t, 12 ≤ t ∧ t < 100 ∧ WGf.g1 t = true ∧ WGf.g1 (t + 1) = false ∧ WGf.r1 t = true) :=
  ⟨WGf_run, DGf_MB, WGf_E, zGf_line, DGf_rows, by intro t ht; simp [WGf, zGf]; omega,
    by unfold AllPos; decide,
    by simp [RQ, QB, DGf] <;> omega, by simp [RRc, RR, QB, DGf] <;> omega, by simp [HQ, QB, DGf] <;> omega, by simp [RT1, DGf] <;> omega,
    by simp [T1, G1, QB, DGf] <;> omega, by simp [T1, G1, QB, DGf] <;> omega, by simp [G2, QB, DGf] <;> omega,
    by simp [QB, DGf] <;> omega, by simp [QB, DGf] <;> omega, by simp [DGf] <;> omega, by simp [DGf] <;> omega, by simp [DGf] <;> omega,
    by simp [DGf] <;> omega,
    cex_G WGf_run DGf_MB WGf_E (by simp [RQ, QB, DGf] <;> omega) (by simp [HQ, QB, DGf] <;> omega) DGf.g1f1 DGf.g1fq
      (Or.inr ⟨rfl, rfl⟩) (by simp [QB, DGf] <;> omega) (by simp [QB, DGf] <;> omega)⟩

/-- **Race R2 (rereq_R2), constructed counter-run.** Client 2 holds first (r2 at 0, r1 waits
from 10), releases at 30, re-requests at 38 = T1b + 1; race R2 misses by exactly 1 ps (run
form and `Arc2.r`), z-rise row tight (`G1b + 1 = RRb + dz`); races Q2 and G2, H_HOLDQ2,
RT1b, RT2a, the A0 fork, H_M and `Rows2` hold. `cex_R2`: z rises while neither grant is
high (C's `zr` fails). -/
theorem rereqR2_counter_run :
    Run DR2 WR2 ∧ MB DR2 4 ∧ E2 DR2 4 WR2 9 12 30 35 43 38 100 ∧ ZLine WR2 zR2 1 ∧
    Rows2 DR2 1 30 35 43 ∧ FromReset WR2 zR2 ∧ AllPos DR2 ∧
    RQ2 DR2 35 38 ∧ RG2 DR2 35 38 ∧ HQ2 DR2 35 43 ∧ RT1b DR2 ∧ T1b DR2 30 35 + 1 = 38 ∧
    T1b DR2 30 35 + DR2.wfa2 ≤ 43 + DR2.wa02 ∧ 35 + DR2.wa01 ≤ G1b DR2 35 + DR2.wg1 ∧
    38 + DR2.wr2s + DR2.Rr2 + 1 = RRb DR2 35 ∧
    DR2.wa0s + DR2.qr + DR2.wfb + DR2.Rrq = DR2.wa02 + DR2.c2f + 1 + DR2.wr2s + DR2.Rr2 + 1 ∧
    DR2.wa0s + DR2.qr + DR2.wfb ≤ DR2.wa02 + DR2.c2f + 1 + DR2.wr2s ∧
    DR2.wa0s + DR2.qr + DR2.wq ≤ DR2.wa02 + DR2.c2f + 1 + DR2.wr2g ∧
    G1b DR2 35 + 1 = RRb DR2 35 + 1 ∧
    (∃ t, 12 + 4 ≤ t ∧ t < 100 ∧ zR2 t = false ∧ zR2 (t + 1) = true ∧
      (WR2.g1 t || WR2.g2 t) = false) :=
  ⟨WR2_run, DR2_MB, WR2_E, zR2_line, DR2_rows, by intro t ht; simp [WR2, zR2]; omega,
    by unfold AllPos; decide,
    by simp [RQ2, QBb, DR2] <;> omega, by simp [RG2, QBb, DR2] <;> omega, by simp [HQ2, QBb, DR2] <;> omega,
    by simp [RT1b, DR2] <;> omega, by simp [T1b, G2b, QBb, DR2] <;> omega, by simp [T1b, G2b, QBb, DR2] <;> omega,
    by simp [G1b, QBb, DR2] <;> omega, by simp [RRb, QBb, DR2] <;> omega, by simp [DR2] <;> omega, by simp [DR2] <;> omega,
    by simp [DR2] <;> omega, by simp [G1b, RRb, QBb, DR2] <;> omega,
    cex_R2 WR2_run DR2_MB WR2_E (by simp [RQ2, QBb, DR2] <;> omega) (by simp [HQ2, QBb, DR2] <;> omega)
      (by simp [RG2, QBb, DR2] <;> omega) (by simp [RRb, QBb, DR2] <;> omega) (by simp [DR2] <;> omega) zR2_line (by decide)
      (by simp [G1b, RRb, QBb, DR2] <;> omega) (by simp [G2b, RRb, QBb, DR2] <;> omega) (by simp [RRb, QBb, DR2] <;> omega)⟩

/-- **Race G2 (rereq_G2), constructed counter-run.** Client 2 holds first, releases at 30,
re-requests at 38 = T1b + 1; race G2 misses by exactly 1 ps (run form and `Arc2.g`); races
Q2 and R2, H_HOLDQ2, RT1b, RT2a, the A0 fork, H_M and `Rows2` hold. `cex_G2`: g2 falls while
r2 is high (C's H_ARB2 fails). -/
theorem rereqG2_counter_run :
    Run DG2 WG2 ∧ MB DG2 4 ∧ E2 DG2 4 WG2 7 12 30 35 42 38 100 ∧ ZLine WG2 zG2 3 ∧
    Rows2 DG2 3 30 35 42 ∧ FromReset WG2 zG2 ∧ AllPos DG2 ∧
    RQ2 DG2 35 38 ∧ RRc2 DG2 35 38 ∧ HQ2 DG2 35 42 ∧ RT1b DG2 ∧ T1b DG2 30 35 + 1 = 38 ∧
    T1b DG2 30 35 + DG2.wfa2 ≤ 42 + DG2.wa02 ∧ 35 + DG2.wa01 ≤ G1b DG2 35 + DG2.wg1 ∧
    38 + DG2.wr2g + 1 = QBb DG2 35 + DG2.wq ∧
    DG2.wa0s + DG2.qr + DG2.wq = DG2.wa02 + DG2.c2f + 1 + DG2.wr2g + 1 ∧
    DG2.wa0s + DG2.qr + DG2.wfb ≤ DG2.wa02 + DG2.c2f + 1 + DG2.wr2s ∧
    DG2.wa0s + DG2.qr + DG2.wfb + DG2.Rrq ≤ DG2.wa02 + DG2.c2f + 1 + DG2.wr2s + DG2.Rr2 ∧
    (∃ t, 12 ≤ t ∧ t < 100 ∧ WG2.g2 t = true ∧ WG2.g2 (t + 1) = false ∧ WG2.r2 t = true) :=
  ⟨WG2_run, DG2_MB, WG2_E, zG2_line, DG2_rows, by intro t ht; simp [WG2, zG2]; omega,
    by unfold AllPos; decide,
    by simp [RQ2, QBb, DG2] <;> omega, by simp [RRc2, RRb, QBb, DG2] <;> omega, by simp [HQ2, QBb, DG2] <;> omega,
    by simp [RT1b, DG2] <;> omega, by simp [T1b, G2b, QBb, DG2] <;> omega, by simp [T1b, G2b, QBb, DG2] <;> omega,
    by simp [G1b, QBb, DG2] <;> omega, by simp [QBb, DG2] <;> omega, by simp [DG2] <;> omega, by simp [DG2] <;> omega, by simp [DG2] <;> omega,
    cex_G2 WG2_run DG2_MB WG2_E (by simp [RQ2, QBb, DG2] <;> omega) (by simp [HQ2, QBb, DG2] <;> omega)
      (by simp [QBb, DG2] <;> omega) (by simp [QBb, DG2] <;> omega)⟩

/-- **Race Q2 (rereq_Q2), constructed counter-run.** Client 2 holds first (r2 at 0, r1 waits
from 10), releases at 30, re-requests at 40 = T1b + 1; race Q2 misses by exactly 1 ps (run
form and `Arc2.q`); races R2 and G2, H_HOLDQ2, RT1b, RT2a, the A0 fork, H_M and `Rows2` hold,
and `cex_Q2`'s side conditions (`qr = qf`, `g1rq = g1fq`, `qr + wfb ≥ 2`). The 4 ps high runt
on q then circulates in ustate's hold loop (q is 1 for 4 ps, 0 for 1 ps, period 5 = wfb + qr),
so g1 pulses with r1 high: `cex_Q2` gives C's H_ARB1 failure. Past the horizon 52 the run is
continued four-phase so that it ends: A2 latches on a g2 pulse once A0 is high (51), client 2
then drops r2 (52), the server drops A0 on a low sample of R0 (60), q is forced to 1 and the
run settles (client 1 holds). On `[51, 63)` both acks are high. -/
theorem rereqQ2_counter_run :
    Run DQ2 WQ2 ∧ MB DQ2 5 ∧ E2 DQ2 5 WQ2 10 12 30 36 46 40 52 ∧ ZLine WQ2 zQ2 1 ∧
    Rows2 DQ2 1 30 36 46 ∧ FromReset WQ2 zQ2 ∧ AllPos DQ2 ∧
    RRc2 DQ2 36 40 ∧ RG2 DQ2 36 40 ∧ HQ2 DQ2 36 46 ∧ RT1b DQ2 ∧ T1b DQ2 30 36 + 1 = 40 ∧
    T1b DQ2 30 36 + DQ2.wfa2 ≤ 46 + DQ2.wa02 ∧ 36 + DQ2.wa01 ≤ G1b DQ2 36 + DQ2.wg1 ∧
    40 + DQ2.wr2s + 1 = QBb DQ2 36 + DQ2.wfb ∧
    DQ2.wa0s + DQ2.qr + DQ2.wfb = DQ2.wa02 + DQ2.c2f + 1 + DQ2.wr2s + 1 ∧
    DQ2.wa0s + DQ2.qr + DQ2.wfb + DQ2.Rrq ≤ DQ2.wa02 + DQ2.c2f + 1 + DQ2.wr2s + DQ2.Rr2 ∧
    DQ2.wa0s + DQ2.qr + DQ2.wq ≤ DQ2.wa02 + DQ2.c2f + 1 + DQ2.wr2g ∧
    DQ2.qr = DQ2.qf ∧ DQ2.g1rq = DQ2.g1fq ∧
    (∃ t, 12 ≤ t ∧ t < 52 ∧ WQ2.g1 t = true ∧ WQ2.g1 (t + 1) = false ∧ WQ2.r1 t = true) ∧
    (∀ t, 51 ≤ t → t < 63 → WQ2.A1 t = true ∧ WQ2.A2 t = true) :=
  ⟨WQ2_run, DQ2_MB, WQ2_E, zQ2_line, DQ2_rows, by intro t ht; simp [WQ2, zQ2]; omega,
    by unfold AllPos; decide,
    by simp [RRc2, RRb, QBb, DQ2] <;> omega, by simp [RG2, QBb, DQ2] <;> omega,
    by simp [HQ2, QBb, DQ2] <;> omega, by simp [RT1b, DQ2] <;> omega,
    by simp [T1b, G2b, QBb, DQ2] <;> omega, by simp [T1b, G2b, QBb, DQ2] <;> omega,
    by simp [G1b, QBb, DQ2] <;> omega, by simp [QBb, DQ2] <;> omega, by simp [DQ2],
    by simp [DQ2], by simp [DQ2], by simp [DQ2], by simp [DQ2],
    cex_Q2 WQ2_run DQ2_MB WQ2_E (by simp [HQ2, QBb, DQ2] <;> omega) (by simp [QBb, DQ2] <;> omega)
      (by simp [DQ2]) (by simp [DQ2]) (by simp [DQ2]) (by simp [QBb, DQ2] <;> omega),
    by intro t h1 h2; simp [WQ2]; omega⟩

end Formal.Cells.ArbCounterRunsAM
