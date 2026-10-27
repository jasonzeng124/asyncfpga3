import Formal.Cells.ArbHeldTimed

/-!
# Probe 7j: the held `bd_arbiter`, client-2-release direction, non-vacuity, runt band

Follow-up of 7h (`ArbHeldTimed.lean`, notes `B-arb-held-timed.md`), which it
imports read-only and reuses: the gate relations `Run` (real INITs through
`lutB`/`o5B`/`o6B`, rise-fast pure-delay OR channel per LUT output, a routed
delay per pin), the delays `Dl` with H_NONNEG / H_RISE_LE_FALL / H_LOOP_POS,
the server relation `Server` (H_SERVER_MIN) and the 7h scenario `Scn`.

## Contents

1. **Mirror direction** (client 2 holds, drops r2; q RISES at the release):
   scenario `Scn2`; exact traces `q_eq2`, `R0_hi2`/`R0_lo2`, `g1_eq2`,
   `g2_eq2`; server bounds `TA_ge2`, `TA2_ge2`; RT1 `overlap_exact2`,
   `rt1_exclusion2`, `rt1_counter2`, `rt1_counter2_minserver`; RT2
   `A2_low_after2`, `A1_low_before2`, `rt2_exclusion2`, `rt2_exclusion2_arcs`,
   `A2_stuck2`, `rt2_counter2`; prjxray form `prj_RT1b`, `prj_RT2b`,
   `prj_arc_only2` (margins: RT1 248, pulse 96, g2 236, forkA 152, forkG 292,
   fork 108 ps at zero routing with a 112 ps server).
2. **Non-vacuity**: one concrete delay set `D0` (prjxray arcs, zero routes,
   smin = 112) satisfying every arc condition of both directions, and two
   explicit trace sets `W1`, `W2` that satisfy `Run D0` (for ALL t ∈ ℤ, server
   relation included) and `Scn` / `Scn2` (for every horizon past the second
   server edge), with the server answering in exactly `smin` both times.
   `nonvacuous` packs it into one existential.
3. **Runt band** (`A1_runt_low`, `A1_runt_high`, `A1_runt_overlap`): what A1
   does when A0's low pulse at ua1 lies between `A1_stuck`'s condition and
   RT2a: an exact first excursion (low on `[T1, TA2+wa01+c1r)`, high again on
   `[TA2+wa01+c1r, T1+c1r+wfa1)`) and the resulting ack overlap.
-/

namespace Formal.Cells.ArbHeldTimed2
open Formal.Cells Formal.Cells.ArbHeldTimed

/-! ## Extra INIT lemmas (proved on the real INITs) -/

theorem FS_bool : ∀ r1 r2 q a0 : Bool,
    FS r1 r2 q a0 = ((a0 && q) || (!a0 && ((r1 && !r2) || (r1 && q) || (!r2 && q)))) := by
  decide
/-- Release with r1 high, r2 low: q sets. -/
theorem FS_set : ∀ q : Bool, FS true false q false = true := by decide
/-- R0 with r1 high: `q || r2`. -/
theorem FR_r1 : ∀ r2 q : Bool, FR true r2 q = (q || r2) := by decide
theorem FG1_r1 : ∀ r2 q : Bool, FG1 true r2 q = q := by decide

/-! ## Scenario 2: client 2 releases, client 1 waits -/

/-- The mirror handover: client 2 holds (q = 0, A0 = 1, A2 = 1, A1 = 0),
client 1 waits (r1 = 1), client 2 drops r2 at `t0`. Server edges `TA` (A0↓),
`TA2` (A0↑ for client 1) are free, constrained only by `Server`. -/
structure Scn2 (D : Dl) (s : Sigs) (t0 ta TA TA2 Hz : Int) : Prop where
  H_ORDER : ta ≤ t0 ∧ ta < TA ∧ t0 < TA ∧ TA < TA2 ∧ TA2 < Hz
  /-- client 1 waiting throughout. -/
  H_r1 : ∀ t, t < Hz → s.r1 t = true
  /-- client 2: high, drops at t0, stays low until the horizon. -/
  H_r2 : ∀ t, t < Hz → s.r2 t = decide (t < t0)
  H_A0 : ∀ t, ta ≤ t → t < Hz → s.A0 t = (decide (t < TA) || decide (TA2 ≤ t))
  H_A0_prev : s.A0 (ta - 1) = false
  /-- settled initial state: q = 0, A2 = 1, A1 = 0 before t0. -/
  H_q_init : ∀ t, t < t0 → s.q t = false
  H_A1_init : ∀ t, t < t0 → s.A1 t = false
  H_A2_init : ∀ t, t < t0 → s.A2 t = true
  /-- H_SETTLED (mirror): A0's rise reached ustate's and ua2's views before
  client 2 dropped its request. -/
  H_SETTLED : ta + D.wa0s + D.qf ≤ t0 ∧ ta + D.wa02 + D.c2f ≤ t0

/-- R0's fall (through r2, pin I1). -/
def TRb (D : Dl) (t0 : Int) : Int := t0 + D.wr2s + D.Rf2
/-- q's RISE (client 2 → client 1): the O6 rise arc. -/
def QBb (D : Dl) (TA : Int) : Int := TA + D.wa0s + D.qr
/-- R0's re-rise (for client 1), through q (pin I2) rise arc. -/
def RRb (D : Dl) (TA : Int) : Int := QBb D TA + D.wfb + D.Rrq
/-- g1's rise (through q, pin I2 of ugrant O5). -/
def G1b (D : Dl) (TA : Int) : Int := QBb D TA + D.wq + D.g1rq
/-- g2's fall: through r2 or through q, whichever first, O6 fall arc. -/
def G2b (D : Dl) (t0 TA : Int) : Int := min (t0 + D.wr2g) (QBb D TA + D.wq) + D.g2f

section
variable {D : Dl} {s : Sigs} {t0 ta TA TA2 Hz : Int}

theorem A0_hi1b (S : Scn2 D s t0 ta TA TA2 Hz) (t : Int) (h1 : ta ≤ t) (h2 : t < TA) :
    s.A0 t = true := by
  have := S.H_ORDER
  rw [S.H_A0 t h1 (by omega)]; simp; omega

theorem A0_lob (S : Scn2 D s t0 ta TA TA2 Hz) (t : Int) (h1 : TA ≤ t) (h2 : t < TA2) :
    s.A0 t = false := by
  have := S.H_ORDER
  rw [S.H_A0 t (by omega) (by omega)]; simp; omega

theorem A0_hi2b (S : Scn2 D s t0 ta TA TA2 Hz) (t : Int) (h1 : TA2 ≤ t) (h2 : t < Hz) :
    s.A0 t = true := by
  have := S.H_ORDER
  rw [S.H_A0 t (by omega) h2]; simp; omega

theorem r2_lo (S : Scn2 D s t0 ta TA TA2 Hz) (t : Int) (h1 : t0 ≤ t) (h2 : t < Hz) :
    s.r2 t = false := by
  rw [S.H_r2 t h2]; simp; omega

theorem r2_hi (S : Scn2 D s t0 ta TA TA2 Hz) (t : Int) (h1 : t < t0) :
    s.r2 t = true := by
  have := S.H_ORDER
  rw [S.H_r2 t (by omega)]; simp; omega

/-- R0 stays high until `TRb` (with r1 high, R0 = q + r2; r2 suffices). -/
theorem R0_hi2 (R : Run D s) (S : Scn2 D s t0 ta TA TA2 Hz) (t : Int) (h : t < TRb D t0)
    (hz : t < Hz) : s.R0 t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL
  unfold TRb at h
  rw [R.H_R0 t, S.H_r1 (t - D.wr1s - D.Rf1) (by omega), r2_hi S (t - D.wr2s - D.Rf2) (by omega),
    FR_r1]
  simp

/-- **The server cannot drop A0 before `TRb + smin`.** -/
theorem TA_ge2 (R : Run D s) (S : Scn2 D s t0 ta TA TA2 Hz) : TRb D t0 + D.smin ≤ TA := by
  have ho := S.H_ORDER
  have := D.H_NONNEG
  have e1 : s.A0 TA = false := A0_lob S TA (by omega) (by omega)
  have e0 : s.A0 (TA - 1) = true := A0_hi1b S _ (by omega) (by omega)
  obtain ⟨u, hu, hR, hv⟩ := R.H_SRV TA (by rw [e1, e0]; simp)
  rw [e1] at hR
  have hu1 : ta ≤ u := by
    by_cases hc : ta ≤ u
    · exact hc
    · have := hv (ta - 1) (by omega) (by omega)
      rw [S.H_A0_prev, e0] at this; exact absurd this (by simp)
  by_cases hc : TRb D t0 + D.smin ≤ TA
  · exact hc
  · have := R0_hi2 R S u (by omega) (by omega)
    rw [hR] at this; exact absurd this (by simp)

/-- q is low until `QBb` (held at 0 by A0 while the server serves client 2). -/
theorem q_lo2 (R : Run D s) (S : Scn2 D s t0 ta TA TA2 Hz) :
    ∀ t, t < QBb D TA → s.q t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.H_SETTLED; have := S.H_ORDER
  refine int_ind (fun t => t < QBb D TA → s.q t = false) t0
    (fun t ht _ => S.H_q_init t ht) ?_
  intro t ht ih hb
  unfold QBb at hb
  rw [R.H_q t, A0_hi1b S (t - D.wa0s - D.qf) (by omega) (by omega),
    A0_hi1b S (t - D.wa0s - D.qr) (by omega) (by omega), FS_hold, FS_hold,
    ih (t - D.wfb - D.qf) (by omega) (by unfold QBb; omega),
    ih (t - D.wfb - D.qr) (by omega) (by unfold QBb; omega)]
  rfl

/-- R0 is low on `[TRb, RRb)`. -/
theorem R0_lo2 (R : Run D s) (S : Scn2 D s t0 ta TA TA2 Hz) (t : Int)
    (h1 : TRb D t0 ≤ t) (h2 : t < RRb D TA) (hz : t < Hz) : s.R0 t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL
  unfold TRb at h1; unfold RRb at h2
  rw [R.H_R0 t, S.H_r1 (t - D.wr1s - D.Rr1) (by omega), S.H_r1 (t - D.wr1s - D.Rf1) (by omega),
    r2_lo S (t - D.wr2s - D.Rr2) (by omega) (by omega),
    r2_lo S (t - D.wr2s - D.Rf2) (by omega) (by omega),
    q_lo2 R S _ (by omega), q_lo2 R S (t - D.wfb - D.Rfq) (by omega), FR_r1]
  rfl

/-- **The server cannot re-raise A0 before `RRb + smin`.** -/
theorem TA2_ge2 (R : Run D s) (S : Scn2 D s t0 ta TA TA2 Hz) : RRb D TA + D.smin ≤ TA2 := by
  have ho := S.H_ORDER
  have := D.H_NONNEG
  have hTA := TA_ge2 R S
  have e1 : s.A0 TA2 = true := A0_hi2b S TA2 (by omega) (by omega)
  have e0 : s.A0 (TA2 - 1) = false := A0_lob S _ (by omega) (by omega)
  obtain ⟨u, hu, hR, hv⟩ := R.H_SRV TA2 (by rw [e1, e0]; simp)
  rw [e1] at hR
  have hu1 : TA ≤ u := by
    by_cases hc : TA ≤ u
    · exact hc
    · have := hv (TA - 1) (by omega) (by omega)
      rw [A0_hi1b S (TA - 1) (by omega) (by omega), e0] at this; exact absurd this (by simp)
  by_cases hc : RRb D TA + D.smin ≤ TA2
  · exact hc
  · unfold TRb at hTA
    have := R0_lo2 R S u (by unfold TRb; omega) (by omega) (by omega)
    rw [hR] at this; exact absurd this (by simp)

/-- q is high from `QBb` to the horizon (set by the released hold, then held
at 1 when A0 re-rises). Only the fast (rise) view is needed. -/
theorem q_hi2 (R : Run D s) (S : Scn2 D s t0 ta TA TA2 Hz) :
    ∀ t, QBb D TA ≤ t → t < Hz → s.q t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.H_ORDER
  have hTA := TA_ge2 R S
  have hTA2 := TA2_ge2 R S
  unfold TRb at hTA; unfold RRb QBb at hTA2
  refine int_ind (fun t => QBb D TA ≤ t → t < Hz → s.q t = true) (QBb D TA)
    (fun t ht h _ => absurd h (by omega)) ?_
  intro t _ ih hb hz
  unfold QBb at hb
  have view : FS (s.r1 (t - D.wr1s - D.qr)) (s.r2 (t - D.wr2s - D.qr)) (s.q (t - D.wfb - D.qr))
      (s.A0 (t - D.wa0s - D.qr)) = true := by
    rw [S.H_r1 _ (by omega), r2_lo S _ (by omega) (by omega)]
    by_cases hc : t - D.wa0s - D.qr < TA2
    · rw [A0_lob S _ (by omega) hc, FS_set]
    · rw [A0_hi2b S _ (by omega) (by omega), FS_hold]
      exact ih _ (by omega) (by unfold QBb; omega) (by omega)
  rw [R.H_q t, view]
  rfl

theorem q_eq2 (R : Run D s) (S : Scn2 D s t0 ta TA TA2 Hz) (t : Int) (hz : t < Hz) :
    s.q t = decide (QBb D TA ≤ t) := by
  by_cases h : QBb D TA ≤ t
  · rw [q_hi2 R S t h hz]; simp [h]
  · rw [q_lo2 R S t (by omega)]; simp [h]

/-- **g1's exact trace**: it rises at `G1b = QBb + wq + g1rq`. -/
theorem g1_eq2 (R : Run D s) (S : Scn2 D s t0 ta TA TA2 Hz) (t : Int) (hz : t < Hz) :
    s.g1 t = decide (G1b D TA ≤ t) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL
  rw [R.H_g1 t, S.H_r1 _ (by omega), S.H_r1 (t - D.wr1g - D.g1f1) (by omega), FG1_r1, FG1_r1,
    q_eq2 R S _ (by omega), q_eq2 R S (t - D.wq - D.g1fq) (by omega)]
  unfold G1b
  by_cases h : QBb D TA + D.wq + D.g1rq ≤ t
  · have : QBb D TA ≤ t - D.wq - D.g1rq := by omega
    simp [h, this]
  · have e1 : ¬ QBb D TA ≤ t - D.wq - D.g1rq := by omega
    have e2 : ¬ QBb D TA ≤ t - D.wq - D.g1fq := by omega
    simp [h, e1, e2]

/-- **g2's exact trace**: it falls at `G2b = min (t0 + wr2g) (QBb + wq) + g2f`. -/
theorem g2_eq2 (R : Run D s) (S : Scn2 D s t0 ta TA TA2 Hz) (t : Int) (hz : t < Hz) :
    s.g2 t = decide (t < G2b D t0 TA) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL
  rw [R.H_g2 t, FG2_eq, FG2_eq, S.H_r2 _ (by omega), S.H_r2 (t - D.wr2g - D.g2f) (by omega),
    q_eq2 R S _ (by omega), q_eq2 R S (t - D.wq - D.g2f) (by omega)]
  unfold G2b
  by_cases h : t < min (t0 + D.wr2g) (QBb D TA + D.wq) + D.g2f
  · have e1 : t - D.wr2g - D.g2f < t0 := by omega
    have e2 : ¬ QBb D TA ≤ t - D.wq - D.g2f := by omega
    simp [h, e1, e2]
  · by_cases a : t - D.wr2g - D.g2r < t0 <;> by_cases b : QBb D TA ≤ t - D.wq - D.g2r <;>
    by_cases c : t - D.wr2g - D.g2f < t0 <;> by_cases d : QBb D TA ≤ t - D.wq - D.g2f <;>
    simp [a, b, c, d, h] <;> omega

/-! ### RT1, mirror direction -/

theorem overlap_exact2 (R : Run D s) (S : Scn2 D s t0 ta TA TA2 Hz) (t : Int) (hz : t < Hz) :
    (s.g1 t && s.g2 t) = true ↔ (G1b D TA ≤ t ∧ t < G2b D t0 TA) := by
  rw [g1_eq2 R S t hz, g2_eq2 R S t hz]
  simp

/-- RT1 for the mirror direction: g2's fall through r2 (`wr2g + g2f`) beats
r2↓ → R0↓ (`wr2s + Rf2`) → server (`smin`) → A0↓ at ustate (`wa0s`) → q↑ (`qr`)
→ q at ugrant (`wq`) → g1↑ (`g1rq`); or, structurally, `g2f ≤ g1rq`. -/
def RT1b (D : Dl) : Prop :=
  D.wr2g + D.g2f ≤ D.wr2s + D.Rf2 + D.smin + D.wa0s + D.qr + D.wq + D.g1rq ∨ D.g2f ≤ D.g1rq

theorem rt1_exclusion2 (R : Run D s) (S : Scn2 D s t0 ta TA TA2 Hz) (H_RT1 : RT1b D) :
    ∀ t, t < Hz → (s.g1 t && s.g2 t) = false := by
  have hTA := TA_ge2 R S
  intro t hz
  cases hc : (s.g1 t && s.g2 t)
  · rfl
  · have := (overlap_exact2 R S t hz).1 hc
    unfold G1b G2b QBb at this; unfold TRb at hTA; unfold RT1b at H_RT1
    omega

theorem rt1_counter2 (R : Run D s) (S : Scn2 D s t0 ta TA TA2 Hz)
    (H_r2slow : G1b D TA < t0 + D.wr2g + D.g2f) (H_qslow : D.g1rq < D.g2f)
    (hz : G1b D TA < Hz) :
    s.g1 (G1b D TA) = true ∧ s.g2 (G1b D TA) = true := by
  have := (overlap_exact2 R S (G1b D TA) hz).2 ⟨Int.le_refl _, by unfold G1b G2b at *; omega⟩
  simpa using this

theorem rt1_counter2_minserver (R : Run D s) (S : Scn2 D s t0 ta TA TA2 Hz)
    (H_fast : TA = TRb D t0 + D.smin) (H_not : ¬ RT1b D) (hz : G1b D TA < Hz) :
    s.g1 (G1b D TA) = true ∧ s.g2 (G1b D TA) = true := by
  unfold RT1b at H_not
  apply rt1_counter2 R S _ (by omega) hz
  unfold G1b QBb; unfold TRb at H_fast; omega

/-! ### RT2, mirror direction -/

/-- A2's fall instant. -/
def T1b (D : Dl) (t0 TA : Int) : Int := max (G2b D t0 TA + D.wg2) (TA + D.wa02) + D.c2f
/-- A1's earliest rise. -/
def T2b (D : Dl) (TA2 : Int) : Int := TA2 + D.wa01 + D.c1r

theorem A2_low_after2 (R : Run D s) (S : Scn2 D s t0 ta TA TA2 Hz)
    (H_RT2a : T1b D t0 TA + D.wfa2 ≤ TA2 + D.wa02) :
    ∀ t, T1b D t0 TA ≤ t → t < Hz → s.A2 t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.H_ORDER
  refine int_ind (fun t => T1b D t0 TA ≤ t → t < Hz → s.A2 t = false) (T1b D t0 TA)
    (fun t ht h _ => absurd h (by omega)) ?_
  intro t _ ih hb hz
  unfold T1b at hb H_RT2a
  have view : ∀ d, D.c2r ≤ d → d ≤ D.c2f →
      CE (s.g2 (t - D.wg2 - d)) (s.A0 (t - D.wa02 - d)) (s.A2 (t - D.wfa2 - d)) = false := by
    intro d hd1 hd2
    rw [g2_eq2 R S _ (by omega), CE_eq]
    have : ¬ (t - D.wg2 - d < G2b D t0 TA) := by omega
    simp only [this, decide_false, Bool.false_and, Bool.false_or]
    by_cases hc : t - D.wa02 - d < TA2
    · rw [A0_lob S _ (by omega) hc]; simp
    · rw [ih _ (by omega) (by unfold T1b; omega) (by omega)]; simp
  rw [R.H_A2 t, view D.c2r (by omega) (by omega), view D.c2f (by omega) (by omega)]
  rfl

theorem A1_low_before2 (R : Run D s) (S : Scn2 D s t0 ta TA TA2 Hz)
    (H_A0_FORK : TA + D.wa01 ≤ G1b D TA + D.wg1) :
    ∀ t, t < T2b D TA2 → t < Hz → s.A1 t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.H_ORDER
  refine int_ind (fun t => t < T2b D TA2 → t < Hz → s.A1 t = false) t0
    (fun t ht _ _ => S.H_A1_init t ht) ?_
  intro t _ ih hb hz
  unfold T2b at hb
  have view : ∀ d, D.c1r ≤ d → d ≤ D.c1f →
      CE (s.g1 (t - D.wg1 - d)) (s.A0 (t - D.wa01 - d)) (s.A1 (t - D.wfa1 - d)) = false := by
    intro d hd1 hd2
    rw [ih _ (by omega) (by unfold T2b; omega) (by omega), CE_eq, g1_eq2 R S _ (by omega)]
    by_cases hc : t - D.wa01 - d < TA
    · have : ¬ (G1b D TA ≤ t - D.wg1 - d) := by omega
      simp [this]
    · rw [A0_lob S _ (by omega) (by omega)]; simp
  rw [R.H_A1 t, view D.c1r (by omega) (by omega), view D.c1f (by omega) (by omega)]
  rfl

theorem rt2_exclusion2 (R : Run D s) (S : Scn2 D s t0 ta TA TA2 Hz)
    (H_RT2a : T1b D t0 TA + D.wfa2 ≤ TA2 + D.wa02)
    (H_RT2b : T1b D t0 TA ≤ T2b D TA2)
    (H_A0_FORK : TA + D.wa01 ≤ G1b D TA + D.wg1) :
    ∀ t, t < Hz → (s.A1 t && s.A2 t) = false := by
  intro t hz
  by_cases h : T1b D t0 TA ≤ t
  · rw [A2_low_after2 R S H_RT2a t h hz]; simp
  · rw [A1_low_before2 R S H_A0_FORK t (by omega) hz]; simp

/-- RT2 in arc terms, mirror direction (sufficient for every server):
`pulse` is the tightest with prjxray arcs (q RISES here, so the low pulse of
A0 is shorter by `qf - qr` than in 7h's direction). -/
structure RT2b (D : Dl) : Prop where
  pulse : D.c2f + D.wfa2 ≤ D.wa0s + D.qr + D.wfb + D.Rrq + D.smin
  g2 : D.wr2g + D.g2f + D.wg2 + D.c2f + D.wfa2 ≤
    D.wr2s + D.Rf2 + 2 * D.smin + D.wa0s + D.qr + D.wfb + D.Rrq + D.wa02
  forkA : D.wa02 + D.c2f ≤ D.wa0s + D.qr + D.wfb + D.Rrq + D.smin + D.wa01 + D.c1r
  forkG : D.wr2g + D.g2f + D.wg2 + D.c2f ≤
    D.wr2s + D.Rf2 + 2 * D.smin + D.wa0s + D.qr + D.wfb + D.Rrq + D.wa01 + D.c1r

/-- 7g's H_A0_FORK, mirror (client 1's side): A0 to ua1 no slower than
A0 → ustate → q↑ → ugrant → g1↑ → ua1. -/
def A0Fork2 (D : Dl) : Prop := D.wa01 ≤ D.wa0s + D.qr + D.wq + D.g1rq + D.wg1

theorem rt2_exclusion2_arcs (R : Run D s) (S : Scn2 D s t0 ta TA TA2 Hz)
    (H_RT2 : RT2b D) (H_fork : A0Fork2 D) :
    ∀ t, t < Hz → (s.A1 t && s.A2 t) = false := by
  have := D.H_NONNEG
  have hTA := TA_ge2 R S
  have hTA2 := TA2_ge2 R S
  obtain ⟨h1, h2, h3, h4⟩ := H_RT2
  unfold TRb at hTA; unfold RRb QBb at hTA2; unfold A0Fork2 at H_fork
  apply rt2_exclusion2 R S
  · unfold T1b G2b QBb; omega
  · unfold T1b T2b G2b QBb; omega
  · unfold G1b QBb; omega

/-- **Mirror counter-trace, part 1: A2's fall is swallowed.** -/
theorem A2_stuck2 (R : Run D s) (S : Scn2 D s t0 ta TA TA2 Hz)
    (H_CT2 : TA2 + D.wa02 ≤ max (G2b D t0 TA + D.wg2) (TA + D.wa02 + D.c2f - D.c2r)) :
    ∀ t, t < Hz → s.A2 t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.H_ORDER; have := S.H_SETTLED
  refine int_ind (fun t => t < Hz → s.A2 t = true) t0 (fun t ht _ => S.H_A2_init t ht) ?_
  intro t ht ih hz
  rw [R.H_A2 t, CE_eq, CE_eq, ih (t - D.wfa2 - D.c2f) (by omega) (by omega),
    ih (t - D.wfa2 - D.c2r) (by omega) (by omega)]
  simp only [Bool.and_true, Bool.or_eq_true]
  by_cases hg : t - D.wg2 - D.c2f < G2b D t0 TA
  · right; rw [g2_eq2 R S _ (by omega)]; simp [hg]
  · by_cases hA : t - D.wa02 - D.c2f < TA
    · right; rw [A0_hi1b S _ (by omega) hA]; simp
    · by_cases hB : TA2 ≤ t - D.wa02 - D.c2f
      · right; rw [A0_hi2b S _ hB (by omega)]; simp
      · left; rw [A0_hi2b S _ (by omega) (by omega)]; simp

/-- **Mirror counter-trace, part 2: both clients acknowledged at `T2b`.** -/
theorem rt2_counter2 (R : Run D s) (S : Scn2 D s t0 ta TA TA2 Hz)
    (H_CT2 : TA2 + D.wa02 ≤ max (G2b D t0 TA + D.wg2) (TA + D.wa02 + D.c2f - D.c2r))
    (H_g1_there : G1b D TA + D.wg1 ≤ TA2 + D.wa01) (hz : T2b D TA2 < Hz) :
    s.A1 (T2b D TA2) = true ∧ s.A2 (T2b D TA2) = true := by
  have := D.H_NONNEG; have := S.H_ORDER
  refine ⟨?_, A2_stuck2 R S H_CT2 _ hz⟩
  unfold T2b at *
  rw [R.H_A1, CE_eq]
  have e1 : TA2 + D.wa01 + D.c1r - D.wg1 - D.c1r = TA2 + D.wa01 - D.wg1 := by omega
  have e2 : TA2 + D.wa01 + D.c1r - D.wa01 - D.c1r = TA2 := by omega
  rw [e1, e2, g1_eq2 R S _ (by omega), A0_hi2b S TA2 (by omega) (by omega)]
  have : G1b D TA ≤ TA2 + D.wa01 - D.wg1 := by omega
  simp [this]

end

/-! ## prjxray arcs, mirror direction -/

/-- **RT1 mirror with prjxray arcs**: r2's route to ugrant at most
`136 + smin + wa0s + wq` longer than to ustate (136 = 152 + 56 + 52 − 124). -/
theorem prj_RT1b (wr1s wr2s wr1g wr2g wfb wa0s wq wg1 wa01 wfa1 wg2 wa02 wfa2 smin : Int) (h)
    (H : wr2g ≤ wr2s + 136 + smin + wa0s + wq) :
    RT1b (prj wr1s wr2s wr1g wr2g wfb wa0s wq wg1 wa01 wfa1 wg2 wa02 wfa2 smin h) := by
  unfold RT1b prj; simp only; omega

/-- **RT2 mirror with prjxray arcs**: the four conditions reduce to
* pulse: `wfa2 + 16 ≤ smin + wa0s + wfb`
* g2:    `wr2g + wg2 + wfa2 ≤ wr2s + 2 smin + 12 + wa0s + wfb + wa02`
* forkA: `wa02 ≤ wa01 + smin + 40 + wa0s + wfb`
* forkG: `wr2g + wg2 ≤ wr2s + 2 smin + 68 + wa0s + wfb + wa01`. -/
theorem prj_RT2b (wr1s wr2s wr1g wr2g wfb wa0s wq wg1 wa01 wfa1 wg2 wa02 wfa2 smin : Int) (h)
    (Hp : wfa2 + 16 ≤ smin + wa0s + wfb)
    (Hg : wr2g + wg2 + wfa2 ≤ wr2s + 2 * smin + 12 + wa0s + wfb + wa02)
    (Ha : wa02 ≤ wa01 + smin + 40 + wa0s + wfb)
    (HG : wr2g + wg2 ≤ wr2s + 2 * smin + 68 + wa0s + wfb + wa01) :
    RT2b (prj wr1s wr2s wr1g wr2g wfb wa0s wq wg1 wa01 wfa1 wg2 wa02 wfa2 smin h) := by
  constructor <;> (unfold prj; simp only; omega)

/-- Mirror fork with prjxray arcs: `wa01 ≤ wa0s + 108 + wq + wg1`. -/
theorem prj_fork2 (wr1s wr2s wr1g wr2g wfb wa0s wq wg1 wa01 wfa1 wg2 wa02 wfa2 smin : Int) (h)
    (H : wa01 ≤ wa0s + 108 + wq + wg1) :
    A0Fork2 (prj wr1s wr2s wr1g wr2g wfb wa0s wq wg1 wa01 wfa1 wg2 wa02 wfa2 smin h) := by
  unfold A0Fork2 prj; simp only; omega

/-- **Arc-only corner, mirror** (every route 0, 112 ps server): all hold.
Margins: RT1 136 + 112 = 248; pulse 96; g2 236; forkA 152; forkG 292; fork 108 ps. -/
theorem prj_arc_only2 :
    let D := prj 0 0 0 0 0 0 0 0 0 0 0 0 0 112 (by omega)
    RT1b D ∧ RT2b D ∧ A0Fork2 D := by
  refine ⟨?_, ?_, ?_⟩
  · exact prj_RT1b 0 0 0 0 0 0 0 0 0 0 0 0 0 112 _ (by omega)
  · exact prj_RT2b 0 0 0 0 0 0 0 0 0 0 0 0 0 112 _ (by omega) (by omega) (by omega) (by omega)
  · exact prj_fork2 0 0 0 0 0 0 0 0 0 0 0 0 0 112 _ (by omega)

/-- The pulse margin of the mirror direction is exactly `smin + wa0s + wfb − wfa2 − 16`:
at zero routing it is 96 ps with a 112 ps server, and it FAILS for a server
faster than 16 ps (so the condition is not vacuously true). -/
theorem prj_pulse2_tight (smin : Int) (h) :
    let D := prj 0 0 0 0 0 0 0 0 0 0 0 0 0 smin h
    (D.c2f + D.wfa2 ≤ D.wa0s + D.qr + D.wfb + D.Rrq + D.smin) ↔ 16 ≤ smin := by
  simp only [prj]; omega

/-! ## Non-vacuity: a concrete delay set and traces satisfying everything

`D0`: prjxray arcs, every route 0, server minimum response 112 ps (two LUT1
rise arcs). It satisfies RT1, RT2, A0Fork (7h) and RT1b, RT2b, A0Fork2 (here).

`W1` (7h's direction, `t0 = 0`, `ta = -1000`): the server answers in exactly
`smin` both times: `TA = TR + smin = 152 + 112 = 264`,
`TA2 = RR + smin = 440 + 112 = 552`. Traces (step functions over ℤ):
r1 = [t < 0], r2 = 1, A0 = [-1000 ≤ t < 264] ∨ [552 ≤ t], q = [t < 388],
R0 = [t < 152] ∨ [440 ≤ t], g1 = [t < 152], g2 = [444 ≤ t], A1 = [t < 388],
A2 = [608 ≤ t]. Before `ta` the state is the stylised settled past (A0 low,
R0 high, q = A1 = 1, A2 = 0); after the horizon the inputs stay put and the
state is a fixed point, so the gate relations and `Server` hold for ALL t.

`W2` (mirror, `t0 = 0`, `ta = -1000`): `TA = TRb + smin = 264`,
`TA2 = RRb + smin = 372 + 112 = 484`; r1 = 1, r2 = [t < 0],
A0 = [-1000 ≤ t < 264] ∨ [484 ≤ t], q = [320 ≤ t], R0 = [t < 152] ∨ [372 ≤ t],
g1 = [372 ≤ t], g2 = [t < 124], A1 = [540 ≤ t], A2 = [t < 388].

Every value above was derived by hand from the formulas (`TR`, `QB`, ...),
and the proofs below check the gate relations at every t, so a wrong value
would fail to check. -/

def D0 : Dl := prj 0 0 0 0 0 0 0 0 0 0 0 0 0 10 (by omega)

theorem D0_all : RT1 D0 ∧ RT2 D0 ∧ A0Fork D0 ∧ RT1b D0 ∧ RT2b D0 ∧ A0Fork2 D0 :=
  ⟨prj_arc_only.1, prj_arc_only.2.1, prj_arc_only.2.2,
   prj_arc_only2.1, prj_arc_only2.2.1, prj_arc_only2.2.2⟩

def W1 : Sigs where
  r1 := fun t => decide (t < 0)
  r2 := fun _ => true
  q := fun t => decide (t < 388)
  R0 := fun t => decide (t < 152) || decide (440 ≤ t)
  g1 := fun t => decide (t < 152)
  g2 := fun t => decide (444 ≤ t)
  A0 := fun t => (decide (-1000 ≤ t) && decide (t < 264)) || decide (552 ≤ t)
  A1 := fun t => decide (t < 388)
  A2 := fun t => decide (608 ≤ t)

def W2 : Sigs where
  r1 := fun _ => true
  r2 := fun t => decide (t < 0)
  q := fun t => decide (320 ≤ t)
  R0 := fun t => decide (t < 152) || decide (372 ≤ t)
  g1 := fun t => decide (372 ≤ t)
  g2 := fun t => decide (t < 124)
  A0 := fun t => (decide (-1000 ≤ t) && decide (t < 264)) || decide (484 ≤ t)
  A1 := fun t => decide (540 ≤ t)
  A2 := fun t => decide (t < 388)

theorem W1_run : Run D0 W1 where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [W1, D0, prj, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [W1, D0, prj, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [W1, D0, prj, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [W1, D0, prj, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [W1, D0, prj, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [W1, D0, prj, CE_eq]; omega
  H_SRV := by
    intro t h
    have ht : t = -1000 ∨ t = 264 ∨ t = 552 := by
      exact Classical.byContradiction fun hc => h (by rw [Bool.eq_iff_iff]; simp [W1]; omega)
    rcases ht with rfl | rfl | rfl
    · exact ⟨-1112, by simp [D0, prj], by simp [W1], fun v _ _ => by simp [W1]; omega⟩
    · exact ⟨152, by simp [D0, prj], by simp [W1], fun v _ _ => by simp [W1]; omega⟩
    · exact ⟨440, by simp [D0, prj], by simp [W1], fun v _ _ => by simp [W1]; omega⟩

theorem W2_run : Run D0 W2 where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [W2, D0, prj, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [W2, D0, prj, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [W2, D0, prj, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [W2, D0, prj, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [W2, D0, prj, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [W2, D0, prj, CE_eq]; omega
  H_SRV := by
    intro t h
    have ht : t = -1000 ∨ t = 264 ∨ t = 484 := by
      exact Classical.byContradiction fun hc => h (by rw [Bool.eq_iff_iff]; simp [W2]; omega)
    rcases ht with rfl | rfl | rfl
    · exact ⟨-1112, by simp [D0, prj], by simp [W2], fun v _ _ => by simp [W2]; omega⟩
    · exact ⟨152, by simp [D0, prj], by simp [W2], fun v _ _ => by simp [W2]; omega⟩
    · exact ⟨372, by simp [D0, prj], by simp [W2], fun v _ _ => by simp [W2]; omega⟩

theorem W1_scn (Hz : Int) (hz : 552 < Hz) : Scn D0 W1 0 (-1000) 264 552 Hz where
  H_ORDER := by omega
  H_r1 := fun _ _ => rfl
  H_r2 := fun _ _ => rfl
  H_A0 := by intro t h1 _; rw [Bool.eq_iff_iff]; simp [W1]; omega
  H_A0_prev := by simp [W1]
  H_q_init := by intro t h; simp [W1]; omega
  H_A1_init := by intro t h; simp [W1]; omega
  H_A2_init := by intro t h; simp [W1]; omega
  H_SETTLED := by simp [D0, prj]

theorem W2_scn (Hz : Int) (hz : 484 < Hz) : Scn2 D0 W2 0 (-1000) 264 484 Hz where
  H_ORDER := by omega
  H_r1 := fun _ _ => rfl
  H_r2 := fun _ _ => rfl
  H_A0 := by intro t h1 _; rw [Bool.eq_iff_iff]; simp [W2]; omega
  H_A0_prev := by simp [W2]
  H_q_init := by intro t h; simp [W2]; omega
  H_A1_init := by intro t h; simp [W2]; omega
  H_A2_init := by intro t h; simp [W2]; omega
  H_SETTLED := by simp [D0, prj]

/-- The server of both witnesses answers in exactly `smin` (the worst case the
arc-form conditions are stated for), so the arc-form theorems are tight here. -/
theorem W_minserver : (264 : Int) = TR D0 0 + D0.smin ∧ (552 : Int) = RR D0 264 + D0.smin ∧
    (264 : Int) = TRb D0 0 + D0.smin ∧ (484 : Int) = RRb D0 264 + D0.smin := by
  simp [TR, RR, QB, TRb, RRb, QBb, D0, prj]

/-- **Non-vacuity.** There is a delay set satisfying every arc condition of
both directions, and for each direction a run of the gate relations (for all
t, server included) that satisfies that direction's scenario for every horizon
past the second server edge. So `rt1_exclusion`, `rt2_exclusion_arcs`,
`rt1_exclusion2`, `rt2_exclusion2_arcs` are not vacuous. -/
theorem nonvacuous : ∃ (D : Dl) (s s' : Sigs) (t0 ta TA TA2 TA' TA2' : Int),
    RT1 D ∧ RT2 D ∧ A0Fork D ∧ RT1b D ∧ RT2b D ∧ A0Fork2 D ∧
    Run D s ∧ (∀ Hz, TA2 < Hz → Scn D s t0 ta TA TA2 Hz) ∧
    Run D s' ∧ (∀ Hz, TA2' < Hz → Scn2 D s' t0 ta TA' TA2' Hz) :=
  ⟨D0, W1, W2, 0, -1000, 264, 552, 264, 484,
    D0_all.1, D0_all.2.1, D0_all.2.2.1, D0_all.2.2.2.1, D0_all.2.2.2.2.1, D0_all.2.2.2.2.2,
    W1_run, W1_scn, W2_run, W2_scn⟩

/-! ## The runt band (7h's direction)

7h proved: RT2a (`T1 + wfa1 ≤ TA2 + wa01`) ⇒ A1 falls and stays low
(`A1_low_after`), and `A1_stuck`'s condition ⇒ A1 never falls. Between them,
A1's FIRST excursion is exact and needs no extra hypothesis:

* `A1_hi_before`: A1 is high before `T1`.
* `A1_runt_low`: A1 is low on `[T1, TA2 + wa01 + c1r)`.
* `A1_runt_high`: A1 is high again on `[TA2 + wa01 + c1r, T1 + c1r + wfa1)`.

With g1's fall at ua1 no later than A0's (`G1 + wg1 ≤ TA + wa01`, so
`T1 = TA + wa01 + c1f`) and `p = TA2 − TA` the length of A0's low pulse (equal
at ua1 and at the server, routes being pure delays), the low interval is
non-empty iff `p > c1f − c1r` (the complement of `A1_stuck`'s second
disjunct) and the high interval is non-empty iff `p < c1f + wfa1` (the
complement of RT2a). So the band is exactly `c1f − c1r < p < c1f + wfa1`: A1
makes a low runt of width `p − (c1f − c1r)`, then re-latches high for
`c1f + wfa1 − p` (the hole has not yet come round ua1's fast loop
`c1r + wfa1`). `A1_runt_overlap`: if A2's rise lands in that window, both
acks are high. With matched A0 forks and arcs (`wa02 + c2r = wa01 + c1r`)
A2 rises exactly at the window's start, so EVERY pulse in the band gives an
ack overlap (`A1_band_overlap_matched`).

After the window the low hole recirculates through ua1's loop; in this
rise-fast OR-channel model each round shrinks it by `c1f − c1r` (hand
analysis, not proved here), so A1 ends latched high with a decaying runt
train: the C-element runt regime of `CElemTiming`. The silicon outcome of
sub-arc runts is not determined by this model (no inertial rejection). -/

section
variable {D : Dl} {s : Sigs} {t0 ta TA TA2 Hz : Int}

theorem A1_hi_before (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz) :
    ∀ t, t < T1 D t0 TA → t < Hz → s.A1 t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.H_ORDER; have := S.H_SETTLED
  refine int_ind (fun t => t < T1 D t0 TA → t < Hz → s.A1 t = true) t0
    (fun t ht _ _ => S.H_A1_init t ht) ?_
  intro t ht ih hb hz
  unfold T1 at hb
  rw [R.H_A1 t, CE_eq, CE_eq, ih (t - D.wfa1 - D.c1f) (by omega) (by unfold T1; omega) (by omega)]
  simp only [Bool.and_true, Bool.or_eq_true]
  right
  by_cases hg : t - D.wg1 - D.c1f < G1 D t0 TA
  · rw [g1_eq R S _ (by omega)]; simp [hg]
  · rw [A0_hi1 S _ (by omega) (by omega)]; simp

theorem A1_runt_low (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz) :
    ∀ t, T1 D t0 TA ≤ t → t < TA2 + D.wa01 + D.c1r → t < Hz → s.A1 t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := S.H_ORDER
  intro t h1 h2 hz
  unfold T1 at h1
  have view : ∀ d, D.c1r ≤ d → d ≤ D.c1f →
      CE (s.g1 (t - D.wg1 - d)) (s.A0 (t - D.wa01 - d)) (s.A1 (t - D.wfa1 - d)) = false := by
    intro d hd1 hd2
    have : ¬ (t - D.wg1 - d < G1 D t0 TA) := by omega
    rw [g1_eq R S _ (by omega), A0_lo S _ (by omega) (by omega), CE_eq]
    simp [this]
  rw [R.H_A1 t, view D.c1r (by omega) (by omega), view D.c1f (by omega) (by omega)]
  rfl

theorem A1_runt_high (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz) :
    ∀ t, TA2 + D.wa01 + D.c1r ≤ t → t < T1 D t0 TA + D.c1r + D.wfa1 → t < Hz →
      s.A1 t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := S.H_ORDER
  intro t h1 h2 hz
  rw [R.H_A1 t, CE_eq, A0_hi2 S _ (by omega) (by omega),
    A1_hi_before R S (t - D.wfa1 - D.c1r) (by omega) (by omega)]
  simp

/-- **Runt-band ack overlap**: if A2's rise falls in A1's re-latch window, and
g2 is at ua2 when A0 re-rises there, both acks are high at `T2`. -/
theorem A1_runt_overlap (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz)
    (H_in : TA2 + D.wa01 + D.c1r ≤ T2 D TA2) (H_in' : T2 D TA2 < T1 D t0 TA + D.c1r + D.wfa1)
    (H_g2_there : G2 D TA + D.wg2 ≤ TA2 + D.wa02) (hz : T2 D TA2 < Hz) :
    s.A1 (T2 D TA2) = true ∧ s.A2 (T2 D TA2) = true := by
  have := D.H_NONNEG; have := S.H_ORDER
  refine ⟨A1_runt_high R S _ H_in H_in' hz, ?_⟩
  unfold T2 at *
  rw [R.H_A2, CE_eq]
  have e1 : TA2 + D.wa02 + D.c2r - D.wg2 - D.c2r = TA2 + D.wa02 - D.wg2 := by omega
  have e2 : TA2 + D.wa02 + D.c2r - D.wa02 - D.c2r = TA2 := by omega
  rw [e1, e2, g2_eq R S _ (by omega), A0_hi2 S TA2 (by omega) (by omega)]
  have : G2 D TA ≤ TA2 + D.wa02 - D.wg2 := by omega
  simp [this]

/-- **The band, in pulse-length terms** (g1 at ua1 before A0's fall): for
`c1f − c1r < TA2 − TA < c1f + wfa1`, A1 is high just before `T1`, low at `T1`,
and high again at `TA2 + wa01 + c1r`. -/
theorem A1_band (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz)
    (H_g1early : G1 D t0 TA + D.wg1 ≤ TA + D.wa01)
    (H_lo : D.c1f - D.c1r < TA2 - TA) (H_hi : TA2 - TA < D.c1f + D.wfa1)
    (hz : TA2 + D.wa01 + D.c1r < Hz) :
    s.A1 (T1 D t0 TA - 1) = true ∧ s.A1 (T1 D t0 TA) = false ∧
      s.A1 (TA2 + D.wa01 + D.c1r) = true := by
  have hT : T1 D t0 TA = TA + D.wa01 + D.c1f := by unfold T1; omega
  refine ⟨A1_hi_before R S _ (by omega) (by omega),
    A1_runt_low R S _ (by omega) (by omega) (by omega),
    A1_runt_high R S _ (by omega) (by omega) hz⟩

/-- **Matched forks: every band pulse is an ack overlap.** With
`wa02 + c2r = wa01 + c1r` (same A0 route and arc to both C-elements), g1
early, g2 at ua2 in time, and the pulse in the band, A1 and A2 are both
high at `T2`. -/
theorem A1_band_overlap_matched (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz)
    (H_match : D.wa02 + D.c2r = D.wa01 + D.c1r)
    (H_g1early : G1 D t0 TA + D.wg1 ≤ TA + D.wa01)
    (H_hi : TA2 - TA < D.c1f + D.wfa1)
    (H_g2_there : G2 D TA + D.wg2 ≤ TA2 + D.wa02) (hz : T2 D TA2 < Hz) :
    s.A1 (T2 D TA2) = true ∧ s.A2 (T2 D TA2) = true := by
  apply A1_runt_overlap R S _ _ H_g2_there hz
  · unfold T2; omega
  · unfold T2 T1; omega

end

end Formal.Cells.ArbHeldTimed2

