import Formal.Cells.Prelim

/-!
# Probe 7h: timed exclusion of the HELD `bd_arbiter` (`cells/rtl/bd_arb.v`)

Probe 7e (`ArbHandover.lean`) showed that in the held arbiter (state node INIT
64'hFFF0_FFB2_ACAC_ACAC) grant exclusion `g1.g2` and ack exclusion `A1.A2` are
NOT speed-independent (`held_grant_overlap_untimed`, `held_ack_overlap_untimed`).
This file names the relative-timing conditions and proves them in a timed model.

## Model (same style as 7e, Part 1)

* Time is `Int` picoseconds; a signal is `Int → Bool`.
* Every LUT output is the rise-fast asymmetric pure-delay channel of 7e:
  `o t = f (pins at their rise arcs) || f (pins at their fall arcs)`, each pin
  additionally delayed by its route (routes include the site-pin delay).
* The functions are the REAL INITs through `lutB`/`o5B`/`o6B`:
  `ustate` 0xFFF0FFB2ACACACAC (O6 = q, O5 = R0), `ugrant` 0x0C0C0C0CA0A0A0A0
  (O5 = g1, O6 = g2), `ua1`/`ua2` = `bd_c2` 0x00E800E800E800E8.
* The server is a relation (`Server`), not a delay: it changes A0 only in
  response to a value R0 had at least `smin` (H_SERVER_MIN) earlier, while the
  server was still in its previous phase. Any four-phase server at least that
  slow satisfies it (a delay-chain server of a hazard-free R0 does).
* Scenario (`Scn`): client 1 holds the resource (q = 1, A0 = 1, A1 = 1), client 2
  waits (r2 = 1), client 1 drops r1 at `t0`. The server's actual edges are
  `TA` (A0 falls) and `TA2` (A0 re-rises for client 2); they are free
  parameters, constrained only by `Server`. Everything holds up to a horizon
  `Hz` before which no client moves again.

## Results

* Exact traces: `q_eq`, `R0` bounds, `g1_eq`, `g2_eq`.
* `TA_ge`, `TA2_ge`: the server relation forces
  `TA ≥ t0 + wr1s + Rf1 + smin` and `TA2 ≥ TA + wa0s + qf + wfb + Rrq + smin`.
* RT1: `overlap_exact` (g1.g2 at t iff `G2 ≤ t < G1`), `rt1_exclusion`
  (arc-form RT1 ⇒ never both grants, for every server), `rt1_counter`
  (counter-trace when RT1 fails).
* RT2: `A1_low_after` / `A2_low_before` / `rt2_exclusion` (run form),
  `rt2_exclusion_arcs` (arc form, every server), `A1_stuck` / `rt2_counter`
  (counter-trace: A1's fall swallowed, A1.A2 both high).
* `prj_*`: the conditions with the numbers of `cells/sim/bd_prims_sim.v`.

**Audit correction (claude/audit REPORT rows 10, 24; findings AB2 #2).** The
pairs 56/124 (O6), 55/152 (O5 I0/I1) and 52/150 (O5 I2) used by `prj` are NOT
rise/fall arcs: they are prjxray's FAST_MAX and SLOW_MAX of ONE arc
(`prjxray/utils/makesdf.py:63` writes `(FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX)`,
each triple applying to both edges). The numeric instance `prj` therefore mixes
corners (fast-corner rises with slow-corner falls; `ArbCorners.prj_is_mix`), and
its margins (292/164/276/220/332 ps, "112 ps server") are artefacts. The generic
theorems (every `Dl`, including rise = fall) are unaffected. Corrected values at
a consistent corner: `ArbCorners.arcs_slowMax`/`arcs_fastMin` (arc parts),
`ArbCorners.slow_arc_only`/`fast_arc_only` (arc-only margins, server = two arcs
at the same corner: 248 / 90 ps), `ArbCorners.box_7h` (each arc independently
in [FAST_MIN, SLOW_MAX]). Rise/fall asymmetry is unmeasured
(`ArbCorners.RF`, H_RF_ASYM).
-/

namespace Formal.Cells.ArbHeldTimed
open Formal.Cells

/-! ## INITs and their equations -/

def INIT_HELD : Nat := 0xFFF0FFB2ACACACAC
def INIT_GRANTS : Nat := 0x0C0C0C0CA0A0A0A0
def INIT_C2 : Nat := 0x00E800E800E800E8

/-- `ustate` O6 (q), pins I0 r1, I1 r2, I2 q (routed back), I3 rst = 0, I4 A0, I5 1. -/
def FS (r1 r2 q a0 : Bool) : Bool := o6B INIT_HELD [r1, r2, q, false, a0, true]
/-- `ustate` O5 (R0). The O5 function does not depend on I4 (A0); see `FR_indep`. -/
def FR (r1 r2 q : Bool) : Bool := o5B INIT_HELD [r1, r2, q, false, false]
/-- `ugrant` O5 = g1. -/
def FG1 (r1 r2 q : Bool) : Bool := o5B INIT_GRANTS [r1, r2, q, false, false]
/-- `ugrant` O6 = g2. -/
def FG2 (r1 r2 q : Bool) : Bool := o6B INIT_GRANTS [r1, r2, q, false, false, true]
/-- `bd_c2` with rst = 0: I0 grant, I1 A0, I2 own output. -/
def CE (g a fb : Bool) : Bool := lutB INIT_C2 [g, a, fb, false, false, false]

theorem FS_eq : ∀ r1 r2 q a0 : Bool,
    FS r1 r2 q a0 = (if a0 then q else ((r1 && !r2) || (r1 && q) || (!r2 && q))) := by decide
theorem FR_indep : ∀ r1 r2 q a0 : Bool,
    o5B INIT_HELD [r1, r2, q, false, a0] = FR r1 r2 q := by decide
theorem FR_eq : ∀ r1 r2 q : Bool, FR r1 r2 q = ((r1 && q) || (r2 && !q)) := by decide
theorem FG1_eq : ∀ r1 r2 q : Bool, FG1 r1 r2 q = (r1 && q) := by decide
theorem FG2_eq : ∀ r1 r2 q : Bool, FG2 r1 r2 q = (r2 && !q) := by decide
theorem CE_eq : ∀ g a fb : Bool, CE g a fb = ((g && a) || (g && fb) || (a && fb)) := by decide

/-- The hold: A0 high, q follows its own feedback whatever the requests. -/
theorem FS_hold : ∀ r1 r2 q : Bool, FS r1 r2 q true = q := by decide
/-- Release with r1 low, r2 high: q resets. -/
theorem FS_rel : ∀ q : Bool, FS false true q false = false := by decide
theorem FR_r1r2 : ∀ q : Bool, FR true true q = true := by decide
theorem FR_lo : ∀ r2 : Bool, FR false r2 true = false := by decide

/-! ## Delays (all named hypotheses) -/

abbrev Sig := Int → Bool

/-- Delays in ps. Routes `w..` run from the driving output to the function's
view of the pin and INCLUDE the site-pin (input buffer) delay of the physical
pin (B-muxtree-fidelity: A1 slowest .. A6 fastest). Arcs are cell arcs.
Test: routed SDF interconnect + prjxray `tile_type_CLBLL_*.json` site-pin
delays + cell arcs; board: not directly measurable. -/
structure Dl where
  /-- routes: r1/r2 to ustate (I0/I1) and to ugrant (I0/I1). -/
  wr1s : Int
  wr2s : Int
  wr1g : Int
  wr2g : Int
  /-- q routed back to ustate's own I2 (read by both O6 and O5). -/
  wfb : Int
  /-- A0 to ustate I4 (the hold pin). -/
  wa0s : Int
  /-- q to ugrant I2. -/
  wq : Int
  /-- ua1: g1 pin, A0 pin, own feedback. -/
  wg1 : Int
  wa01 : Int
  wfa1 : Int
  /-- ua2: g2 pin, A0 pin, own feedback. -/
  wg2 : Int
  wa02 : Int
  wfa2 : Int
  /-- ustate O6 arcs (flat over pins). -/
  qr : Int
  qf : Int
  /-- ustate O5 (R0) arcs per pin: I0 (r1), I1 (r2), I2 (q). -/
  Rr1 : Int
  Rf1 : Int
  Rr2 : Int
  Rf2 : Int
  Rrq : Int
  Rfq : Int
  /-- ugrant O5 (g1) arcs per pin: I0, I1, I2. -/
  g1r1 : Int
  g1f1 : Int
  g1r2 : Int
  g1f2 : Int
  g1rq : Int
  g1fq : Int
  /-- ugrant O6 (g2) arcs (flat). -/
  g2r : Int
  g2f : Int
  /-- ua1 / ua2 O6 arcs (flat). -/
  c1r : Int
  c1f : Int
  c2r : Int
  c2f : Int
  /-- H_SERVER_MIN: minimum server response time (R0 edge to A0 edge). -/
  smin : Int
  /-- H_NONNEG: causality, every route and arc is non-negative, and so is smin. -/
  H_NONNEG : 0 ≤ wr1s ∧ 0 ≤ wr2s ∧ 0 ≤ wr1g ∧ 0 ≤ wr2g ∧ 0 ≤ wfb ∧ 0 ≤ wa0s ∧
    0 ≤ wq ∧ 0 ≤ wg1 ∧ 0 ≤ wa01 ∧ 0 ≤ wfa1 ∧ 0 ≤ wg2 ∧ 0 ≤ wa02 ∧ 0 ≤ wfa2 ∧
    0 ≤ qr ∧ 0 ≤ Rr1 ∧ 0 ≤ Rr2 ∧ 0 ≤ Rrq ∧ 0 ≤ g1r1 ∧ 0 ≤ g1r2 ∧ 0 ≤ g1rq ∧
    0 ≤ g2r ∧ 0 ≤ c1r ∧ 0 ≤ c2r ∧ 0 ≤ smin
  /-- H_RISE_LE_FALL: rise arc ≤ fall arc on every arc: what makes the OR
  channel the rise-fast channel. (The pairs once quoted here as prjxray rise/fall,
  56/124, 55/152, 52/150, are FAST_MAX/SLOW_MAX of one arc, makesdf.py:63; prjxray
  gives no edge split, so the consistent instance is rise = fall, which satisfies
  this hypothesis. See `ArbCorners.RF` and `ArbCorners.prj_is_mix`.) -/
  H_RISE_LE_FALL : qr ≤ qf ∧ Rr1 ≤ Rf1 ∧ Rr2 ≤ Rf2 ∧ Rrq ≤ Rfq ∧ g1r1 ≤ g1f1 ∧
    g1r2 ≤ g1f2 ∧ g1rq ≤ g1fq ∧ g2r ≤ g2f ∧ c1r ≤ c1f ∧ c2r ≤ c2f
  /-- H_LOOP_POS: every feedback loop (ustate, ua1, ua2) has positive delay. -/
  H_LOOP_POS : 0 < qr + wfb ∧ 0 < c1r + wfa1 ∧ 0 < c2r + wfa2

/-- The traces of one `bd_arbiter` instance with its server. -/
structure Sigs where
  r1 : Sig
  r2 : Sig
  q : Sig
  R0 : Sig
  g1 : Sig
  g2 : Sig
  A0 : Sig
  A1 : Sig
  A2 : Sig

/-- H_SERVER: a four-phase server with minimum response `smin`. A0 changes at
`t` only if R0 carried the new value at some `u ≤ t - smin` and A0 had been in
its old phase continuously since `u`. -/
def Server (smin : Int) (R0 A0 : Sig) : Prop :=
  ∀ t, A0 t ≠ A0 (t - 1) →
    ∃ u, u + smin ≤ t ∧ R0 u = A0 t ∧ ∀ v, u ≤ v → v < t → A0 v = A0 (t - 1)

/-- The gate relations (rst = 0). -/
structure Run (D : Dl) (s : Sigs) : Prop where
  H_q : ∀ t, s.q t =
    (FS (s.r1 (t - D.wr1s - D.qr)) (s.r2 (t - D.wr2s - D.qr)) (s.q (t - D.wfb - D.qr))
        (s.A0 (t - D.wa0s - D.qr)) ||
     FS (s.r1 (t - D.wr1s - D.qf)) (s.r2 (t - D.wr2s - D.qf)) (s.q (t - D.wfb - D.qf))
        (s.A0 (t - D.wa0s - D.qf)))
  H_R0 : ∀ t, s.R0 t =
    (FR (s.r1 (t - D.wr1s - D.Rr1)) (s.r2 (t - D.wr2s - D.Rr2)) (s.q (t - D.wfb - D.Rrq)) ||
     FR (s.r1 (t - D.wr1s - D.Rf1)) (s.r2 (t - D.wr2s - D.Rf2)) (s.q (t - D.wfb - D.Rfq)))
  H_g1 : ∀ t, s.g1 t =
    (FG1 (s.r1 (t - D.wr1g - D.g1r1)) (s.r2 (t - D.wr2g - D.g1r2)) (s.q (t - D.wq - D.g1rq)) ||
     FG1 (s.r1 (t - D.wr1g - D.g1f1)) (s.r2 (t - D.wr2g - D.g1f2)) (s.q (t - D.wq - D.g1fq)))
  H_g2 : ∀ t, s.g2 t =
    (FG2 (s.r1 (t - D.wr1g - D.g2r)) (s.r2 (t - D.wr2g - D.g2r)) (s.q (t - D.wq - D.g2r)) ||
     FG2 (s.r1 (t - D.wr1g - D.g2f)) (s.r2 (t - D.wr2g - D.g2f)) (s.q (t - D.wq - D.g2f)))
  H_A1 : ∀ t, s.A1 t =
    (CE (s.g1 (t - D.wg1 - D.c1r)) (s.A0 (t - D.wa01 - D.c1r)) (s.A1 (t - D.wfa1 - D.c1r)) ||
     CE (s.g1 (t - D.wg1 - D.c1f)) (s.A0 (t - D.wa01 - D.c1f)) (s.A1 (t - D.wfa1 - D.c1f)))
  H_A2 : ∀ t, s.A2 t =
    (CE (s.g2 (t - D.wg2 - D.c2r)) (s.A0 (t - D.wa02 - D.c2r)) (s.A2 (t - D.wfa2 - D.c2r)) ||
     CE (s.g2 (t - D.wg2 - D.c2f)) (s.A0 (t - D.wa02 - D.c2f)) (s.A2 (t - D.wfa2 - D.c2f)))
  H_SRV : Server D.smin s.R0 s.A0

/-- The handover scenario: client 1 releases at `t0`, client 2 waits. The
server raised A0 for client 1 at `ta`, drops it at `TA`, re-raises it at `TA2`. -/
structure Scn (D : Dl) (s : Sigs) (t0 ta TA TA2 Hz : Int) : Prop where
  H_ORDER : ta ≤ t0 ∧ ta < TA ∧ t0 < TA ∧ TA < TA2 ∧ TA2 < Hz
  /-- client 1: high, drops at t0, stays low until the horizon. -/
  H_r1 : ∀ t, t < Hz → s.r1 t = decide (t < t0)
  /-- client 2: waiting throughout. -/
  H_r2 : ∀ t, t < Hz → s.r2 t = true
  /-- the server's phases on [ta, Hz). -/
  H_A0 : ∀ t, ta ≤ t → t < Hz → s.A0 t = (decide (t < TA) || decide (TA2 ≤ t))
  H_A0_prev : s.A0 (ta - 1) = false
  /-- settled initial state: q = 1, A1 = 1, A2 = 0 before t0. -/
  H_q_init : ∀ t, t < t0 → s.q t = true
  H_A1_init : ∀ t, t < t0 → s.A1 t = true
  H_A2_init : ∀ t, t < t0 → s.A2 t = false
  /-- H_SETTLED: A0's rise had reached ustate's and ua1's views before client 1
  dropped its request (the four-phase order A0↑ → A1↑ → r1↓ through gates). -/
  H_SETTLED : ta + D.wa0s + D.qf ≤ t0 ∧ ta + D.wa01 + D.c1f ≤ t0

/-! ## Strong induction over Int with a base region -/

theorem int_ind (P : Int → Prop) (a : Int) (hb : ∀ t, t < a → P t)
    (hs : ∀ t, a ≤ t → (∀ u, u < t → P u) → P t) : ∀ t, P t := by
  have key : ∀ n : Nat, ∀ t, t < a + n → P t := by
    intro n
    induction n with
    | zero => intro t ht; exact hb t (by omega)
    | succ n ih =>
      intro t ht
      by_cases h : t < a + n
      · exact ih t h
      · exact hs t (by omega) (fun u hu => ih u (by omega))
  intro t
  exact key (t - a + 1).toNat t (by omega)

theorem and_dec_false {p q : Prop} [Decidable p] [Decidable q] (h : ¬ (p ∧ q)) :
    (decide p && decide q) = false := by
  by_cases hp : p <;> by_cases hq : q <;> simp_all

/-! ## Derived instants -/

/-- R0's fall. -/
def TR (D : Dl) (t0 : Int) : Int := t0 + D.wr1s + D.Rf1
/-- q's fall (client 1 → client 2). -/
def QB (D : Dl) (TA : Int) : Int := TA + D.wa0s + D.qf
/-- g1's fall: through r1 (I0) or through q (I2), whichever is first. -/
def G1 (D : Dl) (t0 TA : Int) : Int := min (t0 + D.wr1g + D.g1f1) (QB D TA + D.wq + D.g1fq)
/-- g2's rise. -/
def G2 (D : Dl) (TA : Int) : Int := QB D TA + D.wq + D.g2r
/-- R0's re-rise (for client 2). -/
def RR (D : Dl) (TA : Int) : Int := QB D TA + D.wfb + D.Rrq

section
variable {D : Dl} {s : Sigs} {t0 ta TA TA2 Hz : Int}

theorem A0_val (S : Scn D s t0 ta TA TA2 Hz) (t : Int) (h1 : ta ≤ t) (h2 : t < Hz) :
    s.A0 t = (decide (t < TA) || decide (TA2 ≤ t)) := S.H_A0 t h1 h2

theorem A0_hi1 (S : Scn D s t0 ta TA TA2 Hz) (t : Int) (h1 : ta ≤ t) (h2 : t < TA) :
    s.A0 t = true := by
  have := S.H_ORDER
  rw [S.H_A0 t h1 (by omega)]; simp; omega

theorem A0_lo (S : Scn D s t0 ta TA TA2 Hz) (t : Int) (h1 : TA ≤ t) (h2 : t < TA2) :
    s.A0 t = false := by
  have := S.H_ORDER
  rw [S.H_A0 t (by omega) (by omega)]; simp; omega

theorem A0_hi2 (S : Scn D s t0 ta TA TA2 Hz) (t : Int) (h1 : TA2 ≤ t) (h2 : t < Hz) :
    s.A0 t = true := by
  have := S.H_ORDER
  rw [S.H_A0 t (by omega) h2]; simp; omega

theorem r1_lo (S : Scn D s t0 ta TA TA2 Hz) (t : Int) (h1 : t0 ≤ t) (h2 : t < Hz) :
    s.r1 t = false := by
  rw [S.H_r1 t h2]; simp; omega

theorem r1_hi (S : Scn D s t0 ta TA TA2 Hz) (t : Int) (h1 : t < t0) :
    s.r1 t = true := by
  have := S.H_ORDER
  rw [S.H_r1 t (by omega)]; simp; omega

/-- R0 stays high until `TR`: with r2 high, R0 = r1 + ~q, so it needs only r1. -/
theorem R0_hi (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz) (t : Int) (h : t < TR D t0)
    (hz : t < Hz) : s.R0 t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL
  unfold TR at h
  rw [R.H_R0 t, r1_hi S (t - D.wr1s - D.Rf1) (by omega), S.H_r2 (t - D.wr2s - D.Rf2) (by omega),
    FR_r1r2]
  simp

/-- **The server cannot drop A0 before `TR + smin`.** -/
theorem TA_ge (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz) : TR D t0 + D.smin ≤ TA := by
  have ho := S.H_ORDER
  have := D.H_NONNEG
  have e1 : s.A0 TA = false := A0_lo S TA (by omega) (by omega)
  have e0 : s.A0 (TA - 1) = true := A0_hi1 S _ (by omega) (by omega)
  obtain ⟨u, hu, hR, hv⟩ := R.H_SRV TA (by rw [e1, e0]; simp)
  rw [e1] at hR
  have hu1 : ta ≤ u := by
    by_cases hc : ta ≤ u
    · exact hc
    · have := hv (ta - 1) (by omega) (by omega)
      rw [S.H_A0_prev, e0] at this; exact absurd this (by simp)
  by_cases hc : TR D t0 + D.smin ≤ TA
  · exact hc
  · have := R0_hi R S u (by omega) (by omega)
    rw [hR] at this; exact absurd this (by simp)

/-- q is high until `QB` (held by A0 while the server is in client 1's phase). -/
theorem q_hi (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz) :
    ∀ t, t < QB D TA → s.q t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.H_SETTLED; have := S.H_ORDER
  refine int_ind (fun t => t < QB D TA → s.q t = true) t0
    (fun t ht _ => S.H_q_init t ht) ?_
  intro t ht ih hb
  unfold QB at hb
  rw [R.H_q t, A0_hi1 S (t - D.wa0s - D.qf) (by omega) (by omega), FS_hold,
    ih (t - D.wfb - D.qf) (by omega) (by unfold QB; omega)]
  simp

/-- R0 is low on `[TR, RR)`. -/
theorem R0_lo (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz) (t : Int)
    (h1 : TR D t0 ≤ t) (h2 : t < RR D TA) (hz : t < Hz) : s.R0 t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL
  unfold TR at h1; unfold RR at h2
  rw [R.H_R0 t, r1_lo S (t - D.wr1s - D.Rr1) (by omega) (by omega),
    r1_lo S (t - D.wr1s - D.Rf1) (by omega) (by omega),
    q_hi R S _ (by omega), q_hi R S (t - D.wfb - D.Rfq) (by omega), FR_lo, FR_lo]
  simp

/-- **The server cannot re-raise A0 before `RR + smin`.** -/
theorem TA2_ge (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz) : RR D TA + D.smin ≤ TA2 := by
  have ho := S.H_ORDER
  have := D.H_NONNEG
  have hTA := TA_ge R S
  have e1 : s.A0 TA2 = true := A0_hi2 S TA2 (by omega) (by omega)
  have e0 : s.A0 (TA2 - 1) = false := A0_lo S _ (by omega) (by omega)
  obtain ⟨u, hu, hR, hv⟩ := R.H_SRV TA2 (by rw [e1, e0]; simp)
  rw [e1] at hR
  have hu1 : TA ≤ u := by
    by_cases hc : TA ≤ u
    · exact hc
    · have := hv (TA - 1) (by omega) (by omega)
      rw [A0_hi1 S (TA - 1) (by omega) (by omega), e0] at this; exact absurd this (by simp)
  by_cases hc : RR D TA + D.smin ≤ TA2
  · exact hc
  · unfold TR at hTA
    have := R0_lo R S u (by unfold TR; omega) (by omega) (by omega)
    rw [hR] at this; exact absurd this (by simp)

/-- q is low from `QB` to the horizon (reset by the released hold, then held
again at 0 when A0 re-rises). -/
theorem q_lo (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz) :
    ∀ t, QB D TA ≤ t → t < Hz → s.q t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.H_ORDER
  have hTA := TA_ge R S
  have hTA2 := TA2_ge R S
  unfold TR at hTA; unfold RR QB at hTA2
  refine int_ind (fun t => QB D TA ≤ t → t < Hz → s.q t = false) (QB D TA)
    (fun t ht h _ => absurd h (by omega)) ?_
  intro t _ ih hb hz
  unfold QB at hb
  -- one view at a time
  have view : ∀ d, D.qr ≤ d → d ≤ D.qf →
      FS (s.r1 (t - D.wr1s - d)) (s.r2 (t - D.wr2s - d)) (s.q (t - D.wfb - d))
        (s.A0 (t - D.wa0s - d)) = false := by
    intro d hd1 hd2
    rw [r1_lo S _ (by omega) (by omega), S.H_r2 _ (by omega)]
    by_cases hc : t - D.wa0s - d < TA2
    · rw [A0_lo S _ (by omega) hc, FS_rel]
    · rw [A0_hi2 S _ (by omega) (by omega), FS_hold]
      exact ih _ (by omega) (by unfold QB; omega) (by omega)
  rw [R.H_q t, view D.qr (by omega) (by omega), view D.qf (by omega) (by omega)]
  rfl

/-- The exact q trace below the horizon. -/
theorem q_eq (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz) (t : Int) (hz : t < Hz) :
    s.q t = decide (t < QB D TA) := by
  by_cases h : t < QB D TA
  · rw [q_hi R S t h]; simp [h]
  · rw [q_lo R S t (by omega) hz]; simp [h]

/-- **g2's exact trace**: it rises at `G2 = QB + wq + g2r`. -/
theorem g2_eq (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz) (t : Int) (hz : t < Hz) :
    s.g2 t = decide (G2 D TA ≤ t) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL
  rw [R.H_g2 t, FG2_eq, FG2_eq, S.H_r2 _ (by omega), S.H_r2 _ (by omega),
    q_eq R S _ (by omega), q_eq R S (t - D.wq - D.g2f) (by omega)]
  unfold G2
  by_cases h : QB D TA + D.wq + D.g2r ≤ t
  · have : ¬ (t - D.wq - D.g2r < QB D TA) := by omega
    simp [h, this]
  · have e1 : t - D.wq - D.g2r < QB D TA := by omega
    have e2 : t - D.wq - D.g2f < QB D TA := by omega
    simp [h, e1, e2]

/-- **g1's exact trace**: it falls at `G1 = min (t0 + wr1g + g1f1) (QB + wq + g1fq)`. -/
theorem g1_eq (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz) (t : Int) (hz : t < Hz) :
    s.g1 t = decide (t < G1 D t0 TA) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL
  rw [R.H_g1 t, FG1_eq, FG1_eq, S.H_r1 _ (by omega), S.H_r1 (t - D.wr1g - D.g1f1) (by omega),
    q_eq R S _ (by omega), q_eq R S (t - D.wq - D.g1fq) (by omega)]
  unfold G1
  by_cases h : t < min (t0 + D.wr1g + D.g1f1) (QB D TA + D.wq + D.g1fq)
  · have e1 : t - D.wr1g - D.g1f1 < t0 := by omega
    have e2 : t - D.wq - D.g1fq < QB D TA := by omega
    simp [h, e1, e2]
  · rw [and_dec_false (by omega), and_dec_false (by omega)]
    simp [h]

/-! ## RT1: grant exclusion across the handover -/

/-- **Exact overlap**: both grants high at `t` iff `G2 ≤ t < G1`. -/
theorem overlap_exact (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz) (t : Int) (hz : t < Hz) :
    (s.g1 t && s.g2 t) = true ↔ (G2 D TA ≤ t ∧ t < G1 D t0 TA) := by
  rw [g1_eq R S t hz, g2_eq R S t hz]
  simp; omega

/-- **RT1 (arc form) ⇒ grant exclusion, for every server.**
RT1: g1's fall through r1 (`wr1g + g1f1`) beats the chain r1↓ → R0↓ (`wr1s + Rf1`)
→ server (`smin`) → A0↓ at ustate (`wa0s`) → q↓ (`qf`) → q at ugrant (`wq`) →
g2↑ (`g2r`). Alternative structural disjunct: g1's fall through q (`g1fq`)
is no slower than g2's rise (`g2r`). -/
def RT1 (D : Dl) : Prop :=
  D.wr1g + D.g1f1 ≤ D.wr1s + D.Rf1 + D.smin + D.wa0s + D.qf + D.wq + D.g2r ∨ D.g1fq ≤ D.g2r

theorem rt1_exclusion (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz) (H_RT1 : RT1 D) :
    ∀ t, t < Hz → (s.g1 t && s.g2 t) = false := by
  have hTA := TA_ge R S
  intro t hz
  cases hc : (s.g1 t && s.g2 t)
  · rfl
  · have := (overlap_exact R S t hz).1 hc
    unfold G1 G2 QB at this; unfold TR at hTA; unfold RT1 at H_RT1
    omega

/-- **RT1 counter-trace.** If both disjuncts of RT1 fail for the actual server
response `TA`, both grants are high at the instant g2 rises. With a server
responding in exactly `smin` (`TA = TR + smin`) this is exactly `¬ RT1`. -/
theorem rt1_counter (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz)
    (H_r1slow : G2 D TA < t0 + D.wr1g + D.g1f1) (H_qslow : D.g2r < D.g1fq)
    (hz : G2 D TA < Hz) :
    s.g1 (G2 D TA) = true ∧ s.g2 (G2 D TA) = true := by
  have := (overlap_exact R S (G2 D TA) hz).2 ⟨Int.le_refl _, by unfold G1 G2 at *; omega⟩
  simpa using this

theorem rt1_counter_minserver (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz)
    (H_fast : TA = TR D t0 + D.smin) (H_not : ¬ RT1 D) (hz : G2 D TA < Hz) :
    s.g1 (G2 D TA) = true ∧ s.g2 (G2 D TA) = true := by
  unfold RT1 at H_not
  apply rt1_counter R S _ (by omega) hz
  unfold G2 QB; unfold TR at H_fast; omega

/-! ## RT2: ack exclusion across the handover -/

/-- A1's fall instant (both g1 and A0 low in its fall view). -/
def T1 (D : Dl) (t0 TA : Int) : Int := max (G1 D t0 TA + D.wg1) (TA + D.wa01) + D.c1f
/-- A2's earliest rise. -/
def T2 (D : Dl) (TA2 : Int) : Int := TA2 + D.wa02 + D.c2r

/-- **A1 falls and stays low** after `T1`, provided its fall has re-reached its
own pin before A0's re-rise reaches ua1 (RT2a). -/
theorem A1_low_after (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz)
    (H_RT2a : T1 D t0 TA + D.wfa1 ≤ TA2 + D.wa01) :
    ∀ t, T1 D t0 TA ≤ t → t < Hz → s.A1 t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.H_ORDER
  refine int_ind (fun t => T1 D t0 TA ≤ t → t < Hz → s.A1 t = false) (T1 D t0 TA)
    (fun t ht h _ => absurd h (by omega)) ?_
  intro t _ ih hb hz
  unfold T1 at hb H_RT2a
  have view : ∀ d, D.c1r ≤ d → d ≤ D.c1f →
      CE (s.g1 (t - D.wg1 - d)) (s.A0 (t - D.wa01 - d)) (s.A1 (t - D.wfa1 - d)) = false := by
    intro d hd1 hd2
    rw [g1_eq R S _ (by omega), CE_eq]
    have : ¬ (t - D.wg1 - d < G1 D t0 TA) := by omega
    simp only [this, decide_false, Bool.false_and, Bool.false_or]
    by_cases hc : t - D.wa01 - d < TA2
    · rw [A0_lo S _ (by omega) hc]; simp
    · rw [ih _ (by omega) (by unfold T1; omega) (by omega)]; simp
  rw [R.H_A1 t, view D.c1r (by omega) (by omega), view D.c1f (by omega) (by omega)]
  rfl

/-- **A2 stays low until `T2`**, given the A0 fork condition of probe 7g
(`ArbA0Fork`, H_A0_FORK): A0's fall reaches ua2 no later than g2's rise does. -/
theorem A2_low_before (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz)
    (H_A0_FORK : TA + D.wa02 ≤ G2 D TA + D.wg2) :
    ∀ t, t < T2 D TA2 → t < Hz → s.A2 t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.H_ORDER
  refine int_ind (fun t => t < T2 D TA2 → t < Hz → s.A2 t = false) t0
    (fun t ht _ _ => S.H_A2_init t ht) ?_
  intro t _ ih hb hz
  unfold T2 at hb
  have view : ∀ d, D.c2r ≤ d → d ≤ D.c2f →
      CE (s.g2 (t - D.wg2 - d)) (s.A0 (t - D.wa02 - d)) (s.A2 (t - D.wfa2 - d)) = false := by
    intro d hd1 hd2
    rw [ih _ (by omega) (by unfold T2; omega) (by omega), CE_eq, g2_eq R S _ (by omega)]
    by_cases hc : t - D.wa02 - d < TA
    · have : ¬ (G2 D TA ≤ t - D.wg2 - d) := by omega
      simp [this]
    · rw [A0_lo S _ (by omega) (by omega)]; simp
  rw [R.H_A2 t, view D.c2r (by omega) (by omega), view D.c2f (by omega) (by omega)]
  rfl

/-- **Ack exclusion, run form.** RT2a (A1's fall completes before A0's re-rise
reaches ua1), RT2b (A1 falls before A2 can rise) and H_A0_FORK (7g). -/
theorem rt2_exclusion (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz)
    (H_RT2a : T1 D t0 TA + D.wfa1 ≤ TA2 + D.wa01)
    (H_RT2b : T1 D t0 TA ≤ T2 D TA2)
    (H_A0_FORK : TA + D.wa02 ≤ G2 D TA + D.wg2) :
    ∀ t, t < Hz → (s.A1 t && s.A2 t) = false := by
  intro t hz
  by_cases h : T1 D t0 TA ≤ t
  · rw [A1_low_after R S H_RT2a t h hz]; rfl
  · rw [A2_low_before R S H_A0_FORK t (by omega) hz]; simp

/-- RT2 in arc terms (sufficient for every server, worst case `TA`, `TA2` minimal):
* `pulse`: A0's low pulse at ua1 outlasts ua1's fall loop;
* `g1`: g1's fall reaches ua1 and its loop closes before A0 re-rises there;
* `forkA`, `forkG`: A1's fall precedes A2's earliest rise (A0 fork skew ua1/ua2). -/
structure RT2 (D : Dl) : Prop where
  pulse : D.c1f + D.wfa1 ≤ D.wa0s + D.qf + D.wfb + D.Rrq + D.smin
  g1 : D.wr1g + D.g1f1 + D.wg1 + D.c1f + D.wfa1 ≤
    D.wr1s + D.Rf1 + 2 * D.smin + D.wa0s + D.qf + D.wfb + D.Rrq + D.wa01
  forkA : D.wa01 + D.c1f ≤ D.wa0s + D.qf + D.wfb + D.Rrq + D.smin + D.wa02 + D.c2r
  forkG : D.wr1g + D.g1f1 + D.wg1 + D.c1f ≤
    D.wr1s + D.Rf1 + 2 * D.smin + D.wa0s + D.qf + D.wfb + D.Rrq + D.wa02 + D.c2r

/-- H_A0_FORK of 7g in arc terms (client 2's side): A0 to ua2 no slower than
A0 → ustate → q → ugrant → g2 → ua2. -/
def A0Fork (D : Dl) : Prop := D.wa02 ≤ D.wa0s + D.qf + D.wq + D.g2r + D.wg2

/-- **Ack exclusion, arc form, for every server satisfying H_SERVER_MIN.** -/
theorem rt2_exclusion_arcs (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz)
    (H_RT2 : RT2 D) (H_fork : A0Fork D) :
    ∀ t, t < Hz → (s.A1 t && s.A2 t) = false := by
  have := D.H_NONNEG
  have hTA := TA_ge R S
  have hTA2 := TA2_ge R S
  obtain ⟨h1, h2, h3, h4⟩ := H_RT2
  unfold TR at hTA; unfold RR QB at hTA2; unfold A0Fork at H_fork
  apply rt2_exclusion R S
  · unfold T1 G1 QB; omega
  · unfold T1 T2 G1 QB; omega
  · unfold G2 QB; omega

/-- **RT2 counter-trace, part 1: A1's fall is swallowed.** If A0's re-rise
reaches ua1 before g1's fall does, or A0's low pulse at ua1 is no longer than
ua1's fall-minus-rise arc, A1 never falls before the horizon. -/
theorem A1_stuck (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz)
    (H_CT2 : TA2 + D.wa01 ≤ max (G1 D t0 TA + D.wg1) (TA + D.wa01 + D.c1f - D.c1r)) :
    ∀ t, t < Hz → s.A1 t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.H_ORDER; have := S.H_SETTLED
  refine int_ind (fun t => t < Hz → s.A1 t = true) t0 (fun t ht _ => S.H_A1_init t ht) ?_
  intro t ht ih hz
  rw [R.H_A1 t, CE_eq, CE_eq, ih (t - D.wfa1 - D.c1f) (by omega) (by omega),
    ih (t - D.wfa1 - D.c1r) (by omega) (by omega)]
  simp only [Bool.and_true, Bool.or_eq_true]
  by_cases hg : t - D.wg1 - D.c1f < G1 D t0 TA
  · right; rw [g1_eq R S _ (by omega)]; simp [hg]
  · by_cases hA : t - D.wa01 - D.c1f < TA
    · right; rw [A0_hi1 S _ (by omega) hA]; simp
    · by_cases hB : TA2 ≤ t - D.wa01 - D.c1f
      · right; rw [A0_hi2 S _ hB (by omega)]; simp
      · left; rw [A0_hi2 S _ (by omega) (by omega)]; simp

/-- **RT2 counter-trace, part 2: both clients acknowledged.** Under `A1_stuck`'s
condition, and with g2 already at ua2 when A0 re-rises there, A1 and A2 are
both high at `T2`. -/
theorem rt2_counter (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz)
    (H_CT2 : TA2 + D.wa01 ≤ max (G1 D t0 TA + D.wg1) (TA + D.wa01 + D.c1f - D.c1r))
    (H_g2_there : G2 D TA + D.wg2 ≤ TA2 + D.wa02) (hz : T2 D TA2 < Hz) :
    s.A1 (T2 D TA2) = true ∧ s.A2 (T2 D TA2) = true := by
  have := D.H_NONNEG; have := S.H_ORDER
  refine ⟨A1_stuck R S H_CT2 _ hz, ?_⟩
  unfold T2 at *
  rw [R.H_A2, CE_eq]
  have e1 : TA2 + D.wa02 + D.c2r - D.wg2 - D.c2r = TA2 + D.wa02 - D.wg2 := by omega
  have e2 : TA2 + D.wa02 + D.c2r - D.wa02 - D.c2r = TA2 := by omega
  rw [e1, e2, g2_eq R S _ (by omega), A0_hi2 S TA2 (by omega) (by omega)]
  have : G2 D TA ≤ TA2 + D.wa02 - D.wg2 := by omega
  simp [this]

end

/-! ## The prjxray arcs -/

/-- The arcs of cells/sim/bd_prims_sim.v: O6 56/124 flat; O5 per pin
I0 55/152, I1 55/152, I2 52/150; routes and smin free. These were read as
rise/fall, but each pair is prjxray's FAST_MAX/SLOW_MAX of one arc
(makesdf.py:63), so this instance mixes corners (`ArbCorners.prj_is_mix`).
Consistent-corner replacements: `ArbCorners.Dslow`/`Dfast` via `ArbCorners.cDl`. -/
def prj (wr1s wr2s wr1g wr2g wfb wa0s wq wg1 wa01 wfa1 wg2 wa02 wfa2 smin : Int)
    (h : 0 ≤ wr1s ∧ 0 ≤ wr2s ∧ 0 ≤ wr1g ∧ 0 ≤ wr2g ∧ 0 ≤ wfb ∧ 0 ≤ wa0s ∧
      0 ≤ wq ∧ 0 ≤ wg1 ∧ 0 ≤ wa01 ∧ 0 ≤ wfa1 ∧ 0 ≤ wg2 ∧ 0 ≤ wa02 ∧ 0 ≤ wfa2 ∧ 0 ≤ smin) :
    Dl where
  wr1s := wr1s
  wr2s := wr2s
  wr1g := wr1g
  wr2g := wr2g
  wfb := wfb
  wa0s := wa0s
  wq := wq
  wg1 := wg1
  wa01 := wa01
  wfa1 := wfa1
  wg2 := wg2
  wa02 := wa02
  wfa2 := wfa2
  qr := 56
  qf := 124
  Rr1 := 55
  Rf1 := 152
  Rr2 := 55
  Rf2 := 152
  Rrq := 52
  Rfq := 150
  g1r1 := 55
  g1f1 := 152
  g1r2 := 55
  g1f2 := 152
  g1rq := 52
  g1fq := 150
  g2r := 56
  g2f := 124
  c1r := 56
  c1f := 124
  c2r := 56
  c2f := 124
  smin := smin
  H_NONNEG := by omega
  H_RISE_LE_FALL := by omega
  H_LOOP_POS := by omega

/-- **RT1 with the `prj` (corner-mixed) arcs**: holds whenever r1's route to
ugrant is at most `180 + smin + wa0s + wq` ps longer than its route to ustate
(180 = qf + g2r, the R0/g1 fall arcs from I0 being equal, 152). The 180 mixes
corners (FAST_MAX rise + SLOW_MAX "fall", makesdf.py:63); at a consistent corner
the arc part is 248 ps (SLOW_MAX) / 90 ps (FAST_MIN): `ArbCorners.arcs_slowMax`,
`ArbCorners.arcs_fastMin`. -/
theorem prj_RT1 (wr1s wr2s wr1g wr2g wfb wa0s wq wg1 wa01 wfa1 wg2 wa02 wfa2 smin : Int) (h)
    (H : wr1g ≤ wr1s + 180 + smin + wa0s + wq) :
    RT1 (prj wr1s wr2s wr1g wr2g wfb wa0s wq wg1 wa01 wfa1 wg2 wa02 wfa2 smin h) := by
  unfold RT1 prj; simp only; omega

/-- **RT2 with the `prj` (corner-mixed) arcs**: the four conditions reduce to
* pulse: `wfa1 ≤ smin + 52 + wa0s + wfb`
* g1:    `wr1g + wg1 + wfa1 ≤ wr1s + 2 smin + 52 + wa0s + wfb + wa01`
* forkA: `wa01 ≤ smin + 108 + wa0s + wfb + wa02`
* forkG: `wr1g + wg1 ≤ wr1s + 2 smin + 108 + wa0s + wfb + wa02`.

The 52/108 arc parts mix FAST_MAX and SLOW_MAX of one arc (makesdf.py:63). At a
consistent corner they are 150/274 ps (SLOW_MAX) and 42/87 ps (FAST_MIN):
`ArbCorners.arcs_slowMax`, `ArbCorners.arcs_fastMin`. -/
theorem prj_RT2 (wr1s wr2s wr1g wr2g wfb wa0s wq wg1 wa01 wfa1 wg2 wa02 wfa2 smin : Int) (h)
    (Hp : wfa1 ≤ smin + 52 + wa0s + wfb)
    (Hg : wr1g + wg1 + wfa1 ≤ wr1s + 2 * smin + 52 + wa0s + wfb + wa01)
    (Ha : wa01 ≤ smin + 108 + wa0s + wfb + wa02)
    (HG : wr1g + wg1 ≤ wr1s + 2 * smin + 108 + wa0s + wfb + wa02) :
    RT2 (prj wr1s wr2s wr1g wr2g wfb wa0s wq wg1 wa01 wfa1 wg2 wa02 wfa2 smin h) := by
  constructor <;> (unfold prj; simp only; omega)

/-- **Arc-only, corner-mixed** (every route 0, server 112 ps = 2 × FAST_MAX):
RT1, RT2 and the 7g fork condition all hold. Margins: RT1 180 + 112 = 292 ps;
RT2 pulse 164, g1 276, forkA 220, forkG 332 ps. These numbers are artefacts of
reading prjxray's FAST_MAX/SLOW_MAX (makesdf.py:63) as rise/fall. Corrected:
`ArbCorners.slow_arc_only` (server 248: RT1 496, pulse 398, g1 646, forkA 522,
forkG 770) and `ArbCorners.fast_arc_only` (server 90: 180, 132, 222, 177, 267). -/
theorem prj_arc_only :
    let D := prj 0 0 0 0 0 0 0 0 0 0 0 0 0 112 (by omega)
    RT1 D ∧ RT2 D ∧ A0Fork D := by
  refine ⟨?_, ?_, ?_⟩
  · exact prj_RT1 0 0 0 0 0 0 0 0 0 0 0 0 0 112 _ (by omega)
  · exact prj_RT2 0 0 0 0 0 0 0 0 0 0 0 0 0 112 _ (by omega) (by omega) (by omega) (by omega)
  · unfold A0Fork prj; simp only; omega

end Formal.Cells.ArbHeldTimed
