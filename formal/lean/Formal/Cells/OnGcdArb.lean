import Formal.Cells.ArbHeldTimed2
import Formal.Timing.RuntAckInst

/-!
# Probe Bag: the held arbiter's RT1 / RT1b on the 36 routed gcd_hw arbiters

Shard B, 2026-10-27. Core Lean (no Mathlib). Note: `formal/notes/B-gcd-arb.md`.

## What is instantiated

7h's `ArbHeldTimed.rt1_exclusion` (client 1 releases, client 2 waiting: g1 and g2
are never high together) and 7j's `ArbHeldTimed2.rt1_exclusion2` (the mirror), on
every `bd_arbiter` of the four routed gcd_hw seeds that shard C's probes 10e/10i/10j
used (seeds 2, 3, 4, d; nine arbiters per route: `ucontrol_merge{2,3,4,6,9,10,11,12}
.uarb1` and `ucontrol_merge12.uarb2`), at each of the four consistent prjxray
corners FMIN, FMAX, SMIN, SMAX.

The routed numbers are NOT copied: each `Q` below is built from shard C's committed,
generated rows `Formal.Timing.RuntAck.Inst.<seed>_<inst>_<corner>_c<k>` (C-10j,
`formal/tools/runtack/extract.py`: prjxray at one consistent corner column, physical
pins from the bits/X_ORIG_PORT, site pins and per-pin LUT arcs included, the shared
prefix of each net split off exactly from the RC tree; UNTRUSTED extraction).
The fields used, client k:
* `drg k`  r_k net suffix (after the r_k split) to ugrant's r_k pin (route + site pin);
* `drs k`  r_k net suffix to ustate$LUT5's pin (R0 half) (`dqs5`/`drs5` in C's row);
* `agr k`  ugrant arc r_k pin -> g_k's output (O5 for k = 1, O6 for k = 2);
* `aRr k`  ustate arc r_k pin -> O5 (R0);
* `agq k`  ugrant arc q pin -> g_k's output;
* `dqg`    q net suffix (after the q split) to ugrant's q pin.

## The condition, and why it needs no server, A0 or q-prefix number

RT1 (7h) is `wr1g + g1f1 ≤ wr1s + Rf1 + smin + wa0s + qf + wq + g2r ∨ g1fq ≤ g2r`:
g1's fall through r1 must not come after g2's rise through r1 → R0 → server → A0 →
q → ugrant. With the r1 net's shared prefix `cr` (H_R_SHARED: one wire, one delay,
in both sums) and the q net's prefix `cq ≥ 0`, every term the extraction lacks
(`smin`, `wa0s`, `qf`, `cq`) is on the safe side and non-negative (H_NONNEG,
H_RISE_LE_FALL). So `m1 := drs1 + aRr1 + dqg + agq2 - (drg1 + agr1) ≥ 0` is a
sufficient condition for RT1 for EVERY server (`rt1_of`). Mirror: `m2` for RT1b.

## Named hypotheses
* H_ONE_CORNER: all the arbiter's delays at one prjxray column (C's row).
* H_R_SHARED (`cr`), H_Q_PREFIX (`cq ≥ 0`): the parts of the r_k and q nets before
  their branch points are one wire each (as C-10i's H_SHARED_PREFIX).
* 7h/7j's model: `Run` (real INITs, per-pin routes, per-output rise/fall arcs, O5
  arcs per pin), `Scn`/`Scn2` (the handover), `Server` with any `smin ≥ 0`.
* H_FLAT_O6: 7h's `Dl` has one O6 arc per LUT for all pins. On these rows the
  ugrant O6 arc from the q pin equals the one from the r2 pin at every corner
  (checked: max difference 0 ps), so the instance loses nothing there; ustate's
  O6 arc (`qr`/`qf`) is only bounded below by 0.

## NOT covered
* The A0 fork (H_A0_FORK / rule J'), RT2 / RT2b (ack exclusion): they need the A0
  branches into ustate and ua_k, which C's committed rows do not carry, and the
  routed artefacts (FASM, routed JSON, SDF of these four routes) are not on disk.
* Within-die independence: see `box_*` below (arithmetic in Lean: exact need).
-/

namespace Formal.Cells.OnGcdArb

open Formal.Cells.ArbHeldTimed
open Formal.Cells.ArbHeldTimed2

/-- The routed quantities of one arbiter at one corner (ps). -/
structure Q where
  dqg : Int
  drg1 : Int
  drs1 : Int
  agr1 : Int
  aRr1 : Int
  agq1 : Int
  drg2 : Int
  drs2 : Int
  agr2 : Int
  aRr2 : Int
  agq2 : Int
deriving Repr

/-- Build `Q` from C-10j's two client rows (client 1, client 2). -/
def ofRows (c1 c2 : Formal.Timing.RuntAck.Row) : Q :=
  { dqg := c1.dqg, drg1 := c1.drg, drs1 := c1.drs5, agr1 := c1.agr, aRr1 := c1.aRr,
    agq1 := c1.agq, drg2 := c2.drg, drs2 := c2.drs5, agr2 := c2.agr, aRr2 := c2.aRr,
    agq2 := c2.agq }

/-- C's two rows agree on the shared q suffix (a consistency check of the data). -/
def rowsAgree (c1 c2 : Formal.Timing.RuntAck.Row) : Bool := c1.dqg == c2.dqg

/-- every field is non-negative -/
def Q.nn (x : Q) : Bool :=
  decide (0 ≤ x.dqg ∧ 0 ≤ x.drg1 ∧ 0 ≤ x.drs1 ∧ 0 ≤ x.agr1 ∧ 0 ≤ x.aRr1 ∧ 0 ≤ x.agq1 ∧
    0 ≤ x.drg2 ∧ 0 ≤ x.drs2 ∧ 0 ≤ x.agr2 ∧ 0 ≤ x.aRr2 ∧ 0 ≤ x.agq2)

/-- RT1's server-free margin (client 1 releases). -/
def Q.m1 (x : Q) : Int := x.drs1 + x.aRr1 + x.dqg + x.agq2 - (x.drg1 + x.agr1)
/-- RT1b's server-free margin (client 2 releases). -/
def Q.m2 (x : Q) : Int := x.drs2 + x.aRr2 + x.dqg + x.agq1 - (x.drg2 + x.agr2)

/-- H_INST1: the 7h delay record `D` realises `x` for the client-1 release, with the
r1 prefix `cr` and the q prefix `cq`. -/
def Real1 (x : Q) (cr cq : Int) (D : Dl) : Prop :=
  0 ≤ cq ∧ D.wr1g = cr + x.drg1 ∧ D.wr1s = cr + x.drs1 ∧ D.g1f1 = x.agr1 ∧
    D.Rf1 = x.aRr1 ∧ D.wq = cq + x.dqg ∧ D.g2r = x.agq2 ∧ D.g1fq = x.agq1

/-- H_INST2: the same for the client-2 release (7j). -/
def Real2 (x : Q) (cr cq : Int) (D : Dl) : Prop :=
  0 ≤ cq ∧ D.wr2g = cr + x.drg2 ∧ D.wr2s = cr + x.drs2 ∧ D.g2f = x.agr2 ∧
    D.Rf2 = x.aRr2 ∧ D.wq = cq + x.dqg ∧ D.g1rq = x.agq1

/-- **RT1 from the routed numbers, for every server.** Exact accounting:
RT1's first disjunct is `0 ≤ m1 + (smin + wa0s + qf + cq)`. -/
theorem rt1_iff (x : Q) (cr cq : Int) (D : Dl) (h : Real1 x cr cq D) :
    RT1 D ↔ (0 ≤ x.m1 + (D.smin + D.wa0s + D.qf + cq) ∨ x.agq1 ≤ x.agq2) := by
  obtain ⟨_, h1, h2, h3, h4, h5, h6, h7⟩ := h
  unfold RT1 Q.m1; rw [h1, h2, h3, h4, h5, h6, h7]; omega

theorem rt1b_iff (x : Q) (cr cq : Int) (D : Dl) (h : Real2 x cr cq D) :
    RT1b D ↔ (0 ≤ x.m2 + (D.smin + D.wa0s + D.qr + cq) ∨ x.agr2 ≤ x.agq1) := by
  obtain ⟨_, h1, h2, h3, h4, h5, h6⟩ := h
  unfold RT1b Q.m2; rw [h1, h2, h3, h4, h5, h6]; omega

theorem rt1_of (x : Q) (cr cq : Int) (D : Dl) (h : Real1 x cr cq D) (hm : 0 ≤ x.m1) :
    RT1 D := by
  have hn := D.H_NONNEG; have hr := D.H_RISE_LE_FALL; have hc := h.1
  exact (rt1_iff x cr cq D h).2 (Or.inl (by omega))

theorem rt1b_of (x : Q) (cr cq : Int) (D : Dl) (h : Real2 x cr cq D) (hm : 0 ≤ x.m2) :
    RT1b D := by
  have hn := D.H_NONNEG; have hc := h.1
  exact (rt1b_iff x cr cq D h).2 (Or.inl (by omega))

/-- **Grant exclusion across a client-1 release** (7h `rt1_exclusion`), for every
server, every A0 branch and every q prefix, once `m1 ≥ 0`. -/
theorem excl1 (x : Q) (hm : 0 ≤ x.m1) {D : Dl} {s : Sigs} {t0 ta TA TA2 Hz cr cq : Int}
    (h : Real1 x cr cq D) (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz) :
    ∀ t, t < Hz → (s.g1 t && s.g2 t) = false :=
  rt1_exclusion R S (rt1_of x cr cq D h hm)

/-- **Grant exclusion across a client-2 release** (7j `rt1_exclusion2`). -/
theorem excl2 (x : Q) (hm : 0 ≤ x.m2) {D : Dl} {s : Sigs} {t0 ta TA TA2 Hz cr cq : Int}
    (h : Real2 x cr cq D) (R : Run D s) (S : Scn2 D s t0 ta TA TA2 Hz) :
    ∀ t, t < Hz → (s.g1 t && s.g2 t) = false :=
  rt1_exclusion2 R S (rt1b_of x cr cq D h hm)

/-! ## Non-vacuity of H_INST: a valid 7h record realises every row -/

/-- A record realising `x` (client-1 release), zero prefixes, server `sm`. -/
def mk1 (x : Q) (sm : Int) (hx : x.nn = true) (hs : 0 ≤ sm) : Dl where
  wr1s := x.drs1
  wr2s := x.drs2
  wr1g := x.drg1
  wr2g := x.drg2
  wfb := 1
  wa0s := 0
  wq := x.dqg
  wg1 := 0
  wa01 := 0
  wfa1 := 1
  wg2 := 0
  wa02 := 0
  wfa2 := 1
  qr := 0
  qf := 0
  Rr1 := x.aRr1
  Rf1 := x.aRr1
  Rr2 := x.aRr2
  Rf2 := x.aRr2
  Rrq := 0
  Rfq := 0
  g1r1 := x.agr1
  g1f1 := x.agr1
  g1r2 := 0
  g1f2 := 0
  g1rq := x.agq1
  g1fq := x.agq1
  g2r := x.agq2
  g2f := x.agq2
  c1r := 0
  c1f := 0
  c2r := 0
  c2f := 0
  smin := sm
  H_NONNEG := by unfold Q.nn at hx; simp only [decide_eq_true_eq] at hx; omega
  H_RISE_LE_FALL := by omega
  H_LOOP_POS := by omega

/-- The same for the client-2 release. -/
def mk2 (x : Q) (sm : Int) (hx : x.nn = true) (hs : 0 ≤ sm) : Dl where
  wr1s := x.drs1
  wr2s := x.drs2
  wr1g := x.drg1
  wr2g := x.drg2
  wfb := 1
  wa0s := 0
  wq := x.dqg
  wg1 := 0
  wa01 := 0
  wfa1 := 1
  wg2 := 0
  wa02 := 0
  wfa2 := 1
  qr := 0
  qf := 0
  Rr1 := x.aRr1
  Rf1 := x.aRr1
  Rr2 := x.aRr2
  Rf2 := x.aRr2
  Rrq := 0
  Rfq := 0
  g1r1 := x.agr1
  g1f1 := x.agr1
  g1r2 := 0
  g1f2 := 0
  g1rq := x.agq1
  g1fq := x.agq1
  g2r := 0
  g2f := x.agr2
  c1r := 0
  c1f := 0
  c2r := 0
  c2f := 0
  smin := sm
  H_NONNEG := by unfold Q.nn at hx; simp only [decide_eq_true_eq] at hx; omega
  H_RISE_LE_FALL := by unfold Q.nn at hx; simp only [decide_eq_true_eq] at hx; omega
  H_LOOP_POS := by omega

theorem sat1 (x : Q) (sm : Int) (hx : x.nn = true) (hs : 0 ≤ sm) :
    Real1 x 0 0 (mk1 x sm hx hs) := by
  unfold Real1 mk1; simp

theorem sat2 (x : Q) (sm : Int) (hx : x.nn = true) (hs : 0 ≤ sm) :
    Real2 x 0 0 (mk2 x sm hx hs) := by
  unfold Real2 mk2; simp

/-! ## The independent box (H_INDEP): each element anywhere in [FMIN, SMAX]

`mix1 lo hi` puts every term on RT1's safe side at `lo` and every term on its
unsafe side at `hi`; it is the worst record in the box. RT1's server-free box
margin is `(mix1 lo hi).m1`; the exact requirement is then
`smin + wa0s + qf + cq ≥ -(mix1 lo hi).m1` (`rt1_iff`, and `box_tight1`). -/

def mix1 (lo hi : Q) : Q :=
  { lo with drg1 := hi.drg1, agr1 := hi.agr1, agq1 := hi.agq1 }
def mix2 (lo hi : Q) : Q :=
  { lo with drg2 := hi.drg2, agr2 := hi.agr2, agq2 := hi.agq2 }

/-- **Box exactness, client 1.** If the second
disjunct fails at the worst box point, then for every server-side sum
`0 ≤ S < -m1` (so `m1 < 0`) there is a valid
record realising that box point with `smin = S` (and `wa0s = qf = cq = 0`) that
violates RT1; with a server answering in exactly `smin`, 7h's
`rt1_counter_minserver` then gives both grants high. -/
theorem box_tight1 (x : Q) (hx : x.nn = true) (hq : x.agq2 < x.agq1)
    (S : Int) (hS0 : 0 ≤ S) (hS : S < -x.m1) :
    Real1 x 0 0 (mk1 x S hx hS0) ∧ (mk1 x S hx hS0).smin = S ∧ ¬ RT1 (mk1 x S hx hS0) := by
  refine ⟨sat1 x S hx hS0, rfl, ?_⟩
  rw [rt1_iff x 0 0 _ (sat1 x S hx hS0)]
  simp only [mk1]; omega

theorem box_tight2 (x : Q) (hx : x.nn = true) (hq : x.agq1 < x.agr2)
    (S : Int) (hS0 : 0 ≤ S) (hS : S < -x.m2) :
    Real2 x 0 0 (mk2 x S hx hS0) ∧ (mk2 x S hx hS0).smin = S ∧ ¬ RT1b (mk2 x S hx hS0) := by
  refine ⟨sat2 x S hx hS0, rfl, ?_⟩
  rw [rt1b_iff x 0 0 _ (sat2 x S hx hS0)]
  simp only [mk2]; omega

/-- H_INDEP box membership (client 1): every term RT1 reads lies in its [lo, hi]. -/
def BoxReal1 (lo hi : Q) (cr cq : Int) (D : Dl) : Prop :=
  0 ≤ cq ∧ cr + lo.drg1 ≤ D.wr1g ∧ D.wr1g ≤ cr + hi.drg1 ∧ cr + lo.drs1 ≤ D.wr1s ∧
    D.wr1s ≤ cr + hi.drs1 ∧ lo.agr1 ≤ D.g1f1 ∧ D.g1f1 ≤ hi.agr1 ∧ lo.aRr1 ≤ D.Rf1 ∧
    D.Rf1 ≤ hi.aRr1 ∧ cq + lo.dqg ≤ D.wq ∧ D.wq ≤ cq + hi.dqg ∧ lo.agq2 ≤ D.g2r ∧
    D.g2r ≤ hi.agq2 ∧ lo.agq1 ≤ D.g1fq ∧ D.g1fq ≤ hi.agq1

def BoxReal2 (lo hi : Q) (cr cq : Int) (D : Dl) : Prop :=
  0 ≤ cq ∧ cr + lo.drg2 ≤ D.wr2g ∧ D.wr2g ≤ cr + hi.drg2 ∧ cr + lo.drs2 ≤ D.wr2s ∧
    D.wr2s ≤ cr + hi.drs2 ∧ lo.agr2 ≤ D.g2f ∧ D.g2f ≤ hi.agr2 ∧ lo.aRr2 ≤ D.Rf2 ∧
    D.Rf2 ≤ hi.aRr2 ∧ cq + lo.dqg ≤ D.wq ∧ D.wq ≤ cq + hi.dqg ∧ lo.agq1 ≤ D.g1rq ∧
    D.g1rq ≤ hi.agq1

/-- **Box, positive direction**: every record in the box satisfies RT1 once the
server-side sum covers the worst point's deficit. -/
theorem box_rt1 (lo hi : Q) (cr cq : Int) (D : Dl) (h : BoxReal1 lo hi cr cq D)
    (hS : 0 ≤ (mix1 lo hi).m1 + (D.smin + D.wa0s + D.qf + cq)) : RT1 D := by
  unfold BoxReal1 at h; unfold Q.m1 mix1 at hS; unfold RT1; simp only at hS; omega

theorem box_rt1b (lo hi : Q) (cr cq : Int) (D : Dl) (h : BoxReal2 lo hi cr cq D)
    (hS : 0 ≤ (mix2 lo hi).m2 + (D.smin + D.wa0s + D.qr + cq)) : RT1b D := by
  unfold BoxReal2 at h; unfold Q.m2 mix2 at hS; unfold RT1b; simp only at hS; omega

/-- The worst box point lies in the box (needs `lo ≤ hi` field by field). -/
def Q.le (a b : Q) : Bool :=
  decide (a.dqg ≤ b.dqg ∧ a.drg1 ≤ b.drg1 ∧ a.drs1 ≤ b.drs1 ∧ a.agr1 ≤ b.agr1 ∧
    a.aRr1 ≤ b.aRr1 ∧ a.agq1 ≤ b.agq1 ∧ a.drg2 ≤ b.drg2 ∧ a.drs2 ≤ b.drs2 ∧
    a.agr2 ≤ b.agr2 ∧ a.aRr2 ≤ b.aRr2 ∧ a.agq2 ≤ b.agq2)

theorem mix1_in (lo hi : Q) (hle : lo.le hi = true) (hx : (mix1 lo hi).nn = true) (S : Int)
    (hS : 0 ≤ S) : BoxReal1 lo hi 0 0 (mk1 (mix1 lo hi) S hx hS) := by
  unfold Q.le at hle; simp only [decide_eq_true_eq] at hle
  unfold BoxReal1 mk1 mix1; simp only; omega

theorem mix2_in (lo hi : Q) (hle : lo.le hi = true) (hx : (mix2 lo hi).nn = true) (S : Int)
    (hS : 0 ≤ S) : BoxReal2 lo hi 0 0 (mk2 (mix2 lo hi) S hx hS) := by
  unfold Q.le at hle; simp only [decide_eq_true_eq] at hle
  unfold BoxReal2 mk2 mix2; simp only; omega

/-- **Box counter-record, client 1**: a record in the box, with `wa0s = qf = 0`
(prefix `cq = 0`) and server `smin = S < need`, that violates RT1. -/
theorem box_cex1 (lo hi : Q) (hle : lo.le hi = true) (hx : (mix1 lo hi).nn = true)
    (hq : (mix1 lo hi).agq2 < (mix1 lo hi).agq1)
    (S : Int) (hS0 : 0 ≤ S) (hS : S < -(mix1 lo hi).m1) :
    ∃ D : Dl, BoxReal1 lo hi 0 0 D ∧ D.smin = S ∧ D.wa0s = 0 ∧ D.qf = 0 ∧ ¬ RT1 D :=
  ⟨_, mix1_in lo hi hle hx S hS0, rfl, rfl, rfl, (box_tight1 _ hx hq S hS0 hS).2.2⟩

theorem box_cex2 (lo hi : Q) (hle : lo.le hi = true) (hx : (mix2 lo hi).nn = true)
    (hq : (mix2 lo hi).agq1 < (mix2 lo hi).agr2)
    (S : Int) (hS0 : 0 ≤ S) (hS : S < -(mix2 lo hi).m2) :
    ∃ D : Dl, BoxReal2 lo hi 0 0 D ∧ D.smin = S ∧ D.wa0s = 0 ∧ D.qr = 0 ∧ ¬ RT1b D :=
  ⟨_, mix2_in lo hi hle hx S hS0, rfl, rfl, rfl, (box_tight2 _ hx hq S hS0 hS).2.2⟩

/-- Check of one corner row: data consistent, non-negative, both margins `≥ 0`. -/
def okCorner (c1 c2 : Formal.Timing.RuntAck.Row) : Bool :=
  rowsAgree c1 c2 && (ofRows c1 c2).nn && decide (0 ≤ (ofRows c1 c2).m1) &&
    decide (0 ≤ (ofRows c1 c2).m2)

theorem okCorner_sound (c1 c2 : Formal.Timing.RuntAck.Row) (h : okCorner c1 c2 = true) :
    (ofRows c1 c2).nn = true ∧ 0 ≤ (ofRows c1 c2).m1 ∧ 0 ≤ (ofRows c1 c2).m2 := by
  unfold okCorner at h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.2, h.1.2, h.2⟩

open Formal.Timing.RuntAck.Inst

/-! ## Per seed x instance x corner: RT1 and RT1b hold for every server

Each `_ok` is decided by the kernel on C's committed rows; with `okCorner_sound`,
`excl1`/`excl2` give grant exclusion in both release directions. The comment on
each line is (m1, m2) in ps. -/

-- m1 = 249, m2 = 407
theorem g2_merge10_uarb1_FMIN_ok : okCorner g2_merge10_uarb1_FMIN_c1 g2_merge10_uarb1_FMIN_c2 = true := by decide
-- m1 = 333, m2 = 544
theorem g2_merge10_uarb1_FMAX_ok : okCorner g2_merge10_uarb1_FMAX_c1 g2_merge10_uarb1_FMAX_c2 = true := by decide
-- m1 = 636, m2 = 974
theorem g2_merge10_uarb1_SMIN_ok : okCorner g2_merge10_uarb1_SMIN_c1 g2_merge10_uarb1_SMIN_c2 = true := by decide
-- m1 = 872, m2 = 1360
theorem g2_merge10_uarb1_SMAX_ok : okCorner g2_merge10_uarb1_SMAX_c1 g2_merge10_uarb1_SMAX_c2 = true := by decide
-- m1 = 949, m2 = 718
theorem g2_merge11_uarb1_FMIN_ok : okCorner g2_merge11_uarb1_FMIN_c1 g2_merge11_uarb1_FMIN_c2 = true := by decide
-- m1 = 1091, m2 = 810
theorem g2_merge11_uarb1_FMAX_ok : okCorner g2_merge11_uarb1_FMAX_c1 g2_merge11_uarb1_FMAX_c2 = true := by decide
-- m1 = 1800, m2 = 1353
theorem g2_merge11_uarb1_SMIN_ok : okCorner g2_merge11_uarb1_SMIN_c1 g2_merge11_uarb1_SMIN_c2 = true := by decide
-- m1 = 2119, m2 = 1576
theorem g2_merge11_uarb1_SMAX_ok : okCorner g2_merge11_uarb1_SMAX_c1 g2_merge11_uarb1_SMAX_c2 = true := by decide
-- m1 = 100, m2 = 109
theorem g2_merge12_uarb1_FMIN_ok : okCorner g2_merge12_uarb1_FMIN_c1 g2_merge12_uarb1_FMIN_c2 = true := by decide
-- m1 = 119, m2 = 139
theorem g2_merge12_uarb1_FMAX_ok : okCorner g2_merge12_uarb1_FMAX_c1 g2_merge12_uarb1_FMAX_c2 = true := by decide
-- m1 = 256, m2 = 327
theorem g2_merge12_uarb1_SMIN_ok : okCorner g2_merge12_uarb1_SMIN_c1 g2_merge12_uarb1_SMIN_c2 = true := by decide
-- m1 = 306, m2 = 404
theorem g2_merge12_uarb1_SMAX_ok : okCorner g2_merge12_uarb1_SMAX_c1 g2_merge12_uarb1_SMAX_c2 = true := by decide
-- m1 = 395, m2 = 196
theorem g2_merge12_uarb2_FMIN_ok : okCorner g2_merge12_uarb2_FMIN_c1 g2_merge12_uarb2_FMIN_c2 = true := by decide
-- m1 = 494, m2 = 247
theorem g2_merge12_uarb2_FMAX_ok : okCorner g2_merge12_uarb2_FMAX_c1 g2_merge12_uarb2_FMAX_c2 = true := by decide
-- m1 = 983, m2 = 566
theorem g2_merge12_uarb2_SMIN_ok : okCorner g2_merge12_uarb2_SMIN_c1 g2_merge12_uarb2_SMIN_c2 = true := by decide
-- m1 = 1218, m2 = 709
theorem g2_merge12_uarb2_SMAX_ok : okCorner g2_merge12_uarb2_SMAX_c1 g2_merge12_uarb2_SMAX_c2 = true := by decide
-- m1 = 94, m2 = 229
theorem g2_merge2_uarb1_FMIN_ok : okCorner g2_merge2_uarb1_FMIN_c1 g2_merge2_uarb1_FMIN_c2 = true := by decide
-- m1 = 112, m2 = 281
theorem g2_merge2_uarb1_FMAX_ok : okCorner g2_merge2_uarb1_FMAX_c1 g2_merge2_uarb1_FMAX_c2 = true := by decide
-- m1 = 289, m2 = 563
theorem g2_merge2_uarb1_SMIN_ok : okCorner g2_merge2_uarb1_SMIN_c1 g2_merge2_uarb1_SMIN_c2 = true := by decide
-- m1 = 346, m2 = 692
theorem g2_merge2_uarb1_SMAX_ok : okCorner g2_merge2_uarb1_SMAX_c1 g2_merge2_uarb1_SMAX_c2 = true := by decide
-- m1 = 254, m2 = 36
theorem g2_merge3_uarb1_FMIN_ok : okCorner g2_merge3_uarb1_FMIN_c1 g2_merge3_uarb1_FMIN_c2 = true := by decide
-- m1 = 311, m2 = 46
theorem g2_merge3_uarb1_FMAX_ok : okCorner g2_merge3_uarb1_FMAX_c1 g2_merge3_uarb1_FMAX_c2 = true := by decide
-- m1 = 606, m2 = 92
theorem g2_merge3_uarb1_SMIN_ok : okCorner g2_merge3_uarb1_SMIN_c1 g2_merge3_uarb1_SMIN_c2 = true := by decide
-- m1 = 742, m2 = 111
theorem g2_merge3_uarb1_SMAX_ok : okCorner g2_merge3_uarb1_SMAX_c1 g2_merge3_uarb1_SMAX_c2 = true := by decide
-- m1 = 374, m2 = 389
theorem g2_merge4_uarb1_FMIN_ok : okCorner g2_merge4_uarb1_FMIN_c1 g2_merge4_uarb1_FMIN_c2 = true := by decide
-- m1 = 458, m2 = 477
theorem g2_merge4_uarb1_FMAX_ok : okCorner g2_merge4_uarb1_FMAX_c1 g2_merge4_uarb1_FMAX_c2 = true := by decide
-- m1 = 904, m2 = 943
theorem g2_merge4_uarb1_SMIN_ok : okCorner g2_merge4_uarb1_SMIN_c1 g2_merge4_uarb1_SMIN_c2 = true := by decide
-- m1 = 1107, m2 = 1169
theorem g2_merge4_uarb1_SMAX_ok : okCorner g2_merge4_uarb1_SMAX_c1 g2_merge4_uarb1_SMAX_c2 = true := by decide
-- m1 = 362, m2 = 235
theorem g2_merge6_uarb1_FMIN_ok : okCorner g2_merge6_uarb1_FMIN_c1 g2_merge6_uarb1_FMIN_c2 = true := by decide
-- m1 = 456, m2 = 290
theorem g2_merge6_uarb1_FMAX_ok : okCorner g2_merge6_uarb1_FMAX_c1 g2_merge6_uarb1_FMAX_c2 = true := by decide
-- m1 = 831, m2 = 635
theorem g2_merge6_uarb1_SMIN_ok : okCorner g2_merge6_uarb1_SMIN_c1 g2_merge6_uarb1_SMIN_c2 = true := by decide
-- m1 = 1062, m2 = 788
theorem g2_merge6_uarb1_SMAX_ok : okCorner g2_merge6_uarb1_SMAX_c1 g2_merge6_uarb1_SMAX_c2 = true := by decide
-- m1 = 169, m2 = 166
theorem g2_merge9_uarb1_FMIN_ok : okCorner g2_merge9_uarb1_FMIN_c1 g2_merge9_uarb1_FMIN_c2 = true := by decide
-- m1 = 210, m2 = 210
theorem g2_merge9_uarb1_FMAX_ok : okCorner g2_merge9_uarb1_FMAX_c1 g2_merge9_uarb1_FMAX_c2 = true := by decide
-- m1 = 442, m2 = 484
theorem g2_merge9_uarb1_SMIN_ok : okCorner g2_merge9_uarb1_SMIN_c1 g2_merge9_uarb1_SMIN_c2 = true := by decide
-- m1 = 545, m2 = 607
theorem g2_merge9_uarb1_SMAX_ok : okCorner g2_merge9_uarb1_SMAX_c1 g2_merge9_uarb1_SMAX_c2 = true := by decide
-- m1 = 395, m2 = 198
theorem g3_merge10_uarb1_FMIN_ok : okCorner g3_merge10_uarb1_FMIN_c1 g3_merge10_uarb1_FMIN_c2 = true := by decide
-- m1 = 478, m2 = 258
theorem g3_merge10_uarb1_FMAX_ok : okCorner g3_merge10_uarb1_FMAX_c1 g3_merge10_uarb1_FMAX_c2 = true := by decide
-- m1 = 961, m2 = 565
theorem g3_merge10_uarb1_SMIN_ok : okCorner g3_merge10_uarb1_SMIN_c1 g3_merge10_uarb1_SMIN_c2 = true := by decide
-- m1 = 1171, m2 = 716
theorem g3_merge10_uarb1_SMAX_ok : okCorner g3_merge10_uarb1_SMAX_c1 g3_merge10_uarb1_SMAX_c2 = true := by decide
-- m1 = 117, m2 = 115
theorem g3_merge11_uarb1_FMIN_ok : okCorner g3_merge11_uarb1_FMIN_c1 g3_merge11_uarb1_FMIN_c2 = true := by decide
-- m1 = 145, m2 = 148
theorem g3_merge11_uarb1_FMAX_ok : okCorner g3_merge11_uarb1_FMAX_c1 g3_merge11_uarb1_FMAX_c2 = true := by decide
-- m1 = 310, m2 = 315
theorem g3_merge11_uarb1_SMIN_ok : okCorner g3_merge11_uarb1_SMIN_c1 g3_merge11_uarb1_SMIN_c2 = true := by decide
-- m1 = 381, m2 = 396
theorem g3_merge11_uarb1_SMAX_ok : okCorner g3_merge11_uarb1_SMAX_c1 g3_merge11_uarb1_SMAX_c2 = true := by decide
-- m1 = 181, m2 = 33
theorem g3_merge12_uarb1_FMIN_ok : okCorner g3_merge12_uarb1_FMIN_c1 g3_merge12_uarb1_FMIN_c2 = true := by decide
-- m1 = 226, m2 = 47
theorem g3_merge12_uarb1_FMAX_ok : okCorner g3_merge12_uarb1_FMAX_c1 g3_merge12_uarb1_FMAX_c2 = true := by decide
-- m1 = 436, m2 = 141
theorem g3_merge12_uarb1_SMIN_ok : okCorner g3_merge12_uarb1_SMIN_c1 g3_merge12_uarb1_SMIN_c2 = true := by decide
-- m1 = 537, m2 = 179
theorem g3_merge12_uarb1_SMAX_ok : okCorner g3_merge12_uarb1_SMAX_c1 g3_merge12_uarb1_SMAX_c2 = true := by decide
-- m1 = 294, m2 = 118
theorem g3_merge12_uarb2_FMIN_ok : okCorner g3_merge12_uarb2_FMIN_c1 g3_merge12_uarb2_FMIN_c2 = true := by decide
-- m1 = 360, m2 = 152
theorem g3_merge12_uarb2_FMAX_ok : okCorner g3_merge12_uarb2_FMAX_c1 g3_merge12_uarb2_FMAX_c2 = true := by decide
-- m1 = 662, m2 = 319
theorem g3_merge12_uarb2_SMIN_ok : okCorner g3_merge12_uarb2_SMIN_c1 g3_merge12_uarb2_SMIN_c2 = true := by decide
-- m1 = 806, m2 = 400
theorem g3_merge12_uarb2_SMAX_ok : okCorner g3_merge12_uarb2_SMAX_c1 g3_merge12_uarb2_SMAX_c2 = true := by decide
-- m1 = 170, m2 = 183
theorem g3_merge2_uarb1_FMIN_ok : okCorner g3_merge2_uarb1_FMIN_c1 g3_merge2_uarb1_FMIN_c2 = true := by decide
-- m1 = 212, m2 = 230
theorem g3_merge2_uarb1_FMAX_ok : okCorner g3_merge2_uarb1_FMAX_c1 g3_merge2_uarb1_FMAX_c2 = true := by decide
-- m1 = 445, m2 = 470
theorem g3_merge2_uarb1_SMIN_ok : okCorner g3_merge2_uarb1_SMIN_c1 g3_merge2_uarb1_SMIN_c2 = true := by decide
-- m1 = 550, m2 = 586
theorem g3_merge2_uarb1_SMAX_ok : okCorner g3_merge2_uarb1_SMAX_c1 g3_merge2_uarb1_SMAX_c2 = true := by decide
-- m1 = 165, m2 = 242
theorem g3_merge3_uarb1_FMIN_ok : okCorner g3_merge3_uarb1_FMIN_c1 g3_merge3_uarb1_FMIN_c2 = true := by decide
-- m1 = 204, m2 = 301
theorem g3_merge3_uarb1_FMAX_ok : okCorner g3_merge3_uarb1_FMAX_c1 g3_merge3_uarb1_FMAX_c2 = true := by decide
-- m1 = 416, m2 = 579
theorem g3_merge3_uarb1_SMIN_ok : okCorner g3_merge3_uarb1_SMIN_c1 g3_merge3_uarb1_SMIN_c2 = true := by decide
-- m1 = 506, m2 = 716
theorem g3_merge3_uarb1_SMAX_ok : okCorner g3_merge3_uarb1_SMAX_c1 g3_merge3_uarb1_SMAX_c2 = true := by decide
-- m1 = 407, m2 = 271
theorem g3_merge4_uarb1_FMIN_ok : okCorner g3_merge4_uarb1_FMIN_c1 g3_merge4_uarb1_FMIN_c2 = true := by decide
-- m1 = 503, m2 = 345
theorem g3_merge4_uarb1_FMAX_ok : okCorner g3_merge4_uarb1_FMAX_c1 g3_merge4_uarb1_FMAX_c2 = true := by decide
-- m1 = 1050, m2 = 730
theorem g3_merge4_uarb1_SMIN_ok : okCorner g3_merge4_uarb1_SMIN_c1 g3_merge4_uarb1_SMIN_c2 = true := by decide
-- m1 = 1301, m2 = 911
theorem g3_merge4_uarb1_SMAX_ok : okCorner g3_merge4_uarb1_SMAX_c1 g3_merge4_uarb1_SMAX_c2 = true := by decide
-- m1 = 259, m2 = 320
theorem g3_merge6_uarb1_FMIN_ok : okCorner g3_merge6_uarb1_FMIN_c1 g3_merge6_uarb1_FMIN_c2 = true := by decide
-- m1 = 320, m2 = 405
theorem g3_merge6_uarb1_FMAX_ok : okCorner g3_merge6_uarb1_FMAX_c1 g3_merge6_uarb1_FMAX_c2 = true := by decide
-- m1 = 619, m2 = 810
theorem g3_merge6_uarb1_SMIN_ok : okCorner g3_merge6_uarb1_SMIN_c1 g3_merge6_uarb1_SMIN_c2 = true := by decide
-- m1 = 764, m2 = 1011
theorem g3_merge6_uarb1_SMAX_ok : okCorner g3_merge6_uarb1_SMAX_c1 g3_merge6_uarb1_SMAX_c2 = true := by decide
-- m1 = 203, m2 = 122
theorem g3_merge9_uarb1_FMIN_ok : okCorner g3_merge9_uarb1_FMIN_c1 g3_merge9_uarb1_FMIN_c2 = true := by decide
-- m1 = 249, m2 = 149
theorem g3_merge9_uarb1_FMAX_ok : okCorner g3_merge9_uarb1_FMAX_c1 g3_merge9_uarb1_FMAX_c2 = true := by decide
-- m1 = 505, m2 = 316
theorem g3_merge9_uarb1_SMIN_ok : okCorner g3_merge9_uarb1_SMIN_c1 g3_merge9_uarb1_SMIN_c2 = true := by decide
-- m1 = 618, m2 = 385
theorem g3_merge9_uarb1_SMAX_ok : okCorner g3_merge9_uarb1_SMAX_c1 g3_merge9_uarb1_SMAX_c2 = true := by decide
-- m1 = 368, m2 = 424
theorem g4_merge10_uarb1_FMIN_ok : okCorner g4_merge10_uarb1_FMIN_c1 g4_merge10_uarb1_FMIN_c2 = true := by decide
-- m1 = 453, m2 = 519
theorem g4_merge10_uarb1_FMAX_ok : okCorner g4_merge10_uarb1_FMAX_c1 g4_merge10_uarb1_FMAX_c2 = true := by decide
-- m1 = 865, m2 = 981
theorem g4_merge10_uarb1_SMIN_ok : okCorner g4_merge10_uarb1_SMIN_c1 g4_merge10_uarb1_SMIN_c2 = true := by decide
-- m1 = 1060, m2 = 1210
theorem g4_merge10_uarb1_SMAX_ok : okCorner g4_merge10_uarb1_SMAX_c1 g4_merge10_uarb1_SMAX_c2 = true := by decide
-- m1 = 169, m2 = 173
theorem g4_merge11_uarb1_FMIN_ok : okCorner g4_merge11_uarb1_FMIN_c1 g4_merge11_uarb1_FMIN_c2 = true := by decide
-- m1 = 209, m2 = 220
theorem g4_merge11_uarb1_FMAX_ok : okCorner g4_merge11_uarb1_FMAX_c1 g4_merge11_uarb1_FMAX_c2 = true := by decide
-- m1 = 450, m2 = 496
theorem g4_merge11_uarb1_SMIN_ok : okCorner g4_merge11_uarb1_SMIN_c1 g4_merge11_uarb1_SMIN_c2 = true := by decide
-- m1 = 555, m2 = 621
theorem g4_merge11_uarb1_SMAX_ok : okCorner g4_merge11_uarb1_SMAX_c1 g4_merge11_uarb1_SMAX_c2 = true := by decide
-- m1 = 218, m2 = 255
theorem g4_merge12_uarb1_FMIN_ok : okCorner g4_merge12_uarb1_FMIN_c1 g4_merge12_uarb1_FMIN_c2 = true := by decide
-- m1 = 270, m2 = 320
theorem g4_merge12_uarb1_FMAX_ok : okCorner g4_merge12_uarb1_FMAX_c1 g4_merge12_uarb1_FMAX_c2 = true := by decide
-- m1 = 477, m2 = 652
theorem g4_merge12_uarb1_SMIN_ok : okCorner g4_merge12_uarb1_SMIN_c1 g4_merge12_uarb1_SMIN_c2 = true := by decide
-- m1 = 584, m2 = 819
theorem g4_merge12_uarb1_SMAX_ok : okCorner g4_merge12_uarb1_SMAX_c1 g4_merge12_uarb1_SMAX_c2 = true := by decide
-- m1 = 357, m2 = 212
theorem g4_merge12_uarb2_FMIN_ok : okCorner g4_merge12_uarb2_FMIN_c1 g4_merge12_uarb2_FMIN_c2 = true := by decide
-- m1 = 430, m2 = 255
theorem g4_merge12_uarb2_FMAX_ok : okCorner g4_merge12_uarb2_FMAX_c1 g4_merge12_uarb2_FMAX_c2 = true := by decide
-- m1 = 941, m2 = 609
theorem g4_merge12_uarb2_SMIN_ok : okCorner g4_merge12_uarb2_SMIN_c1 g4_merge12_uarb2_SMIN_c2 = true := by decide
-- m1 = 1144, m2 = 738
theorem g4_merge12_uarb2_SMAX_ok : okCorner g4_merge12_uarb2_SMAX_c1 g4_merge12_uarb2_SMAX_c2 = true := by decide
-- m1 = 508, m2 = 169
theorem g4_merge2_uarb1_FMIN_ok : okCorner g4_merge2_uarb1_FMIN_c1 g4_merge2_uarb1_FMIN_c2 = true := by decide
-- m1 = 580, m2 = 213
theorem g4_merge2_uarb1_FMAX_ok : okCorner g4_merge2_uarb1_FMAX_c1 g4_merge2_uarb1_FMAX_c2 = true := by decide
-- m1 = 1020, m2 = 493
theorem g4_merge2_uarb1_SMIN_ok : okCorner g4_merge2_uarb1_SMIN_c1 g4_merge2_uarb1_SMIN_c2 = true := by decide
-- m1 = 1209, m2 = 616
theorem g4_merge2_uarb1_SMAX_ok : okCorner g4_merge2_uarb1_SMAX_c1 g4_merge2_uarb1_SMAX_c2 = true := by decide
-- m1 = 241, m2 = 652
theorem g4_merge3_uarb1_FMIN_ok : okCorner g4_merge3_uarb1_FMIN_c1 g4_merge3_uarb1_FMIN_c2 = true := by decide
-- m1 = 291, m2 = 759
theorem g4_merge3_uarb1_FMAX_ok : okCorner g4_merge3_uarb1_FMAX_c1 g4_merge3_uarb1_FMAX_c2 = true := by decide
-- m1 = 606, m2 = 1385
theorem g4_merge3_uarb1_SMIN_ok : okCorner g4_merge3_uarb1_SMIN_c1 g4_merge3_uarb1_SMIN_c2 = true := by decide
-- m1 = 734, m2 = 1657
theorem g4_merge3_uarb1_SMAX_ok : okCorner g4_merge3_uarb1_SMAX_c1 g4_merge3_uarb1_SMAX_c2 = true := by decide
-- m1 = 226, m2 = 217
theorem g4_merge4_uarb1_FMIN_ok : okCorner g4_merge4_uarb1_FMIN_c1 g4_merge4_uarb1_FMIN_c2 = true := by decide
-- m1 = 277, m2 = 261
theorem g4_merge4_uarb1_FMAX_ok : okCorner g4_merge4_uarb1_FMAX_c1 g4_merge4_uarb1_FMAX_c2 = true := by decide
-- m1 = 590, m2 = 631
theorem g4_merge4_uarb1_SMIN_ok : okCorner g4_merge4_uarb1_SMIN_c1 g4_merge4_uarb1_SMIN_c2 = true := by decide
-- m1 = 721, m2 = 771
theorem g4_merge4_uarb1_SMAX_ok : okCorner g4_merge4_uarb1_SMAX_c1 g4_merge4_uarb1_SMAX_c2 = true := by decide
-- m1 = 363, m2 = 240
theorem g4_merge6_uarb1_FMIN_ok : okCorner g4_merge6_uarb1_FMIN_c1 g4_merge6_uarb1_FMIN_c2 = true := by decide
-- m1 = 440, m2 = 299
theorem g4_merge6_uarb1_FMAX_ok : okCorner g4_merge6_uarb1_FMAX_c1 g4_merge6_uarb1_FMAX_c2 = true := by decide
-- m1 = 860, m2 = 663
theorem g4_merge6_uarb1_SMIN_ok : okCorner g4_merge6_uarb1_SMIN_c1 g4_merge6_uarb1_SMIN_c2 = true := by decide
-- m1 = 1046, m2 = 821
theorem g4_merge6_uarb1_SMAX_ok : okCorner g4_merge6_uarb1_SMAX_c1 g4_merge6_uarb1_SMAX_c2 = true := by decide
-- m1 = 257, m2 = 249
theorem g4_merge9_uarb1_FMIN_ok : okCorner g4_merge9_uarb1_FMIN_c1 g4_merge9_uarb1_FMIN_c2 = true := by decide
-- m1 = 314, m2 = 309
theorem g4_merge9_uarb1_FMAX_ok : okCorner g4_merge9_uarb1_FMAX_c1 g4_merge9_uarb1_FMAX_c2 = true := by decide
-- m1 = 671, m2 = 706
theorem g4_merge9_uarb1_SMIN_ok : okCorner g4_merge9_uarb1_SMIN_c1 g4_merge9_uarb1_SMIN_c2 = true := by decide
-- m1 = 821, m2 = 875
theorem g4_merge9_uarb1_SMAX_ok : okCorner g4_merge9_uarb1_SMAX_c1 g4_merge9_uarb1_SMAX_c2 = true := by decide
-- m1 = 375, m2 = 305
theorem gd_merge10_uarb1_FMIN_ok : okCorner gd_merge10_uarb1_FMIN_c1 gd_merge10_uarb1_FMIN_c2 = true := by decide
-- m1 = 508, m2 = 420
theorem gd_merge10_uarb1_FMAX_ok : okCorner gd_merge10_uarb1_FMAX_c1 gd_merge10_uarb1_FMAX_c2 = true := by decide
-- m1 = 862, m2 = 783
theorem gd_merge10_uarb1_SMIN_ok : okCorner gd_merge10_uarb1_SMIN_c1 gd_merge10_uarb1_SMIN_c2 = true := by decide
-- m1 = 1222, m2 = 1098
theorem gd_merge10_uarb1_SMAX_ok : okCorner gd_merge10_uarb1_SMAX_c1 gd_merge10_uarb1_SMAX_c2 = true := by decide
-- m1 = 267, m2 = 375
theorem gd_merge11_uarb1_FMIN_ok : okCorner gd_merge11_uarb1_FMIN_c1 gd_merge11_uarb1_FMIN_c2 = true := by decide
-- m1 = 333, m2 = 462
theorem gd_merge11_uarb1_FMAX_ok : okCorner gd_merge11_uarb1_FMAX_c1 gd_merge11_uarb1_FMAX_c2 = true := by decide
-- m1 = 632, m2 = 917
theorem gd_merge11_uarb1_SMIN_ok : okCorner gd_merge11_uarb1_SMIN_c1 gd_merge11_uarb1_SMIN_c2 = true := by decide
-- m1 = 785, m2 = 1137
theorem gd_merge11_uarb1_SMAX_ok : okCorner gd_merge11_uarb1_SMAX_c1 gd_merge11_uarb1_SMAX_c2 = true := by decide
-- m1 = 316, m2 = 229
theorem gd_merge12_uarb1_FMIN_ok : okCorner gd_merge12_uarb1_FMIN_c1 gd_merge12_uarb1_FMIN_c2 = true := by decide
-- m1 = 390, m2 = 286
theorem gd_merge12_uarb1_FMAX_ok : okCorner gd_merge12_uarb1_FMAX_c1 gd_merge12_uarb1_FMAX_c2 = true := by decide
-- m1 = 768, m2 = 621
theorem gd_merge12_uarb1_SMIN_ok : okCorner gd_merge12_uarb1_SMIN_c1 gd_merge12_uarb1_SMIN_c2 = true := by decide
-- m1 = 945, m2 = 772
theorem gd_merge12_uarb1_SMAX_ok : okCorner gd_merge12_uarb1_SMAX_c1 gd_merge12_uarb1_SMAX_c2 = true := by decide
-- m1 = 353, m2 = 203
theorem gd_merge12_uarb2_FMIN_ok : okCorner gd_merge12_uarb2_FMIN_c1 gd_merge12_uarb2_FMIN_c2 = true := by decide
-- m1 = 408, m2 = 218
theorem gd_merge12_uarb2_FMAX_ok : okCorner gd_merge12_uarb2_FMAX_c1 gd_merge12_uarb2_FMAX_c2 = true := by decide
-- m1 = 813, m2 = 551
theorem gd_merge12_uarb2_SMIN_ok : okCorner gd_merge12_uarb2_SMIN_c1 gd_merge12_uarb2_SMIN_c2 = true := by decide
-- m1 = 923, m2 = 566
theorem gd_merge12_uarb2_SMAX_ok : okCorner gd_merge12_uarb2_SMAX_c1 gd_merge12_uarb2_SMAX_c2 = true := by decide
-- m1 = 169, m2 = 172
theorem gd_merge2_uarb1_FMIN_ok : okCorner gd_merge2_uarb1_FMIN_c1 gd_merge2_uarb1_FMIN_c2 = true := by decide
-- m1 = 209, m2 = 220
theorem gd_merge2_uarb1_FMAX_ok : okCorner gd_merge2_uarb1_FMAX_c1 gd_merge2_uarb1_FMAX_c2 = true := by decide
-- m1 = 450, m2 = 489
theorem gd_merge2_uarb1_SMIN_ok : okCorner gd_merge2_uarb1_SMIN_c1 gd_merge2_uarb1_SMIN_c2 = true := by decide
-- m1 = 555, m2 = 619
theorem gd_merge2_uarb1_SMAX_ok : okCorner gd_merge2_uarb1_SMAX_c1 gd_merge2_uarb1_SMAX_c2 = true := by decide
-- m1 = 245, m2 = 382
theorem gd_merge3_uarb1_FMIN_ok : okCorner gd_merge3_uarb1_FMIN_c1 gd_merge3_uarb1_FMIN_c2 = true := by decide
-- m1 = 305, m2 = 476
theorem gd_merge3_uarb1_FMAX_ok : okCorner gd_merge3_uarb1_FMAX_c1 gd_merge3_uarb1_FMAX_c2 = true := by decide
-- m1 = 623, m2 = 969
theorem gd_merge3_uarb1_SMIN_ok : okCorner gd_merge3_uarb1_SMIN_c1 gd_merge3_uarb1_SMIN_c2 = true := by decide
-- m1 = 775, m2 = 1201
theorem gd_merge3_uarb1_SMAX_ok : okCorner gd_merge3_uarb1_SMAX_c1 gd_merge3_uarb1_SMAX_c2 = true := by decide
-- m1 = 266, m2 = 269
theorem gd_merge4_uarb1_FMIN_ok : okCorner gd_merge4_uarb1_FMIN_c1 gd_merge4_uarb1_FMIN_c2 = true := by decide
-- m1 = 329, m2 = 349
theorem gd_merge4_uarb1_FMAX_ok : okCorner gd_merge4_uarb1_FMAX_c1 gd_merge4_uarb1_FMAX_c2 = true := by decide
-- m1 = 631, m2 = 798
theorem gd_merge4_uarb1_SMIN_ok : okCorner gd_merge4_uarb1_SMIN_c1 gd_merge4_uarb1_SMIN_c2 = true := by decide
-- m1 = 771, m2 = 1008
theorem gd_merge4_uarb1_SMAX_ok : okCorner gd_merge4_uarb1_SMAX_c1 gd_merge4_uarb1_SMAX_c2 = true := by decide
-- m1 = 397, m2 = 448
theorem gd_merge6_uarb1_FMIN_ok : okCorner gd_merge6_uarb1_FMIN_c1 gd_merge6_uarb1_FMIN_c2 = true := by decide
-- m1 = 487, m2 = 557
theorem gd_merge6_uarb1_FMAX_ok : okCorner gd_merge6_uarb1_FMAX_c1 gd_merge6_uarb1_FMAX_c2 = true := by decide
-- m1 = 961, m2 = 1140
theorem gd_merge6_uarb1_SMIN_ok : okCorner gd_merge6_uarb1_SMIN_c1 gd_merge6_uarb1_SMIN_c2 = true := by decide
-- m1 = 1181, m2 = 1415
theorem gd_merge6_uarb1_SMAX_ok : okCorner gd_merge6_uarb1_SMAX_c1 gd_merge6_uarb1_SMAX_c2 = true := by decide
-- m1 = 53, m2 = 125
theorem gd_merge9_uarb1_FMIN_ok : okCorner gd_merge9_uarb1_FMIN_c1 gd_merge9_uarb1_FMIN_c2 = true := by decide
-- m1 = 68, m2 = 165
theorem gd_merge9_uarb1_FMAX_ok : okCorner gd_merge9_uarb1_FMAX_c1 gd_merge9_uarb1_FMAX_c2 = true := by decide
-- m1 = 102, m2 = 332
theorem gd_merge9_uarb1_SMIN_ok : okCorner gd_merge9_uarb1_SMIN_c1 gd_merge9_uarb1_SMIN_c2 = true := by decide
-- m1 = 122, m2 = 417
theorem gd_merge9_uarb1_SMAX_ok : okCorner gd_merge9_uarb1_SMAX_c1 gd_merge9_uarb1_SMAX_c2 = true := by decide

/-- All 36 arbiters x 4 corners. -/
def allRows : List (Formal.Timing.RuntAck.Row × Formal.Timing.RuntAck.Row) :=
  [(g2_merge10_uarb1_FMIN_c1, g2_merge10_uarb1_FMIN_c2),
   (g2_merge10_uarb1_FMAX_c1, g2_merge10_uarb1_FMAX_c2),
   (g2_merge10_uarb1_SMIN_c1, g2_merge10_uarb1_SMIN_c2),
   (g2_merge10_uarb1_SMAX_c1, g2_merge10_uarb1_SMAX_c2),
   (g2_merge11_uarb1_FMIN_c1, g2_merge11_uarb1_FMIN_c2),
   (g2_merge11_uarb1_FMAX_c1, g2_merge11_uarb1_FMAX_c2),
   (g2_merge11_uarb1_SMIN_c1, g2_merge11_uarb1_SMIN_c2),
   (g2_merge11_uarb1_SMAX_c1, g2_merge11_uarb1_SMAX_c2),
   (g2_merge12_uarb1_FMIN_c1, g2_merge12_uarb1_FMIN_c2),
   (g2_merge12_uarb1_FMAX_c1, g2_merge12_uarb1_FMAX_c2),
   (g2_merge12_uarb1_SMIN_c1, g2_merge12_uarb1_SMIN_c2),
   (g2_merge12_uarb1_SMAX_c1, g2_merge12_uarb1_SMAX_c2),
   (g2_merge12_uarb2_FMIN_c1, g2_merge12_uarb2_FMIN_c2),
   (g2_merge12_uarb2_FMAX_c1, g2_merge12_uarb2_FMAX_c2),
   (g2_merge12_uarb2_SMIN_c1, g2_merge12_uarb2_SMIN_c2),
   (g2_merge12_uarb2_SMAX_c1, g2_merge12_uarb2_SMAX_c2),
   (g2_merge2_uarb1_FMIN_c1, g2_merge2_uarb1_FMIN_c2),
   (g2_merge2_uarb1_FMAX_c1, g2_merge2_uarb1_FMAX_c2),
   (g2_merge2_uarb1_SMIN_c1, g2_merge2_uarb1_SMIN_c2),
   (g2_merge2_uarb1_SMAX_c1, g2_merge2_uarb1_SMAX_c2),
   (g2_merge3_uarb1_FMIN_c1, g2_merge3_uarb1_FMIN_c2),
   (g2_merge3_uarb1_FMAX_c1, g2_merge3_uarb1_FMAX_c2),
   (g2_merge3_uarb1_SMIN_c1, g2_merge3_uarb1_SMIN_c2),
   (g2_merge3_uarb1_SMAX_c1, g2_merge3_uarb1_SMAX_c2),
   (g2_merge4_uarb1_FMIN_c1, g2_merge4_uarb1_FMIN_c2),
   (g2_merge4_uarb1_FMAX_c1, g2_merge4_uarb1_FMAX_c2),
   (g2_merge4_uarb1_SMIN_c1, g2_merge4_uarb1_SMIN_c2),
   (g2_merge4_uarb1_SMAX_c1, g2_merge4_uarb1_SMAX_c2),
   (g2_merge6_uarb1_FMIN_c1, g2_merge6_uarb1_FMIN_c2),
   (g2_merge6_uarb1_FMAX_c1, g2_merge6_uarb1_FMAX_c2),
   (g2_merge6_uarb1_SMIN_c1, g2_merge6_uarb1_SMIN_c2),
   (g2_merge6_uarb1_SMAX_c1, g2_merge6_uarb1_SMAX_c2),
   (g2_merge9_uarb1_FMIN_c1, g2_merge9_uarb1_FMIN_c2),
   (g2_merge9_uarb1_FMAX_c1, g2_merge9_uarb1_FMAX_c2),
   (g2_merge9_uarb1_SMIN_c1, g2_merge9_uarb1_SMIN_c2),
   (g2_merge9_uarb1_SMAX_c1, g2_merge9_uarb1_SMAX_c2),
   (g3_merge10_uarb1_FMIN_c1, g3_merge10_uarb1_FMIN_c2),
   (g3_merge10_uarb1_FMAX_c1, g3_merge10_uarb1_FMAX_c2),
   (g3_merge10_uarb1_SMIN_c1, g3_merge10_uarb1_SMIN_c2),
   (g3_merge10_uarb1_SMAX_c1, g3_merge10_uarb1_SMAX_c2),
   (g3_merge11_uarb1_FMIN_c1, g3_merge11_uarb1_FMIN_c2),
   (g3_merge11_uarb1_FMAX_c1, g3_merge11_uarb1_FMAX_c2),
   (g3_merge11_uarb1_SMIN_c1, g3_merge11_uarb1_SMIN_c2),
   (g3_merge11_uarb1_SMAX_c1, g3_merge11_uarb1_SMAX_c2),
   (g3_merge12_uarb1_FMIN_c1, g3_merge12_uarb1_FMIN_c2),
   (g3_merge12_uarb1_FMAX_c1, g3_merge12_uarb1_FMAX_c2),
   (g3_merge12_uarb1_SMIN_c1, g3_merge12_uarb1_SMIN_c2),
   (g3_merge12_uarb1_SMAX_c1, g3_merge12_uarb1_SMAX_c2),
   (g3_merge12_uarb2_FMIN_c1, g3_merge12_uarb2_FMIN_c2),
   (g3_merge12_uarb2_FMAX_c1, g3_merge12_uarb2_FMAX_c2),
   (g3_merge12_uarb2_SMIN_c1, g3_merge12_uarb2_SMIN_c2),
   (g3_merge12_uarb2_SMAX_c1, g3_merge12_uarb2_SMAX_c2),
   (g3_merge2_uarb1_FMIN_c1, g3_merge2_uarb1_FMIN_c2),
   (g3_merge2_uarb1_FMAX_c1, g3_merge2_uarb1_FMAX_c2),
   (g3_merge2_uarb1_SMIN_c1, g3_merge2_uarb1_SMIN_c2),
   (g3_merge2_uarb1_SMAX_c1, g3_merge2_uarb1_SMAX_c2),
   (g3_merge3_uarb1_FMIN_c1, g3_merge3_uarb1_FMIN_c2),
   (g3_merge3_uarb1_FMAX_c1, g3_merge3_uarb1_FMAX_c2),
   (g3_merge3_uarb1_SMIN_c1, g3_merge3_uarb1_SMIN_c2),
   (g3_merge3_uarb1_SMAX_c1, g3_merge3_uarb1_SMAX_c2),
   (g3_merge4_uarb1_FMIN_c1, g3_merge4_uarb1_FMIN_c2),
   (g3_merge4_uarb1_FMAX_c1, g3_merge4_uarb1_FMAX_c2),
   (g3_merge4_uarb1_SMIN_c1, g3_merge4_uarb1_SMIN_c2),
   (g3_merge4_uarb1_SMAX_c1, g3_merge4_uarb1_SMAX_c2),
   (g3_merge6_uarb1_FMIN_c1, g3_merge6_uarb1_FMIN_c2),
   (g3_merge6_uarb1_FMAX_c1, g3_merge6_uarb1_FMAX_c2),
   (g3_merge6_uarb1_SMIN_c1, g3_merge6_uarb1_SMIN_c2),
   (g3_merge6_uarb1_SMAX_c1, g3_merge6_uarb1_SMAX_c2),
   (g3_merge9_uarb1_FMIN_c1, g3_merge9_uarb1_FMIN_c2),
   (g3_merge9_uarb1_FMAX_c1, g3_merge9_uarb1_FMAX_c2),
   (g3_merge9_uarb1_SMIN_c1, g3_merge9_uarb1_SMIN_c2),
   (g3_merge9_uarb1_SMAX_c1, g3_merge9_uarb1_SMAX_c2),
   (g4_merge10_uarb1_FMIN_c1, g4_merge10_uarb1_FMIN_c2),
   (g4_merge10_uarb1_FMAX_c1, g4_merge10_uarb1_FMAX_c2),
   (g4_merge10_uarb1_SMIN_c1, g4_merge10_uarb1_SMIN_c2),
   (g4_merge10_uarb1_SMAX_c1, g4_merge10_uarb1_SMAX_c2),
   (g4_merge11_uarb1_FMIN_c1, g4_merge11_uarb1_FMIN_c2),
   (g4_merge11_uarb1_FMAX_c1, g4_merge11_uarb1_FMAX_c2),
   (g4_merge11_uarb1_SMIN_c1, g4_merge11_uarb1_SMIN_c2),
   (g4_merge11_uarb1_SMAX_c1, g4_merge11_uarb1_SMAX_c2),
   (g4_merge12_uarb1_FMIN_c1, g4_merge12_uarb1_FMIN_c2),
   (g4_merge12_uarb1_FMAX_c1, g4_merge12_uarb1_FMAX_c2),
   (g4_merge12_uarb1_SMIN_c1, g4_merge12_uarb1_SMIN_c2),
   (g4_merge12_uarb1_SMAX_c1, g4_merge12_uarb1_SMAX_c2),
   (g4_merge12_uarb2_FMIN_c1, g4_merge12_uarb2_FMIN_c2),
   (g4_merge12_uarb2_FMAX_c1, g4_merge12_uarb2_FMAX_c2),
   (g4_merge12_uarb2_SMIN_c1, g4_merge12_uarb2_SMIN_c2),
   (g4_merge12_uarb2_SMAX_c1, g4_merge12_uarb2_SMAX_c2),
   (g4_merge2_uarb1_FMIN_c1, g4_merge2_uarb1_FMIN_c2),
   (g4_merge2_uarb1_FMAX_c1, g4_merge2_uarb1_FMAX_c2),
   (g4_merge2_uarb1_SMIN_c1, g4_merge2_uarb1_SMIN_c2),
   (g4_merge2_uarb1_SMAX_c1, g4_merge2_uarb1_SMAX_c2),
   (g4_merge3_uarb1_FMIN_c1, g4_merge3_uarb1_FMIN_c2),
   (g4_merge3_uarb1_FMAX_c1, g4_merge3_uarb1_FMAX_c2),
   (g4_merge3_uarb1_SMIN_c1, g4_merge3_uarb1_SMIN_c2),
   (g4_merge3_uarb1_SMAX_c1, g4_merge3_uarb1_SMAX_c2),
   (g4_merge4_uarb1_FMIN_c1, g4_merge4_uarb1_FMIN_c2),
   (g4_merge4_uarb1_FMAX_c1, g4_merge4_uarb1_FMAX_c2),
   (g4_merge4_uarb1_SMIN_c1, g4_merge4_uarb1_SMIN_c2),
   (g4_merge4_uarb1_SMAX_c1, g4_merge4_uarb1_SMAX_c2),
   (g4_merge6_uarb1_FMIN_c1, g4_merge6_uarb1_FMIN_c2),
   (g4_merge6_uarb1_FMAX_c1, g4_merge6_uarb1_FMAX_c2),
   (g4_merge6_uarb1_SMIN_c1, g4_merge6_uarb1_SMIN_c2),
   (g4_merge6_uarb1_SMAX_c1, g4_merge6_uarb1_SMAX_c2),
   (g4_merge9_uarb1_FMIN_c1, g4_merge9_uarb1_FMIN_c2),
   (g4_merge9_uarb1_FMAX_c1, g4_merge9_uarb1_FMAX_c2),
   (g4_merge9_uarb1_SMIN_c1, g4_merge9_uarb1_SMIN_c2),
   (g4_merge9_uarb1_SMAX_c1, g4_merge9_uarb1_SMAX_c2),
   (gd_merge10_uarb1_FMIN_c1, gd_merge10_uarb1_FMIN_c2),
   (gd_merge10_uarb1_FMAX_c1, gd_merge10_uarb1_FMAX_c2),
   (gd_merge10_uarb1_SMIN_c1, gd_merge10_uarb1_SMIN_c2),
   (gd_merge10_uarb1_SMAX_c1, gd_merge10_uarb1_SMAX_c2),
   (gd_merge11_uarb1_FMIN_c1, gd_merge11_uarb1_FMIN_c2),
   (gd_merge11_uarb1_FMAX_c1, gd_merge11_uarb1_FMAX_c2),
   (gd_merge11_uarb1_SMIN_c1, gd_merge11_uarb1_SMIN_c2),
   (gd_merge11_uarb1_SMAX_c1, gd_merge11_uarb1_SMAX_c2),
   (gd_merge12_uarb1_FMIN_c1, gd_merge12_uarb1_FMIN_c2),
   (gd_merge12_uarb1_FMAX_c1, gd_merge12_uarb1_FMAX_c2),
   (gd_merge12_uarb1_SMIN_c1, gd_merge12_uarb1_SMIN_c2),
   (gd_merge12_uarb1_SMAX_c1, gd_merge12_uarb1_SMAX_c2),
   (gd_merge12_uarb2_FMIN_c1, gd_merge12_uarb2_FMIN_c2),
   (gd_merge12_uarb2_FMAX_c1, gd_merge12_uarb2_FMAX_c2),
   (gd_merge12_uarb2_SMIN_c1, gd_merge12_uarb2_SMIN_c2),
   (gd_merge12_uarb2_SMAX_c1, gd_merge12_uarb2_SMAX_c2),
   (gd_merge2_uarb1_FMIN_c1, gd_merge2_uarb1_FMIN_c2),
   (gd_merge2_uarb1_FMAX_c1, gd_merge2_uarb1_FMAX_c2),
   (gd_merge2_uarb1_SMIN_c1, gd_merge2_uarb1_SMIN_c2),
   (gd_merge2_uarb1_SMAX_c1, gd_merge2_uarb1_SMAX_c2),
   (gd_merge3_uarb1_FMIN_c1, gd_merge3_uarb1_FMIN_c2),
   (gd_merge3_uarb1_FMAX_c1, gd_merge3_uarb1_FMAX_c2),
   (gd_merge3_uarb1_SMIN_c1, gd_merge3_uarb1_SMIN_c2),
   (gd_merge3_uarb1_SMAX_c1, gd_merge3_uarb1_SMAX_c2),
   (gd_merge4_uarb1_FMIN_c1, gd_merge4_uarb1_FMIN_c2),
   (gd_merge4_uarb1_FMAX_c1, gd_merge4_uarb1_FMAX_c2),
   (gd_merge4_uarb1_SMIN_c1, gd_merge4_uarb1_SMIN_c2),
   (gd_merge4_uarb1_SMAX_c1, gd_merge4_uarb1_SMAX_c2),
   (gd_merge6_uarb1_FMIN_c1, gd_merge6_uarb1_FMIN_c2),
   (gd_merge6_uarb1_FMAX_c1, gd_merge6_uarb1_FMAX_c2),
   (gd_merge6_uarb1_SMIN_c1, gd_merge6_uarb1_SMIN_c2),
   (gd_merge6_uarb1_SMAX_c1, gd_merge6_uarb1_SMAX_c2),
   (gd_merge9_uarb1_FMIN_c1, gd_merge9_uarb1_FMIN_c2),
   (gd_merge9_uarb1_FMAX_c1, gd_merge9_uarb1_FMAX_c2),
   (gd_merge9_uarb1_SMIN_c1, gd_merge9_uarb1_SMIN_c2),
   (gd_merge9_uarb1_SMAX_c1, gd_merge9_uarb1_SMAX_c2)]

theorem allRows_length : allRows.length = 144 := by rfl

set_option maxRecDepth 100000 in
theorem allRows_ok : allRows.all (fun p => okCorner p.1 p.2) = true := by decide

/-- **Headline, client-1 release.** On every routed gcd_hw arbiter (4 seeds x 9) at
every consistent prjxray corner, for every 7h delay record realising C's routed row
(any r1/q prefixes, any A0 branch, any ustate O6 arc, ANY server `smin ≥ 0`), every
run of the gate relations through the handover keeps g1 and g2 exclusive. -/
theorem gcd_rt1_all : ∀ p ∈ allRows, ∀ {D : Dl} {s : Sigs} {t0 ta TA TA2 Hz cr cq : Int},
    Real1 (ofRows p.1 p.2) cr cq D → Run D s → Scn D s t0 ta TA TA2 Hz →
    ∀ t, t < Hz → (s.g1 t && s.g2 t) = false := by
  intro p hp D s t0 ta TA TA2 Hz cr cq h R S
  have hok := List.all_eq_true.mp allRows_ok p hp
  exact excl1 _ (okCorner_sound _ _ hok).2.1 h R S

/-- **Headline, client-2 release** (7j's mirror). -/
theorem gcd_rt1b_all : ∀ p ∈ allRows, ∀ {D : Dl} {s : Sigs} {t0 ta TA TA2 Hz cr cq : Int},
    Real2 (ofRows p.1 p.2) cr cq D → Run D s → Scn2 D s t0 ta TA TA2 Hz →
    ∀ t, t < Hz → (s.g1 t && s.g2 t) = false := by
  intro p hp D s t0 ta TA TA2 Hz cr cq h R S
  have hok := List.all_eq_true.mp allRows_ok p hp
  exact excl2 _ (okCorner_sound _ _ hok).2.2 h R S

/-- Non-vacuity of the instantiation hypotheses on every row: a valid 7h record
realises it (for any server). The model's own non-vacuity (a `Run` and `Scn`/`Scn2`
exist) is `ArbCorners.nonvacuous_corners`. -/
theorem allRows_sat : ∀ p ∈ allRows, ∀ sm : Int, 0 ≤ sm →
    (∃ D : Dl, Real1 (ofRows p.1 p.2) 0 0 D ∧ D.smin = sm) ∧
    (∃ D : Dl, Real2 (ofRows p.1 p.2) 0 0 D ∧ D.smin = sm) := by
  intro p hp sm hs
  have hok := List.all_eq_true.mp allRows_ok p hp
  have hx := (okCorner_sound _ _ hok).1
  exact ⟨⟨_, sat1 _ sm hx hs, rfl⟩, ⟨_, sat2 _ sm hx hs, rfl⟩⟩

/-! ## The independent box (H_INDEP: each element in [FMIN, SMAX]), per instance

`_box` gives the exact worst-point server-free margins (m1, m2); when one is
negative, `_cex1`/`_cex2` exhibit a valid record in the box with
`smin + wa0s + qf + cq = need - 1` that violates RT1/RT1b (7h's
`rt1_counter_minserver` / 7j's `rt1_counter2_minserver` turn it into an overlap
when the server answers in exactly `smin`); `box_rt1`/`box_rt1b` give RT1/RT1b for
every box record once that sum is `≥ need`. So `need` is exact. -/

theorem g2_merge10_uarb1_box : (ofRows g2_merge10_uarb1_FMIN_c1 g2_merge10_uarb1_FMIN_c2).le (ofRows g2_merge10_uarb1_SMAX_c1 g2_merge10_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows g2_merge10_uarb1_FMIN_c1 g2_merge10_uarb1_FMIN_c2) (ofRows g2_merge10_uarb1_SMAX_c1 g2_merge10_uarb1_SMAX_c2)).m1 = -383 ∧
    (mix2 (ofRows g2_merge10_uarb1_FMIN_c1 g2_merge10_uarb1_FMIN_c2) (ofRows g2_merge10_uarb1_SMAX_c1 g2_merge10_uarb1_SMAX_c2)).m2 = -9 := by decide
theorem g2_merge10_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows g2_merge10_uarb1_FMIN_c1 g2_merge10_uarb1_FMIN_c2) (ofRows g2_merge10_uarb1_SMAX_c1 g2_merge10_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 382 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 382 (by decide) (by decide)
theorem g2_merge10_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows g2_merge10_uarb1_FMIN_c1 g2_merge10_uarb1_FMIN_c2) (ofRows g2_merge10_uarb1_SMAX_c1 g2_merge10_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 8 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 8 (by decide) (by decide)
theorem g2_merge11_uarb1_box : (ofRows g2_merge11_uarb1_FMIN_c1 g2_merge11_uarb1_FMIN_c2).le (ofRows g2_merge11_uarb1_SMAX_c1 g2_merge11_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows g2_merge11_uarb1_FMIN_c1 g2_merge11_uarb1_FMIN_c2) (ofRows g2_merge11_uarb1_SMAX_c1 g2_merge11_uarb1_SMAX_c2)).m1 = 263 ∧
    (mix2 (ofRows g2_merge11_uarb1_FMIN_c1 g2_merge11_uarb1_FMIN_c2) (ofRows g2_merge11_uarb1_SMAX_c1 g2_merge11_uarb1_SMAX_c2)).m2 = 98 := by decide
theorem g2_merge12_uarb1_box : (ofRows g2_merge12_uarb1_FMIN_c1 g2_merge12_uarb1_FMIN_c2).le (ofRows g2_merge12_uarb1_SMAX_c1 g2_merge12_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows g2_merge12_uarb1_FMIN_c1 g2_merge12_uarb1_FMIN_c2) (ofRows g2_merge12_uarb1_SMAX_c1 g2_merge12_uarb1_SMAX_c2)).m1 = -447 ∧
    (mix2 (ofRows g2_merge12_uarb1_FMIN_c1 g2_merge12_uarb1_FMIN_c2) (ofRows g2_merge12_uarb1_SMAX_c1 g2_merge12_uarb1_SMAX_c2)).m2 = -587 := by decide
theorem g2_merge12_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows g2_merge12_uarb1_FMIN_c1 g2_merge12_uarb1_FMIN_c2) (ofRows g2_merge12_uarb1_SMAX_c1 g2_merge12_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 446 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 446 (by decide) (by decide)
theorem g2_merge12_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows g2_merge12_uarb1_FMIN_c1 g2_merge12_uarb1_FMIN_c2) (ofRows g2_merge12_uarb1_SMAX_c1 g2_merge12_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 586 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 586 (by decide) (by decide)
theorem g2_merge12_uarb2_box : (ofRows g2_merge12_uarb2_FMIN_c1 g2_merge12_uarb2_FMIN_c2).le (ofRows g2_merge12_uarb2_SMAX_c1 g2_merge12_uarb2_SMAX_c2) = true ∧ (mix1 (ofRows g2_merge12_uarb2_FMIN_c1 g2_merge12_uarb2_FMIN_c2) (ofRows g2_merge12_uarb2_SMAX_c1 g2_merge12_uarb2_SMAX_c2)).m1 = 131 ∧
    (mix2 (ofRows g2_merge12_uarb2_FMIN_c1 g2_merge12_uarb2_FMIN_c2) (ofRows g2_merge12_uarb2_SMAX_c1 g2_merge12_uarb2_SMAX_c2)).m2 = -402 := by decide
theorem g2_merge12_uarb2_cex2 : ∃ D : Dl, BoxReal2 (ofRows g2_merge12_uarb2_FMIN_c1 g2_merge12_uarb2_FMIN_c2) (ofRows g2_merge12_uarb2_SMAX_c1 g2_merge12_uarb2_SMAX_c2) 0 0 D ∧ D.smin = 401 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 401 (by decide) (by decide)
theorem g2_merge2_uarb1_box : (ofRows g2_merge2_uarb1_FMIN_c1 g2_merge2_uarb1_FMIN_c2).le (ofRows g2_merge2_uarb1_SMAX_c1 g2_merge2_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows g2_merge2_uarb1_FMIN_c1 g2_merge2_uarb1_FMIN_c2) (ofRows g2_merge2_uarb1_SMAX_c1 g2_merge2_uarb1_SMAX_c2)).m1 = -556 ∧
    (mix2 (ofRows g2_merge2_uarb1_FMIN_c1 g2_merge2_uarb1_FMIN_c2) (ofRows g2_merge2_uarb1_SMAX_c1 g2_merge2_uarb1_SMAX_c2)).m2 = -208 := by decide
theorem g2_merge2_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows g2_merge2_uarb1_FMIN_c1 g2_merge2_uarb1_FMIN_c2) (ofRows g2_merge2_uarb1_SMAX_c1 g2_merge2_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 555 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 555 (by decide) (by decide)
theorem g2_merge2_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows g2_merge2_uarb1_FMIN_c1 g2_merge2_uarb1_FMIN_c2) (ofRows g2_merge2_uarb1_SMAX_c1 g2_merge2_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 207 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 207 (by decide) (by decide)
theorem g2_merge3_uarb1_box : (ofRows g2_merge3_uarb1_FMIN_c1 g2_merge3_uarb1_FMIN_c2).le (ofRows g2_merge3_uarb1_SMAX_c1 g2_merge3_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows g2_merge3_uarb1_FMIN_c1 g2_merge3_uarb1_FMIN_c2) (ofRows g2_merge3_uarb1_SMAX_c1 g2_merge3_uarb1_SMAX_c2)).m1 = -165 ∧
    (mix2 (ofRows g2_merge3_uarb1_FMIN_c1 g2_merge3_uarb1_FMIN_c2) (ofRows g2_merge3_uarb1_SMAX_c1 g2_merge3_uarb1_SMAX_c2)).m2 = -494 := by decide
theorem g2_merge3_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows g2_merge3_uarb1_FMIN_c1 g2_merge3_uarb1_FMIN_c2) (ofRows g2_merge3_uarb1_SMAX_c1 g2_merge3_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 164 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 164 (by decide) (by decide)
theorem g2_merge3_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows g2_merge3_uarb1_FMIN_c1 g2_merge3_uarb1_FMIN_c2) (ofRows g2_merge3_uarb1_SMAX_c1 g2_merge3_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 493 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 493 (by decide) (by decide)
theorem g2_merge4_uarb1_box : (ofRows g2_merge4_uarb1_FMIN_c1 g2_merge4_uarb1_FMIN_c2).le (ofRows g2_merge4_uarb1_SMAX_c1 g2_merge4_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows g2_merge4_uarb1_FMIN_c1 g2_merge4_uarb1_FMIN_c2) (ofRows g2_merge4_uarb1_SMAX_c1 g2_merge4_uarb1_SMAX_c2)).m1 = -136 ∧
    (mix2 (ofRows g2_merge4_uarb1_FMIN_c1 g2_merge4_uarb1_FMIN_c2) (ofRows g2_merge4_uarb1_SMAX_c1 g2_merge4_uarb1_SMAX_c2)).m2 = 33 := by decide
theorem g2_merge4_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows g2_merge4_uarb1_FMIN_c1 g2_merge4_uarb1_FMIN_c2) (ofRows g2_merge4_uarb1_SMAX_c1 g2_merge4_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 135 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 135 (by decide) (by decide)
theorem g2_merge6_uarb1_box : (ofRows g2_merge6_uarb1_FMIN_c1 g2_merge6_uarb1_FMIN_c2).le (ofRows g2_merge6_uarb1_SMAX_c1 g2_merge6_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows g2_merge6_uarb1_FMIN_c1 g2_merge6_uarb1_FMIN_c2) (ofRows g2_merge6_uarb1_SMAX_c1 g2_merge6_uarb1_SMAX_c2)).m1 = -137 ∧
    (mix2 (ofRows g2_merge6_uarb1_FMIN_c1 g2_merge6_uarb1_FMIN_c2) (ofRows g2_merge6_uarb1_SMAX_c1 g2_merge6_uarb1_SMAX_c2)).m2 = -339 := by decide
theorem g2_merge6_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows g2_merge6_uarb1_FMIN_c1 g2_merge6_uarb1_FMIN_c2) (ofRows g2_merge6_uarb1_SMAX_c1 g2_merge6_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 136 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 136 (by decide) (by decide)
theorem g2_merge6_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows g2_merge6_uarb1_FMIN_c1 g2_merge6_uarb1_FMIN_c2) (ofRows g2_merge6_uarb1_SMAX_c1 g2_merge6_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 338 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 338 (by decide) (by decide)
theorem g2_merge9_uarb1_box : (ofRows g2_merge9_uarb1_FMIN_c1 g2_merge9_uarb1_FMIN_c2).le (ofRows g2_merge9_uarb1_SMAX_c1 g2_merge9_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows g2_merge9_uarb1_FMIN_c1 g2_merge9_uarb1_FMIN_c2) (ofRows g2_merge9_uarb1_SMAX_c1 g2_merge9_uarb1_SMAX_c2)).m1 = -379 ∧
    (mix2 (ofRows g2_merge9_uarb1_FMIN_c1 g2_merge9_uarb1_FMIN_c2) (ofRows g2_merge9_uarb1_SMAX_c1 g2_merge9_uarb1_SMAX_c2)).m2 = -357 := by decide
theorem g2_merge9_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows g2_merge9_uarb1_FMIN_c1 g2_merge9_uarb1_FMIN_c2) (ofRows g2_merge9_uarb1_SMAX_c1 g2_merge9_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 378 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 378 (by decide) (by decide)
theorem g2_merge9_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows g2_merge9_uarb1_FMIN_c1 g2_merge9_uarb1_FMIN_c2) (ofRows g2_merge9_uarb1_SMAX_c1 g2_merge9_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 356 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 356 (by decide) (by decide)
theorem g3_merge10_uarb1_box : (ofRows g3_merge10_uarb1_FMIN_c1 g3_merge10_uarb1_FMIN_c2).le (ofRows g3_merge10_uarb1_SMAX_c1 g3_merge10_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows g3_merge10_uarb1_FMIN_c1 g3_merge10_uarb1_FMIN_c2) (ofRows g3_merge10_uarb1_SMAX_c1 g3_merge10_uarb1_SMAX_c2)).m1 = -12 ∧
    (mix2 (ofRows g3_merge10_uarb1_FMIN_c1 g3_merge10_uarb1_FMIN_c2) (ofRows g3_merge10_uarb1_SMAX_c1 g3_merge10_uarb1_SMAX_c2)).m2 = -490 := by decide
theorem g3_merge10_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows g3_merge10_uarb1_FMIN_c1 g3_merge10_uarb1_FMIN_c2) (ofRows g3_merge10_uarb1_SMAX_c1 g3_merge10_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 11 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 11 (by decide) (by decide)
theorem g3_merge10_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows g3_merge10_uarb1_FMIN_c1 g3_merge10_uarb1_FMIN_c2) (ofRows g3_merge10_uarb1_SMAX_c1 g3_merge10_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 489 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 489 (by decide) (by decide)
theorem g3_merge11_uarb1_box : (ofRows g3_merge11_uarb1_FMIN_c1 g3_merge11_uarb1_FMIN_c2).le (ofRows g3_merge11_uarb1_SMAX_c1 g3_merge11_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows g3_merge11_uarb1_FMIN_c1 g3_merge11_uarb1_FMIN_c2) (ofRows g3_merge11_uarb1_SMAX_c1 g3_merge11_uarb1_SMAX_c2)).m1 = -437 ∧
    (mix2 (ofRows g3_merge11_uarb1_FMIN_c1 g3_merge11_uarb1_FMIN_c2) (ofRows g3_merge11_uarb1_SMAX_c1 g3_merge11_uarb1_SMAX_c2)).m2 = -305 := by decide
theorem g3_merge11_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows g3_merge11_uarb1_FMIN_c1 g3_merge11_uarb1_FMIN_c2) (ofRows g3_merge11_uarb1_SMAX_c1 g3_merge11_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 436 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 436 (by decide) (by decide)
theorem g3_merge11_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows g3_merge11_uarb1_FMIN_c1 g3_merge11_uarb1_FMIN_c2) (ofRows g3_merge11_uarb1_SMAX_c1 g3_merge11_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 304 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 304 (by decide) (by decide)
theorem g3_merge12_uarb1_box : (ofRows g3_merge12_uarb1_FMIN_c1 g3_merge12_uarb1_FMIN_c2).le (ofRows g3_merge12_uarb1_SMAX_c1 g3_merge12_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows g3_merge12_uarb1_FMIN_c1 g3_merge12_uarb1_FMIN_c2) (ofRows g3_merge12_uarb1_SMAX_c1 g3_merge12_uarb1_SMAX_c2)).m1 = -357 ∧
    (mix2 (ofRows g3_merge12_uarb1_FMIN_c1 g3_merge12_uarb1_FMIN_c2) (ofRows g3_merge12_uarb1_SMAX_c1 g3_merge12_uarb1_SMAX_c2)).m2 = -711 := by decide
theorem g3_merge12_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows g3_merge12_uarb1_FMIN_c1 g3_merge12_uarb1_FMIN_c2) (ofRows g3_merge12_uarb1_SMAX_c1 g3_merge12_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 356 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 356 (by decide) (by decide)
theorem g3_merge12_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows g3_merge12_uarb1_FMIN_c1 g3_merge12_uarb1_FMIN_c2) (ofRows g3_merge12_uarb1_SMAX_c1 g3_merge12_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 710 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 710 (by decide) (by decide)
theorem g3_merge12_uarb2_box : (ofRows g3_merge12_uarb2_FMIN_c1 g3_merge12_uarb2_FMIN_c2).le (ofRows g3_merge12_uarb2_SMAX_c1 g3_merge12_uarb2_SMAX_c2) = true ∧ (mix1 (ofRows g3_merge12_uarb2_FMIN_c1 g3_merge12_uarb2_FMIN_c2) (ofRows g3_merge12_uarb2_SMAX_c1 g3_merge12_uarb2_SMAX_c2)).m1 = -258 ∧
    (mix2 (ofRows g3_merge12_uarb2_FMIN_c1 g3_merge12_uarb2_FMIN_c2) (ofRows g3_merge12_uarb2_SMAX_c1 g3_merge12_uarb2_SMAX_c2)).m2 = -492 := by decide
theorem g3_merge12_uarb2_cex1 : ∃ D : Dl, BoxReal1 (ofRows g3_merge12_uarb2_FMIN_c1 g3_merge12_uarb2_FMIN_c2) (ofRows g3_merge12_uarb2_SMAX_c1 g3_merge12_uarb2_SMAX_c2) 0 0 D ∧ D.smin = 257 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 257 (by decide) (by decide)
theorem g3_merge12_uarb2_cex2 : ∃ D : Dl, BoxReal2 (ofRows g3_merge12_uarb2_FMIN_c1 g3_merge12_uarb2_FMIN_c2) (ofRows g3_merge12_uarb2_SMAX_c1 g3_merge12_uarb2_SMAX_c2) 0 0 D ∧ D.smin = 491 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 491 (by decide) (by decide)
theorem g3_merge2_uarb1_box : (ofRows g3_merge2_uarb1_FMIN_c1 g3_merge2_uarb1_FMIN_c2).le (ofRows g3_merge2_uarb1_SMAX_c1 g3_merge2_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows g3_merge2_uarb1_FMIN_c1 g3_merge2_uarb1_FMIN_c2) (ofRows g3_merge2_uarb1_SMAX_c1 g3_merge2_uarb1_SMAX_c2)).m1 = -278 ∧
    (mix2 (ofRows g3_merge2_uarb1_FMIN_c1 g3_merge2_uarb1_FMIN_c2) (ofRows g3_merge2_uarb1_SMAX_c1 g3_merge2_uarb1_SMAX_c2)).m2 = -75 := by decide
theorem g3_merge2_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows g3_merge2_uarb1_FMIN_c1 g3_merge2_uarb1_FMIN_c2) (ofRows g3_merge2_uarb1_SMAX_c1 g3_merge2_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 277 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 277 (by decide) (by decide)
theorem g3_merge2_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows g3_merge2_uarb1_FMIN_c1 g3_merge2_uarb1_FMIN_c2) (ofRows g3_merge2_uarb1_SMAX_c1 g3_merge2_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 74 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 74 (by decide) (by decide)
theorem g3_merge3_uarb1_box : (ofRows g3_merge3_uarb1_FMIN_c1 g3_merge3_uarb1_FMIN_c2).le (ofRows g3_merge3_uarb1_SMAX_c1 g3_merge3_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows g3_merge3_uarb1_FMIN_c1 g3_merge3_uarb1_FMIN_c2) (ofRows g3_merge3_uarb1_SMAX_c1 g3_merge3_uarb1_SMAX_c2)).m1 = -389 ∧
    (mix2 (ofRows g3_merge3_uarb1_FMIN_c1 g3_merge3_uarb1_FMIN_c2) (ofRows g3_merge3_uarb1_SMAX_c1 g3_merge3_uarb1_SMAX_c2)).m2 = -178 := by decide
theorem g3_merge3_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows g3_merge3_uarb1_FMIN_c1 g3_merge3_uarb1_FMIN_c2) (ofRows g3_merge3_uarb1_SMAX_c1 g3_merge3_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 388 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 388 (by decide) (by decide)
theorem g3_merge3_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows g3_merge3_uarb1_FMIN_c1 g3_merge3_uarb1_FMIN_c2) (ofRows g3_merge3_uarb1_SMAX_c1 g3_merge3_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 177 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 177 (by decide) (by decide)
theorem g3_merge4_uarb1_box : (ofRows g3_merge4_uarb1_FMIN_c1 g3_merge4_uarb1_FMIN_c2).le (ofRows g3_merge4_uarb1_SMAX_c1 g3_merge4_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows g3_merge4_uarb1_FMIN_c1 g3_merge4_uarb1_FMIN_c2) (ofRows g3_merge4_uarb1_SMAX_c1 g3_merge4_uarb1_SMAX_c2)).m1 = -43 ∧
    (mix2 (ofRows g3_merge4_uarb1_FMIN_c1 g3_merge4_uarb1_FMIN_c2) (ofRows g3_merge4_uarb1_SMAX_c1 g3_merge4_uarb1_SMAX_c2)).m2 = -234 := by decide
theorem g3_merge4_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows g3_merge4_uarb1_FMIN_c1 g3_merge4_uarb1_FMIN_c2) (ofRows g3_merge4_uarb1_SMAX_c1 g3_merge4_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 42 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 42 (by decide) (by decide)
theorem g3_merge4_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows g3_merge4_uarb1_FMIN_c1 g3_merge4_uarb1_FMIN_c2) (ofRows g3_merge4_uarb1_SMAX_c1 g3_merge4_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 233 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 233 (by decide) (by decide)
theorem g3_merge6_uarb1_box : (ofRows g3_merge6_uarb1_FMIN_c1 g3_merge6_uarb1_FMIN_c2).le (ofRows g3_merge6_uarb1_SMAX_c1 g3_merge6_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows g3_merge6_uarb1_FMIN_c1 g3_merge6_uarb1_FMIN_c2) (ofRows g3_merge6_uarb1_SMAX_c1 g3_merge6_uarb1_SMAX_c2)).m1 = -99 ∧
    (mix2 (ofRows g3_merge6_uarb1_FMIN_c1 g3_merge6_uarb1_FMIN_c2) (ofRows g3_merge6_uarb1_SMAX_c1 g3_merge6_uarb1_SMAX_c2)).m2 = -100 := by decide
theorem g3_merge6_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows g3_merge6_uarb1_FMIN_c1 g3_merge6_uarb1_FMIN_c2) (ofRows g3_merge6_uarb1_SMAX_c1 g3_merge6_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 98 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 98 (by decide) (by decide)
theorem g3_merge6_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows g3_merge6_uarb1_FMIN_c1 g3_merge6_uarb1_FMIN_c2) (ofRows g3_merge6_uarb1_SMAX_c1 g3_merge6_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 99 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 99 (by decide) (by decide)
theorem g3_merge9_uarb1_box : (ofRows g3_merge9_uarb1_FMIN_c1 g3_merge9_uarb1_FMIN_c2).le (ofRows g3_merge9_uarb1_SMAX_c1 g3_merge9_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows g3_merge9_uarb1_FMIN_c1 g3_merge9_uarb1_FMIN_c2) (ofRows g3_merge9_uarb1_SMAX_c1 g3_merge9_uarb1_SMAX_c2)).m1 = -380 ∧
    (mix2 (ofRows g3_merge9_uarb1_FMIN_c1 g3_merge9_uarb1_FMIN_c2) (ofRows g3_merge9_uarb1_SMAX_c1 g3_merge9_uarb1_SMAX_c2)).m2 = -401 := by decide
theorem g3_merge9_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows g3_merge9_uarb1_FMIN_c1 g3_merge9_uarb1_FMIN_c2) (ofRows g3_merge9_uarb1_SMAX_c1 g3_merge9_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 379 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 379 (by decide) (by decide)
theorem g3_merge9_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows g3_merge9_uarb1_FMIN_c1 g3_merge9_uarb1_FMIN_c2) (ofRows g3_merge9_uarb1_SMAX_c1 g3_merge9_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 400 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 400 (by decide) (by decide)
theorem g4_merge10_uarb1_box : (ofRows g4_merge10_uarb1_FMIN_c1 g4_merge10_uarb1_FMIN_c2).le (ofRows g4_merge10_uarb1_SMAX_c1 g4_merge10_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows g4_merge10_uarb1_FMIN_c1 g4_merge10_uarb1_FMIN_c2) (ofRows g4_merge10_uarb1_SMAX_c1 g4_merge10_uarb1_SMAX_c2)).m1 = -144 ∧
    (mix2 (ofRows g4_merge10_uarb1_FMIN_c1 g4_merge10_uarb1_FMIN_c2) (ofRows g4_merge10_uarb1_SMAX_c1 g4_merge10_uarb1_SMAX_c2)).m2 = -81 := by decide
theorem g4_merge10_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows g4_merge10_uarb1_FMIN_c1 g4_merge10_uarb1_FMIN_c2) (ofRows g4_merge10_uarb1_SMAX_c1 g4_merge10_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 143 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 143 (by decide) (by decide)
theorem g4_merge10_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows g4_merge10_uarb1_FMIN_c1 g4_merge10_uarb1_FMIN_c2) (ofRows g4_merge10_uarb1_SMAX_c1 g4_merge10_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 80 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 80 (by decide) (by decide)
theorem g4_merge11_uarb1_box : (ofRows g4_merge11_uarb1_FMIN_c1 g4_merge11_uarb1_FMIN_c2).le (ofRows g4_merge11_uarb1_SMAX_c1 g4_merge11_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows g4_merge11_uarb1_FMIN_c1 g4_merge11_uarb1_FMIN_c2) (ofRows g4_merge11_uarb1_SMAX_c1 g4_merge11_uarb1_SMAX_c2)).m1 = -394 ∧
    (mix2 (ofRows g4_merge11_uarb1_FMIN_c1 g4_merge11_uarb1_FMIN_c2) (ofRows g4_merge11_uarb1_SMAX_c1 g4_merge11_uarb1_SMAX_c2)).m2 = -264 := by decide
theorem g4_merge11_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows g4_merge11_uarb1_FMIN_c1 g4_merge11_uarb1_FMIN_c2) (ofRows g4_merge11_uarb1_SMAX_c1 g4_merge11_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 393 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 393 (by decide) (by decide)
theorem g4_merge11_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows g4_merge11_uarb1_FMIN_c1 g4_merge11_uarb1_FMIN_c2) (ofRows g4_merge11_uarb1_SMAX_c1 g4_merge11_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 263 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 263 (by decide) (by decide)
theorem g4_merge12_uarb1_box : (ofRows g4_merge12_uarb1_FMIN_c1 g4_merge12_uarb1_FMIN_c2).le (ofRows g4_merge12_uarb1_SMAX_c1 g4_merge12_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows g4_merge12_uarb1_FMIN_c1 g4_merge12_uarb1_FMIN_c2) (ofRows g4_merge12_uarb1_SMAX_c1 g4_merge12_uarb1_SMAX_c2)).m1 = -490 ∧
    (mix2 (ofRows g4_merge12_uarb1_FMIN_c1 g4_merge12_uarb1_FMIN_c2) (ofRows g4_merge12_uarb1_SMAX_c1 g4_merge12_uarb1_SMAX_c2)).m2 = -441 := by decide
theorem g4_merge12_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows g4_merge12_uarb1_FMIN_c1 g4_merge12_uarb1_FMIN_c2) (ofRows g4_merge12_uarb1_SMAX_c1 g4_merge12_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 489 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 489 (by decide) (by decide)
theorem g4_merge12_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows g4_merge12_uarb1_FMIN_c1 g4_merge12_uarb1_FMIN_c2) (ofRows g4_merge12_uarb1_SMAX_c1 g4_merge12_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 440 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 440 (by decide) (by decide)
theorem g4_merge12_uarb2_box : (ofRows g4_merge12_uarb2_FMIN_c1 g4_merge12_uarb2_FMIN_c2).le (ofRows g4_merge12_uarb2_SMAX_c1 g4_merge12_uarb2_SMAX_c2) = true ∧ (mix1 (ofRows g4_merge12_uarb2_FMIN_c1 g4_merge12_uarb2_FMIN_c2) (ofRows g4_merge12_uarb2_SMAX_c1 g4_merge12_uarb2_SMAX_c2)).m1 = 93 ∧
    (mix2 (ofRows g4_merge12_uarb2_FMIN_c1 g4_merge12_uarb2_FMIN_c2) (ofRows g4_merge12_uarb2_SMAX_c1 g4_merge12_uarb2_SMAX_c2)).m2 = -386 := by decide
theorem g4_merge12_uarb2_cex2 : ∃ D : Dl, BoxReal2 (ofRows g4_merge12_uarb2_FMIN_c1 g4_merge12_uarb2_FMIN_c2) (ofRows g4_merge12_uarb2_SMAX_c1 g4_merge12_uarb2_SMAX_c2) 0 0 D ∧ D.smin = 385 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 385 (by decide) (by decide)
theorem g4_merge2_uarb1_box : (ofRows g4_merge2_uarb1_FMIN_c1 g4_merge2_uarb1_FMIN_c2).le (ofRows g4_merge2_uarb1_SMAX_c1 g4_merge2_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows g4_merge2_uarb1_FMIN_c1 g4_merge2_uarb1_FMIN_c2) (ofRows g4_merge2_uarb1_SMAX_c1 g4_merge2_uarb1_SMAX_c2)).m1 = 167 ∧
    (mix2 (ofRows g4_merge2_uarb1_FMIN_c1 g4_merge2_uarb1_FMIN_c2) (ofRows g4_merge2_uarb1_SMAX_c1 g4_merge2_uarb1_SMAX_c2)).m2 = -525 := by decide
theorem g4_merge2_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows g4_merge2_uarb1_FMIN_c1 g4_merge2_uarb1_FMIN_c2) (ofRows g4_merge2_uarb1_SMAX_c1 g4_merge2_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 524 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 524 (by decide) (by decide)
theorem g4_merge3_uarb1_box : (ofRows g4_merge3_uarb1_FMIN_c1 g4_merge3_uarb1_FMIN_c2).le (ofRows g4_merge3_uarb1_SMAX_c1 g4_merge3_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows g4_merge3_uarb1_FMIN_c1 g4_merge3_uarb1_FMIN_c2) (ofRows g4_merge3_uarb1_SMAX_c1 g4_merge3_uarb1_SMAX_c2)).m1 = -408 ∧
    (mix2 (ofRows g4_merge3_uarb1_FMIN_c1 g4_merge3_uarb1_FMIN_c2) (ofRows g4_merge3_uarb1_SMAX_c1 g4_merge3_uarb1_SMAX_c2)).m2 = 190 := by decide
theorem g4_merge3_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows g4_merge3_uarb1_FMIN_c1 g4_merge3_uarb1_FMIN_c2) (ofRows g4_merge3_uarb1_SMAX_c1 g4_merge3_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 407 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 407 (by decide) (by decide)
theorem g4_merge4_uarb1_box : (ofRows g4_merge4_uarb1_FMIN_c1 g4_merge4_uarb1_FMIN_c2).le (ofRows g4_merge4_uarb1_SMAX_c1 g4_merge4_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows g4_merge4_uarb1_FMIN_c1 g4_merge4_uarb1_FMIN_c2) (ofRows g4_merge4_uarb1_SMAX_c1 g4_merge4_uarb1_SMAX_c2)).m1 = -421 ∧
    (mix2 (ofRows g4_merge4_uarb1_FMIN_c1 g4_merge4_uarb1_FMIN_c2) (ofRows g4_merge4_uarb1_SMAX_c1 g4_merge4_uarb1_SMAX_c2)).m2 = -299 := by decide
theorem g4_merge4_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows g4_merge4_uarb1_FMIN_c1 g4_merge4_uarb1_FMIN_c2) (ofRows g4_merge4_uarb1_SMAX_c1 g4_merge4_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 420 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 420 (by decide) (by decide)
theorem g4_merge4_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows g4_merge4_uarb1_FMIN_c1 g4_merge4_uarb1_FMIN_c2) (ofRows g4_merge4_uarb1_SMAX_c1 g4_merge4_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 298 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 298 (by decide) (by decide)
theorem g4_merge6_uarb1_box : (ofRows g4_merge6_uarb1_FMIN_c1 g4_merge6_uarb1_FMIN_c2).le (ofRows g4_merge6_uarb1_SMAX_c1 g4_merge6_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows g4_merge6_uarb1_FMIN_c1 g4_merge6_uarb1_FMIN_c2) (ofRows g4_merge6_uarb1_SMAX_c1 g4_merge6_uarb1_SMAX_c2)).m1 = -280 ∧
    (mix2 (ofRows g4_merge6_uarb1_FMIN_c1 g4_merge6_uarb1_FMIN_c2) (ofRows g4_merge6_uarb1_SMAX_c1 g4_merge6_uarb1_SMAX_c2)).m2 = -215 := by decide
theorem g4_merge6_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows g4_merge6_uarb1_FMIN_c1 g4_merge6_uarb1_FMIN_c2) (ofRows g4_merge6_uarb1_SMAX_c1 g4_merge6_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 279 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 279 (by decide) (by decide)
theorem g4_merge6_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows g4_merge6_uarb1_FMIN_c1 g4_merge6_uarb1_FMIN_c2) (ofRows g4_merge6_uarb1_SMAX_c1 g4_merge6_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 214 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 214 (by decide) (by decide)
theorem g4_merge9_uarb1_box : (ofRows g4_merge9_uarb1_FMIN_c1 g4_merge9_uarb1_FMIN_c2).le (ofRows g4_merge9_uarb1_SMAX_c1 g4_merge9_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows g4_merge9_uarb1_FMIN_c1 g4_merge9_uarb1_FMIN_c2) (ofRows g4_merge9_uarb1_SMAX_c1 g4_merge9_uarb1_SMAX_c2)).m1 = -162 ∧
    (mix2 (ofRows g4_merge9_uarb1_FMIN_c1 g4_merge9_uarb1_FMIN_c2) (ofRows g4_merge9_uarb1_SMAX_c1 g4_merge9_uarb1_SMAX_c2)).m2 = -281 := by decide
theorem g4_merge9_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows g4_merge9_uarb1_FMIN_c1 g4_merge9_uarb1_FMIN_c2) (ofRows g4_merge9_uarb1_SMAX_c1 g4_merge9_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 161 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 161 (by decide) (by decide)
theorem g4_merge9_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows g4_merge9_uarb1_FMIN_c1 g4_merge9_uarb1_FMIN_c2) (ofRows g4_merge9_uarb1_SMAX_c1 g4_merge9_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 280 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 280 (by decide) (by decide)
theorem gd_merge10_uarb1_box : (ofRows gd_merge10_uarb1_FMIN_c1 gd_merge10_uarb1_FMIN_c2).le (ofRows gd_merge10_uarb1_SMAX_c1 gd_merge10_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows gd_merge10_uarb1_FMIN_c1 gd_merge10_uarb1_FMIN_c2) (ofRows gd_merge10_uarb1_SMAX_c1 gd_merge10_uarb1_SMAX_c2)).m1 = -44 ∧
    (mix2 (ofRows gd_merge10_uarb1_FMIN_c1 gd_merge10_uarb1_FMIN_c2) (ofRows gd_merge10_uarb1_SMAX_c1 gd_merge10_uarb1_SMAX_c2)).m2 = -52 := by decide
theorem gd_merge10_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows gd_merge10_uarb1_FMIN_c1 gd_merge10_uarb1_FMIN_c2) (ofRows gd_merge10_uarb1_SMAX_c1 gd_merge10_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 43 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 43 (by decide) (by decide)
theorem gd_merge10_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows gd_merge10_uarb1_FMIN_c1 gd_merge10_uarb1_FMIN_c2) (ofRows gd_merge10_uarb1_SMAX_c1 gd_merge10_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 51 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 51 (by decide) (by decide)
theorem gd_merge11_uarb1_box : (ofRows gd_merge11_uarb1_FMIN_c1 gd_merge11_uarb1_FMIN_c2).le (ofRows gd_merge11_uarb1_SMAX_c1 gd_merge11_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows gd_merge11_uarb1_FMIN_c1 gd_merge11_uarb1_FMIN_c2) (ofRows gd_merge11_uarb1_SMAX_c1 gd_merge11_uarb1_SMAX_c2)).m1 = -472 ∧
    (mix2 (ofRows gd_merge11_uarb1_FMIN_c1 gd_merge11_uarb1_FMIN_c2) (ofRows gd_merge11_uarb1_SMAX_c1 gd_merge11_uarb1_SMAX_c2)).m2 = -62 := by decide
theorem gd_merge11_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows gd_merge11_uarb1_FMIN_c1 gd_merge11_uarb1_FMIN_c2) (ofRows gd_merge11_uarb1_SMAX_c1 gd_merge11_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 471 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 471 (by decide) (by decide)
theorem gd_merge11_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows gd_merge11_uarb1_FMIN_c1 gd_merge11_uarb1_FMIN_c2) (ofRows gd_merge11_uarb1_SMAX_c1 gd_merge11_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 61 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 61 (by decide) (by decide)
theorem gd_merge12_uarb1_box : (ofRows gd_merge12_uarb1_FMIN_c1 gd_merge12_uarb1_FMIN_c2).le (ofRows gd_merge12_uarb1_SMAX_c1 gd_merge12_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows gd_merge12_uarb1_FMIN_c1 gd_merge12_uarb1_FMIN_c2) (ofRows gd_merge12_uarb1_SMAX_c1 gd_merge12_uarb1_SMAX_c2)).m1 = -132 ∧
    (mix2 (ofRows gd_merge12_uarb1_FMIN_c1 gd_merge12_uarb1_FMIN_c2) (ofRows gd_merge12_uarb1_SMAX_c1 gd_merge12_uarb1_SMAX_c2)).m2 = -287 := by decide
theorem gd_merge12_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows gd_merge12_uarb1_FMIN_c1 gd_merge12_uarb1_FMIN_c2) (ofRows gd_merge12_uarb1_SMAX_c1 gd_merge12_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 131 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 131 (by decide) (by decide)
theorem gd_merge12_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows gd_merge12_uarb1_FMIN_c1 gd_merge12_uarb1_FMIN_c2) (ofRows gd_merge12_uarb1_SMAX_c1 gd_merge12_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 286 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 286 (by decide) (by decide)
theorem gd_merge12_uarb2_box : (ofRows gd_merge12_uarb2_FMIN_c1 gd_merge12_uarb2_FMIN_c2).le (ofRows gd_merge12_uarb2_SMAX_c1 gd_merge12_uarb2_SMAX_c2) = true ∧ (mix1 (ofRows gd_merge12_uarb2_FMIN_c1 gd_merge12_uarb2_FMIN_c2) (ofRows gd_merge12_uarb2_SMAX_c1 gd_merge12_uarb2_SMAX_c2)).m1 = -339 ∧
    (mix2 (ofRows gd_merge12_uarb2_FMIN_c1 gd_merge12_uarb2_FMIN_c2) (ofRows gd_merge12_uarb2_SMAX_c1 gd_merge12_uarb2_SMAX_c2)).m2 = -563 := by decide
theorem gd_merge12_uarb2_cex1 : ∃ D : Dl, BoxReal1 (ofRows gd_merge12_uarb2_FMIN_c1 gd_merge12_uarb2_FMIN_c2) (ofRows gd_merge12_uarb2_SMAX_c1 gd_merge12_uarb2_SMAX_c2) 0 0 D ∧ D.smin = 338 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 338 (by decide) (by decide)
theorem gd_merge12_uarb2_cex2 : ∃ D : Dl, BoxReal2 (ofRows gd_merge12_uarb2_FMIN_c1 gd_merge12_uarb2_FMIN_c2) (ofRows gd_merge12_uarb2_SMAX_c1 gd_merge12_uarb2_SMAX_c2) 0 0 D ∧ D.smin = 562 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 562 (by decide) (by decide)
theorem gd_merge2_uarb1_box : (ofRows gd_merge2_uarb1_FMIN_c1 gd_merge2_uarb1_FMIN_c2).le (ofRows gd_merge2_uarb1_SMAX_c1 gd_merge2_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows gd_merge2_uarb1_FMIN_c1 gd_merge2_uarb1_FMIN_c2) (ofRows gd_merge2_uarb1_SMAX_c1 gd_merge2_uarb1_SMAX_c2)).m1 = -394 ∧
    (mix2 (ofRows gd_merge2_uarb1_FMIN_c1 gd_merge2_uarb1_FMIN_c2) (ofRows gd_merge2_uarb1_SMAX_c1 gd_merge2_uarb1_SMAX_c2)).m2 = -345 := by decide
theorem gd_merge2_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows gd_merge2_uarb1_FMIN_c1 gd_merge2_uarb1_FMIN_c2) (ofRows gd_merge2_uarb1_SMAX_c1 gd_merge2_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 393 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 393 (by decide) (by decide)
theorem gd_merge2_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows gd_merge2_uarb1_FMIN_c1 gd_merge2_uarb1_FMIN_c2) (ofRows gd_merge2_uarb1_SMAX_c1 gd_merge2_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 344 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 344 (by decide) (by decide)
theorem gd_merge3_uarb1_box : (ofRows gd_merge3_uarb1_FMIN_c1 gd_merge3_uarb1_FMIN_c2).le (ofRows gd_merge3_uarb1_SMAX_c1 gd_merge3_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows gd_merge3_uarb1_FMIN_c1 gd_merge3_uarb1_FMIN_c2) (ofRows gd_merge3_uarb1_SMAX_c1 gd_merge3_uarb1_SMAX_c2)).m1 = -420 ∧
    (mix2 (ofRows gd_merge3_uarb1_FMIN_c1 gd_merge3_uarb1_FMIN_c2) (ofRows gd_merge3_uarb1_SMAX_c1 gd_merge3_uarb1_SMAX_c2)).m2 = -38 := by decide
theorem gd_merge3_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows gd_merge3_uarb1_FMIN_c1 gd_merge3_uarb1_FMIN_c2) (ofRows gd_merge3_uarb1_SMAX_c1 gd_merge3_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 419 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 419 (by decide) (by decide)
theorem gd_merge3_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows gd_merge3_uarb1_FMIN_c1 gd_merge3_uarb1_FMIN_c2) (ofRows gd_merge3_uarb1_SMAX_c1 gd_merge3_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 37 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 37 (by decide) (by decide)
theorem gd_merge4_uarb1_box : (ofRows gd_merge4_uarb1_FMIN_c1 gd_merge4_uarb1_FMIN_c2).le (ofRows gd_merge4_uarb1_SMAX_c1 gd_merge4_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows gd_merge4_uarb1_FMIN_c1 gd_merge4_uarb1_FMIN_c2) (ofRows gd_merge4_uarb1_SMAX_c1 gd_merge4_uarb1_SMAX_c2)).m1 = -139 ∧
    (mix2 (ofRows gd_merge4_uarb1_FMIN_c1 gd_merge4_uarb1_FMIN_c2) (ofRows gd_merge4_uarb1_SMAX_c1 gd_merge4_uarb1_SMAX_c2)).m2 = -233 := by decide
theorem gd_merge4_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows gd_merge4_uarb1_FMIN_c1 gd_merge4_uarb1_FMIN_c2) (ofRows gd_merge4_uarb1_SMAX_c1 gd_merge4_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 138 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 138 (by decide) (by decide)
theorem gd_merge4_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows gd_merge4_uarb1_FMIN_c1 gd_merge4_uarb1_FMIN_c2) (ofRows gd_merge4_uarb1_SMAX_c1 gd_merge4_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 232 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 232 (by decide) (by decide)
theorem gd_merge6_uarb1_box : (ofRows gd_merge6_uarb1_FMIN_c1 gd_merge6_uarb1_FMIN_c2).le (ofRows gd_merge6_uarb1_SMAX_c1 gd_merge6_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows gd_merge6_uarb1_FMIN_c1 gd_merge6_uarb1_FMIN_c2) (ofRows gd_merge6_uarb1_SMAX_c1 gd_merge6_uarb1_SMAX_c2)).m1 = -20 ∧
    (mix2 (ofRows gd_merge6_uarb1_FMIN_c1 gd_merge6_uarb1_FMIN_c2) (ofRows gd_merge6_uarb1_SMAX_c1 gd_merge6_uarb1_SMAX_c2)).m2 = 174 := by decide
theorem gd_merge6_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows gd_merge6_uarb1_FMIN_c1 gd_merge6_uarb1_FMIN_c2) (ofRows gd_merge6_uarb1_SMAX_c1 gd_merge6_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 19 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 19 (by decide) (by decide)
theorem gd_merge9_uarb1_box : (ofRows gd_merge9_uarb1_FMIN_c1 gd_merge9_uarb1_FMIN_c2).le (ofRows gd_merge9_uarb1_SMAX_c1 gd_merge9_uarb1_SMAX_c2) = true ∧ (mix1 (ofRows gd_merge9_uarb1_FMIN_c1 gd_merge9_uarb1_FMIN_c2) (ofRows gd_merge9_uarb1_SMAX_c1 gd_merge9_uarb1_SMAX_c2)).m1 = -395 ∧
    (mix2 (ofRows gd_merge9_uarb1_FMIN_c1 gd_merge9_uarb1_FMIN_c2) (ofRows gd_merge9_uarb1_SMAX_c1 gd_merge9_uarb1_SMAX_c2)).m2 = -398 := by decide
theorem gd_merge9_uarb1_cex1 : ∃ D : Dl, BoxReal1 (ofRows gd_merge9_uarb1_FMIN_c1 gd_merge9_uarb1_FMIN_c2) (ofRows gd_merge9_uarb1_SMAX_c1 gd_merge9_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 394 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 394 (by decide) (by decide)
theorem gd_merge9_uarb1_cex2 : ∃ D : Dl, BoxReal2 (ofRows gd_merge9_uarb1_FMIN_c1 gd_merge9_uarb1_FMIN_c2) (ofRows gd_merge9_uarb1_SMAX_c1 gd_merge9_uarb1_SMAX_c2) 0 0 D ∧ D.smin = 397 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 397 (by decide) (by decide)

end Formal.Cells.OnGcdArb
