import Formal.Cells.ArbHeldTimed2

/-!
# Probe Bag2: RT1 / RT1b on the 36 routed gcd_hw arbiters, with the corrected net split

Shard B, 2026-10-27. Core Lean (no Mathlib). Note: `formal/notes/B-gcd-arb-fix.md`.
Re-does probe Bag (`Formal/Cells/OnGcdArb.lean`) on rows that do NOT come from shard C's
`Formal/Timing/RuntAckInst.lean`. That file is not imported.

## Why
Probe Bar (`notes/B-gcd-arb-a0.md`, finding 1) found that tcheck's `Prjx.split` (as used
by C-10i/10j's `grantfork`/`runtack` extractors, which produced RuntAckInst) mis-splits a
net whose driver leaves its site through TWO site pins (LUT O6 on both X and XMUX): the
two sinks are then on different RC nets, nothing is shared, yet the old split counted
sink a's driver-side OUTMUX hop as shared prefix and dropped sink b's. On these routes
four r_k nets are affected (seed 2 merge10.uarb1 r1; seed 2 merge2.uarb1, seed 4
merge10.uarb1, seed d merge10.uarb1 r2).

## Where the numbers come from (UNTRUSTED extraction)
Every `Q` below is generated (scratchpad `Bag2/gen.py`) from probe Bar's extraction
`Bar/out/part_{2,3,4,d}.json` (`Bar/a0extract.py`: tcheck's prjxray RC tree over the
FASM's ON pips of C-10e's four routes, rebuilt byte-identical to `results/sha_*.txt`,
with the CORRECTED split; physical pins from X_ORIG_PORT; INITs and connectivity
checked against the RTL; flat O6 arcs checked). Field map, client k:
* `drg k` = `rg_k` (r_k suffix to ugrant's pin, incl. site pin and, if the sinks are on
  different site pins of the driver, its own driver hop);
* `drs k` = `rs_k` (r_k suffix to ustate's pin; the LUT5 and LUT6 halves share it, checked);
* `agr 1` = `ag1r`, `agr 2` = `ag2`, `aRr k` = `aR_k`, `agq 1` = `ag1q`, `agq 2` = `ag2`
  (ugrant O6 is flat over its q / r2 pins, checked);
* `dqg` = `qgw + pqg` (q suffix to ugrant incl. site pin).

## Rounding
Each corner row is the integer hull `[⌊v⌋, ⌈v⌉]` of the extracted value (H_ONE_CORNER +
rounding hull, as Bar). RT1 is proved for EVERY record in the hull (worst point `mix1`),
so no rounding direction is assumed. (C's RuntAckInst rounds per field for C's own
certificate: `dqg`, `agq` up and `drg`, `agr` down, which is the optimistic direction for
RT1; Bag's margins inherited up to 3 ps of that.) The box row is `[⌊FMIN⌋, ⌈SMAX⌉]`.

## Named hypotheses
* H_ONE_CORNER (+ rounding hull): every delay RT1 reads is in its corner's `[⌊v⌋, ⌈v⌉]`.
* H_R_SHARED (`cr`, any value, in both sums) and H_Q_PREFIX (`cq ≥ 0`), as in Bag.
* 7h/7j's model: `Run`, `Scn`/`Scn2`, any server `smin ≥ 0`; H_FLAT_O6.
* UNTRUSTED extraction (Bar's `a0extract.py`).

## NOT covered
The A0 fork and RT2 (Bar's `OnGcdArbA0`), the rise/fall split, metastability.
-/
namespace Formal.Cells.OnGcdArbFix

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

/-! ## Corner rows: the rounding hull, checked by the kernel -/

/-- A hull row `[lo, hi]` passes: ordered, non-negative at the worst points, and both
worst-point server-free margins `≥ 0`. -/
def okRow (lo hi : Q) : Bool :=
  lo.le hi && lo.nn && (mix1 lo hi).nn && (mix2 lo hi).nn &&
    decide (0 ≤ (mix1 lo hi).m1) && decide (0 ≤ (mix2 lo hi).m2)

theorem okRow_sound (lo hi : Q) (h : okRow lo hi = true) :
    lo.le hi = true ∧ (mix1 lo hi).nn = true ∧ (mix2 lo hi).nn = true ∧
      0 ≤ (mix1 lo hi).m1 ∧ 0 ≤ (mix2 lo hi).m2 := by
  unfold okRow at h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- RT1 for every record in the hull, for every server, A0 branch, ustate O6 arc and
q prefix, once the worst-point margin is `≥ 0`. -/
theorem hull_rt1 (lo hi : Q) (hm : 0 ≤ (mix1 lo hi).m1) {cr cq : Int} {D : Dl}
    (h : BoxReal1 lo hi cr cq D) : RT1 D := by
  have hn := D.H_NONNEG; have hr := D.H_RISE_LE_FALL; have hc := h.1
  exact box_rt1 lo hi cr cq D h (by omega)

theorem hull_rt1b (lo hi : Q) (hm : 0 ≤ (mix2 lo hi).m2) {cr cq : Int} {D : Dl}
    (h : BoxReal2 lo hi cr cq D) : RT1b D := by
  have hn := D.H_NONNEG; have hr := D.H_RISE_LE_FALL; have hc := h.1
  exact box_rt1b lo hi cr cq D h (by omega)

/-- **Grant exclusion across a client-1 release** (7h `rt1_exclusion`) on a hull row. -/
theorem hull_excl1 (lo hi : Q) (hm : 0 ≤ (mix1 lo hi).m1) {D : Dl} {s : Sigs}
    {t0 ta TA TA2 Hz cr cq : Int} (h : BoxReal1 lo hi cr cq D) (R : Run D s)
    (S : Scn D s t0 ta TA TA2 Hz) : ∀ t, t < Hz → (s.g1 t && s.g2 t) = false :=
  rt1_exclusion R S (hull_rt1 lo hi hm h)

/-- **Grant exclusion across a client-2 release** (7j `rt1_exclusion2`) on a hull row. -/
theorem hull_excl2 (lo hi : Q) (hm : 0 ≤ (mix2 lo hi).m2) {D : Dl} {s : Sigs}
    {t0 ta TA TA2 Hz cr cq : Int} (h : BoxReal2 lo hi cr cq D) (R : Run D s)
    (S : Scn2 D s t0 ta TA TA2 Hz) : ∀ t, t < Hz → (s.g1 t && s.g2 t) = false :=
  rt1_exclusion2 R S (hull_rt1b lo hi hm h)


/-! ## Data: per seed x arbiter x corner, the hull `[lo, hi]` (ps; generated) -/

def g2_merge10_uarb1_FMIN_lo : Q := { dqg := 267, drg1 := 388, drs1 := 246, agr1 := 43, aRr1 := 46, agq1 := 44, drg2 := 145, drs2 := 241, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g2_merge10_uarb1_FMIN_hi : Q := { dqg := 268, drg1 := 389, drs1 := 247, agr1 := 43, aRr1 := 46, agq1 := 44, drg2 := 145, drs2 := 242, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g2_merge10_uarb1_FMAX_lo : Q := { dqg := 326, drg1 := 467, drs1 := 318, agr1 := 55, aRr1 := 61, agq1 := 56, drg2 := 180, drs2 := 339, agr2 := 56, aRr2 := 58, agq2 := 56 }
def g2_merge10_uarb1_FMAX_hi : Q := { dqg := 327, drg1 := 468, drs1 := 319, agr1 := 55, aRr1 := 61, agq1 := 56, drg2 := 180, drs2 := 340, agr2 := 56, aRr2 := 58, agq2 := 56 }
def g2_merge10_uarb1_SMIN_lo : Q := { dqg := 667, drg1 := 859, drs1 := 558, agr1 := 121, aRr1 := 120, agq1 := 120, drg2 := 392, drs2 := 557, agr2 := 100, aRr2 := 121, agq2 := 100 }
def g2_merge10_uarb1_SMIN_hi : Q := { dqg := 668, drg1 := 860, drs1 := 559, agr1 := 121, aRr1 := 120, agq1 := 120, drg2 := 392, drs2 := 558, agr2 := 100, aRr2 := 121, agq2 := 100 }
def g2_merge10_uarb1_SMAX_lo : Q := { dqg := 815, drg1 := 1045, drs1 := 767, agr1 := 154, aRr1 := 153, agq1 := 154, drg2 := 482, drs2 := 840, agr2 := 124, aRr2 := 156, agq2 := 124 }
def g2_merge10_uarb1_SMAX_hi : Q := { dqg := 816, drg1 := 1046, drs1 := 768, agr1 := 154, aRr1 := 153, agq1 := 154, drg2 := 482, drs2 := 841, agr2 := 124, aRr2 := 156, agq2 := 124 }
def g2_merge11_uarb1_FMIN_lo : Q := { dqg := 439, drg1 := 271, drs1 := 734, agr1 := 43, aRr1 := 44, agq1 := 48, drg2 := 276, drs2 := 503, agr2 := 45, aRr2 := 48, agq2 := 45 }
def g2_merge11_uarb1_FMIN_hi : Q := { dqg := 440, drg1 := 272, drs1 := 735, agr1 := 43, aRr1 := 44, agq1 := 48, drg2 := 277, drs2 := 504, agr2 := 45, aRr2 := 48, agq2 := 45 }
def g2_merge11_uarb1_FMAX_lo : Q := { dqg := 501, drg1 := 329, drs1 := 859, agr1 := 55, aRr1 := 58, agq1 := 61, drg2 := 338, drs2 := 580, agr2 := 56, aRr2 := 61, agq2 := 56 }
def g2_merge11_uarb1_FMAX_hi : Q := { dqg := 502, drg1 := 330, drs1 := 860, agr1 := 55, aRr1 := 58, agq1 := 61, drg2 := 339, drs2 := 581, agr2 := 56, aRr2 := 61, agq2 := 56 }
def g2_merge11_uarb1_SMIN_lo : Q := { dqg := 880, drg1 := 696, drs1 := 1514, agr1 := 120, aRr1 := 121, agq1 := 93, drg2 := 669, drs2 := 1055, agr2 := 100, aRr2 := 93, agq2 := 100 }
def g2_merge11_uarb1_SMIN_hi : Q := { dqg := 881, drg1 := 697, drs1 := 1515, agr1 := 120, aRr1 := 121, agq1 := 93, drg2 := 670, drs2 := 1056, agr2 := 100, aRr2 := 93, agq2 := 100 }
def g2_merge11_uarb1_SMAX_lo : Q := { dqg := 1032, drg1 := 847, drs1 := 1806, agr1 := 153, aRr1 := 156, agq1 := 119, drg2 := 817, drs2 := 1246, agr2 := 124, aRr2 := 119, agq2 := 124 }
def g2_merge11_uarb1_SMAX_hi : Q := { dqg := 1033, drg1 := 848, drs1 := 1807, agr1 := 153, aRr1 := 156, agq1 := 119, drg2 := 818, drs2 := 1247, agr2 := 124, aRr2 := 119, agq2 := 124 }
def g2_merge12_uarb1_FMIN_lo : Q := { dqg := 86, drg1 := 211, drs1 := 178, agr1 := 43, aRr1 := 44, agq1 := 48, drg2 := 321, drs2 := 298, agr2 := 45, aRr2 := 43, agq2 := 45 }
def g2_merge12_uarb1_FMIN_hi : Q := { dqg := 87, drg1 := 212, drs1 := 179, agr1 := 43, aRr1 := 44, agq1 := 48, drg2 := 322, drs2 := 299, agr2 := 45, aRr2 := 43, agq2 := 45 }
def g2_merge12_uarb1_FMAX_lo : Q := { dqg := 104, drg1 := 262, drs1 := 218, agr1 := 55, aRr1 := 57, agq1 := 63, drg2 := 392, drs2 := 365, agr2 := 56, aRr2 := 55, agq2 := 56 }
def g2_merge12_uarb1_FMAX_hi : Q := { dqg := 105, drg1 := 263, drs1 := 219, agr1 := 55, aRr1 := 57, agq1 := 63, drg2 := 393, drs2 := 366, agr2 := 56, aRr2 := 55, agq2 := 56 }
def g2_merge12_uarb1_SMIN_lo : Q := { dqg := 221, drg1 := 525, drs1 := 460, agr1 := 121, aRr1 := 120, agq1 := 94, drg2 := 767, drs2 := 758, agr2 := 100, aRr2 := 121, agq2 := 100 }
def g2_merge12_uarb1_SMIN_hi : Q := { dqg := 222, drg1 := 526, drs1 := 461, agr1 := 121, aRr1 := 120, agq1 := 94, drg2 := 768, drs2 := 759, agr2 := 100, aRr2 := 121, agq2 := 100 }
def g2_merge12_uarb1_SMAX_lo : Q := { dqg := 268, drg1 := 647, drs1 := 561, agr1 := 154, aRr1 := 153, agq1 := 120, drg2 := 938, drs2 := 924, agr2 := 124, aRr2 := 154, agq2 := 124 }
def g2_merge12_uarb1_SMAX_hi : Q := { dqg := 269, drg1 := 648, drs1 := 562, agr1 := 154, aRr1 := 153, agq1 := 120, drg2 := 939, drs2 := 925, agr2 := 124, aRr2 := 154, agq2 := 124 }
def g2_merge12_uarb2_FMIN_lo : Q := { dqg := 214, drg1 := 78, drs1 := 218, agr1 := 48, aRr1 := 44, agq1 := 44, drg2 := 264, drs2 := 204, agr2 := 45, aRr2 := 43, agq2 := 45 }
def g2_merge12_uarb2_FMIN_hi : Q := { dqg := 214, drg1 := 78, drs1 := 218, agr1 := 48, aRr1 := 44, agq1 := 44, drg2 := 265, drs2 := 205, agr2 := 45, aRr2 := 43, agq2 := 45 }
def g2_merge12_uarb2_FMAX_lo : Q := { dqg := 266, drg1 := 97, drs1 := 272, agr1 := 61, aRr1 := 58, agq1 := 58, drg2 := 325, drs2 := 249, agr2 := 56, aRr2 := 55, agq2 := 56 }
def g2_merge12_uarb2_FMAX_hi : Q := { dqg := 266, drg1 := 97, drs1 := 272, agr1 := 61, aRr1 := 58, agq1 := 58, drg2 := 326, drs2 := 250, agr2 := 56, aRr2 := 55, agq2 := 56 }
def g2_merge12_uarb2_SMIN_lo : Q := { dqg := 534, drg1 := 221, drs1 := 542, agr1 := 93, aRr1 := 121, agq1 := 121, drg2 := 638, drs2 := 529, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g2_merge12_uarb2_SMIN_hi : Q := { dqg := 534, drg1 := 221, drs1 := 542, agr1 := 93, aRr1 := 121, agq1 := 121, drg2 := 639, drs2 := 530, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g2_merge12_uarb2_SMAX_lo : Q := { dqg := 659, drg1 := 271, drs1 := 669, agr1 := 119, aRr1 := 156, agq1 := 156, drg2 := 783, drs2 := 648, agr2 := 124, aRr2 := 153, agq2 := 124 }
def g2_merge12_uarb2_SMAX_hi : Q := { dqg := 659, drg1 := 271, drs1 := 669, agr1 := 119, aRr1 := 156, agq1 := 156, drg2 := 784, drs2 := 649, agr2 := 124, aRr2 := 153, agq2 := 124 }
def g2_merge2_uarb1_FMIN_lo : Q := { dqg := 128, drg1 := 270, drs1 := 189, agr1 := 44, aRr1 := 46, agq1 := 48, drg2 := 182, drs2 := 307, agr2 := 45, aRr2 := 43, agq2 := 45 }
def g2_merge2_uarb1_FMIN_hi : Q := { dqg := 129, drg1 := 271, drs1 := 190, agr1 := 44, aRr1 := 46, agq1 := 48, drg2 := 183, drs2 := 308, agr2 := 45, aRr2 := 43, agq2 := 45 }
def g2_merge2_uarb1_FMAX_lo : Q := { dqg := 157, drg1 := 334, drs1 := 230, agr1 := 58, aRr1 := 61, agq1 := 61, drg2 := 218, drs2 := 370, agr2 := 56, aRr2 := 55, agq2 := 56 }
def g2_merge2_uarb1_FMAX_hi : Q := { dqg := 158, drg1 := 335, drs1 := 231, agr1 := 58, aRr1 := 61, agq1 := 61, drg2 := 219, drs2 := 371, agr2 := 56, aRr2 := 55, agq2 := 56 }
def g2_merge2_uarb1_SMIN_lo : Q := { dqg := 332, drg1 := 658, drs1 := 516, agr1 := 121, aRr1 := 120, agq1 := 93, drg2 := 444, drs2 := 729, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g2_merge2_uarb1_SMIN_hi : Q := { dqg := 333, drg1 := 659, drs1 := 517, agr1 := 121, aRr1 := 120, agq1 := 93, drg2 := 445, drs2 := 730, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g2_merge2_uarb1_SMAX_lo : Q := { dqg := 403, drg1 := 808, drs1 := 630, agr1 := 156, aRr1 := 153, agq1 := 119, drg2 := 540, drs2 := 921, agr2 := 124, aRr2 := 153, agq2 := 124 }
def g2_merge2_uarb1_SMAX_hi : Q := { dqg := 404, drg1 := 809, drs1 := 631, agr1 := 156, aRr1 := 153, agq1 := 119, drg2 := 541, drs2 := 922, agr2 := 124, aRr2 := 153, agq2 := 124 }
def g2_merge3_uarb1_FMIN_lo : Q := { dqg := 131, drg1 := 129, drs1 := 209, agr1 := 46, aRr1 := 43, agq1 := 48, drg2 := 218, drs2 := 71, agr2 := 45, aRr2 := 48, agq2 := 45 }
def g2_merge3_uarb1_FMIN_hi : Q := { dqg := 132, drg1 := 129, drs1 := 209, agr1 := 46, aRr1 := 43, agq1 := 48, drg2 := 218, drs2 := 71, agr2 := 45, aRr2 := 48, agq2 := 45 }
def g2_merge3_uarb1_FMAX_lo : Q := { dqg := 160, drg1 := 160, drs1 := 260, agr1 := 61, aRr1 := 55, agq1 := 61, drg2 := 272, drs2 := 89, agr2 := 56, aRr2 := 63, agq2 := 56 }
def g2_merge3_uarb1_FMAX_hi : Q := { dqg := 161, drg1 := 160, drs1 := 260, agr1 := 61, aRr1 := 55, agq1 := 61, drg2 := 272, drs2 := 89, agr2 := 56, aRr2 := 63, agq2 := 56 }
def g2_merge3_uarb1_SMIN_lo : Q := { dqg := 340, drg1 := 358, drs1 := 523, agr1 := 120, aRr1 := 121, agq1 := 93, drg2 := 542, drs2 := 206, agr2 := 100, aRr2 := 94, agq2 := 100 }
def g2_merge3_uarb1_SMIN_hi : Q := { dqg := 341, drg1 := 358, drs1 := 523, agr1 := 120, aRr1 := 121, agq1 := 93, drg2 := 542, drs2 := 206, agr2 := 100, aRr2 := 94, agq2 := 100 }
def g2_merge3_uarb1_SMAX_lo : Q := { dqg := 412, drg1 := 441, drs1 := 645, agr1 := 153, aRr1 := 154, agq1 := 119, drg2 := 669, drs2 := 252, agr2 := 124, aRr2 := 120, agq2 := 124 }
def g2_merge3_uarb1_SMAX_hi : Q := { dqg := 413, drg1 := 441, drs1 := 645, agr1 := 153, aRr1 := 154, agq1 := 119, drg2 := 669, drs2 := 252, agr2 := 124, aRr2 := 120, agq2 := 124 }
def g2_merge4_uarb1_FMIN_lo : Q := { dqg := 271, drg1 := 190, drs1 := 250, agr1 := 46, aRr1 := 43, agq1 := 44, drg2 := 119, drs2 := 194, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g2_merge4_uarb1_FMIN_hi : Q := { dqg := 272, drg1 := 191, drs1 := 251, agr1 := 46, aRr1 := 43, agq1 := 44, drg2 := 120, drs2 := 195, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g2_merge4_uarb1_FMAX_lo : Q := { dqg := 330, drg1 := 232, drs1 := 309, agr1 := 61, aRr1 := 55, agq1 := 57, drg2 := 146, drs2 := 235, agr2 := 56, aRr2 := 57, agq2 := 56 }
def g2_merge4_uarb1_FMAX_hi : Q := { dqg := 331, drg1 := 233, drs1 := 310, agr1 := 61, aRr1 := 55, agq1 := 57, drg2 := 147, drs2 := 236, agr2 := 56, aRr2 := 57, agq2 := 56 }
def g2_merge4_uarb1_SMIN_lo : Q := { dqg := 654, drg1 := 485, drs1 := 633, agr1 := 120, aRr1 := 121, agq1 := 118, drg2 := 327, drs2 := 478, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g2_merge4_uarb1_SMIN_hi : Q := { dqg := 655, drg1 := 486, drs1 := 634, agr1 := 120, aRr1 := 121, agq1 := 118, drg2 := 328, drs2 := 479, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g2_merge4_uarb1_SMAX_lo : Q := { dqg := 798, drg1 := 593, drs1 := 776, agr1 := 153, aRr1 := 154, agq1 := 157, drg2 := 396, drs2 := 581, agr2 := 124, aRr2 := 153, agq2 := 124 }
def g2_merge4_uarb1_SMAX_hi : Q := { dqg := 799, drg1 := 594, drs1 := 777, agr1 := 153, aRr1 := 154, agq1 := 157, drg2 := 397, drs2 := 582, agr2 := 124, aRr2 := 153, agq2 := 124 }
def g2_merge6_uarb1_FMIN_lo : Q := { dqg := 231, drg1 := 126, drs1 := 210, agr1 := 43, aRr1 := 44, agq1 := 44, drg2 := 183, drs2 := 145, agr2 := 45, aRr2 := 42, agq2 := 45 }
def g2_merge6_uarb1_FMIN_hi : Q := { dqg := 232, drg1 := 126, drs1 := 210, agr1 := 43, aRr1 := 44, agq1 := 44, drg2 := 183, drs2 := 145, agr2 := 45, aRr2 := 42, agq2 := 45 }
def g2_merge6_uarb1_FMAX_lo : Q := { dqg := 328, drg1 := 191, drs1 := 261, agr1 := 55, aRr1 := 56, agq1 := 57, drg2 := 273, drs2 := 180, agr2 := 56, aRr2 := 53, agq2 := 56 }
def g2_merge6_uarb1_FMAX_hi : Q := { dqg := 329, drg1 := 191, drs1 := 261, agr1 := 55, aRr1 := 56, agq1 := 57, drg2 := 273, drs2 := 180, agr2 := 56, aRr2 := 53, agq2 := 56 }
def g2_merge6_uarb1_SMIN_lo : Q := { dqg := 523, drg1 := 323, drs1 := 530, agr1 := 120, aRr1 := 120, agq1 := 118, drg2 := 419, drs2 := 392, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g2_merge6_uarb1_SMIN_hi : Q := { dqg := 524, drg1 := 323, drs1 := 530, agr1 := 120, aRr1 := 120, agq1 := 118, drg2 := 419, drs2 := 392, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g2_merge6_uarb1_SMAX_lo : Q := { dqg := 797, drg1 := 515, drs1 := 654, agr1 := 153, aRr1 := 154, agq1 := 157, drg2 := 678, drs2 := 482, agr2 := 124, aRr2 := 153, agq2 := 124 }
def g2_merge6_uarb1_SMAX_hi : Q := { dqg := 798, drg1 := 515, drs1 := 654, agr1 := 153, aRr1 := 154, agq1 := 157, drg2 := 678, drs2 := 482, agr2 := 124, aRr2 := 153, agq2 := 124 }
def g2_merge9_uarb1_FMIN_lo : Q := { dqg := 124, drg1 := 208, drs1 := 208, agr1 := 43, aRr1 := 43, agq1 := 44, drg2 := 210, drs2 := 209, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g2_merge9_uarb1_FMIN_hi : Q := { dqg := 124, drg1 := 208, drs1 := 208, agr1 := 43, aRr1 := 43, agq1 := 44, drg2 := 210, drs2 := 209, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g2_merge9_uarb1_FMAX_lo : Q := { dqg := 154, drg1 := 259, drs1 := 259, agr1 := 55, aRr1 := 55, agq1 := 57, drg2 := 261, drs2 := 260, agr2 := 56, aRr2 := 56, agq2 := 56 }
def g2_merge9_uarb1_FMAX_hi : Q := { dqg := 154, drg1 := 259, drs1 := 259, agr1 := 55, aRr1 := 55, agq1 := 57, drg2 := 261, drs2 := 260, agr2 := 56, aRr2 := 56, agq2 := 56 }
def g2_merge9_uarb1_SMIN_lo : Q := { dqg := 343, drg1 := 523, drs1 := 522, agr1 := 121, aRr1 := 121, agq1 := 120, drg2 := 530, drs2 := 531, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g2_merge9_uarb1_SMIN_hi : Q := { dqg := 343, drg1 := 523, drs1 := 522, agr1 := 121, aRr1 := 121, agq1 := 120, drg2 := 530, drs2 := 531, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g2_merge9_uarb1_SMAX_lo : Q := { dqg := 422, drg1 := 645, drs1 := 644, agr1 := 154, aRr1 := 154, agq1 := 153, drg2 := 654, drs2 := 656, agr2 := 124, aRr2 := 154, agq2 := 124 }
def g2_merge9_uarb1_SMAX_hi : Q := { dqg := 422, drg1 := 645, drs1 := 644, agr1 := 154, aRr1 := 154, agq1 := 153, drg2 := 654, drs2 := 656, agr2 := 124, aRr2 := 154, agq2 := 124 }
def g3_merge10_uarb1_FMIN_lo : Q := { dqg := 275, drg1 := 134, drs1 := 210, agr1 := 44, aRr1 := 43, agq1 := 44, drg2 := 338, drs2 := 218, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g3_merge10_uarb1_FMIN_hi : Q := { dqg := 276, drg1 := 135, drs1 := 211, agr1 := 44, aRr1 := 43, agq1 := 44, drg2 := 339, drs2 := 218, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g3_merge10_uarb1_FMAX_lo : Q := { dqg := 334, drg1 := 164, drs1 := 254, agr1 := 57, aRr1 := 55, agq1 := 56, drg2 := 407, drs2 := 272, agr2 := 56, aRr2 := 58, agq2 := 56 }
def g3_merge10_uarb1_FMAX_hi : Q := { dqg := 335, drg1 := 165, drs1 := 255, agr1 := 57, aRr1 := 55, agq1 := 56, drg2 := 408, drs2 := 272, agr2 := 56, aRr2 := 58, agq2 := 56 }
def g3_merge10_uarb1_SMIN_lo : Q := { dqg := 662, drg1 := 353, drs1 := 552, agr1 := 120, aRr1 := 120, agq1 := 120, drg2 := 781, drs2 := 542, agr2 := 100, aRr2 := 121, agq2 := 100 }
def g3_merge10_uarb1_SMIN_hi : Q := { dqg := 663, drg1 := 354, drs1 := 553, agr1 := 120, aRr1 := 120, agq1 := 120, drg2 := 782, drs2 := 542, agr2 := 100, aRr2 := 121, agq2 := 100 }
def g3_merge10_uarb1_SMAX_lo : Q := { dqg := 807, drg1 := 432, drs1 := 672, agr1 := 153, aRr1 := 153, agq1 := 154, drg2 := 947, drs2 := 669, agr2 := 124, aRr2 := 156, agq2 := 124 }
def g3_merge10_uarb1_SMAX_hi : Q := { dqg := 808, drg1 := 433, drs1 := 673, agr1 := 153, aRr1 := 153, agq1 := 154, drg2 := 948, drs2 := 669, agr2 := 124, aRr2 := 156, agq2 := 124 }
def g3_merge11_uarb1_FMIN_lo : Q := { dqg := 71, drg1 := 211, drs1 := 212, agr1 := 44, aRr1 := 44, agq1 := 48, drg2 := 148, drs2 := 147, agr2 := 45, aRr2 := 42, agq2 := 45 }
def g3_merge11_uarb1_FMIN_hi : Q := { dqg := 71, drg1 := 211, drs1 := 212, agr1 := 44, aRr1 := 44, agq1 := 48, drg2 := 148, drs2 := 147, agr2 := 45, aRr2 := 42, agq2 := 45 }
def g3_merge11_uarb1_FMAX_lo : Q := { dqg := 89, drg1 := 262, drs1 := 263, agr1 := 56, aRr1 := 56, agq1 := 63, drg2 := 184, drs2 := 183, agr2 := 56, aRr2 := 53, agq2 := 56 }
def g3_merge11_uarb1_FMAX_hi : Q := { dqg := 89, drg1 := 262, drs1 := 263, agr1 := 56, aRr1 := 56, agq1 := 63, drg2 := 184, drs2 := 183, agr2 := 56, aRr2 := 53, agq2 := 56 }
def g3_merge11_uarb1_SMIN_lo : Q := { dqg := 206, drg1 := 531, drs1 := 535, agr1 := 120, aRr1 := 120, agq1 := 94, drg2 := 397, drs2 := 393, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g3_merge11_uarb1_SMIN_hi : Q := { dqg := 206, drg1 := 531, drs1 := 535, agr1 := 120, aRr1 := 120, agq1 := 94, drg2 := 397, drs2 := 393, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g3_merge11_uarb1_SMAX_lo : Q := { dqg := 252, drg1 := 655, drs1 := 660, agr1 := 154, aRr1 := 154, agq1 := 120, drg2 := 489, drs2 := 484, agr2 := 124, aRr2 := 153, agq2 := 124 }
def g3_merge11_uarb1_SMAX_hi : Q := { dqg := 252, drg1 := 655, drs1 := 660, agr1 := 154, aRr1 := 154, agq1 := 120, drg2 := 489, drs2 := 484, agr2 := 124, aRr2 := 153, agq2 := 124 }
def g3_merge12_uarb1_FMIN_lo : Q := { dqg := 72, drg1 := 199, drs1 := 263, agr1 := 42, aRr1 := 43, agq1 := 48, drg2 := 313, drs2 := 227, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g3_merge12_uarb1_FMIN_hi : Q := { dqg := 72, drg1 := 200, drs1 := 264, agr1 := 42, aRr1 := 43, agq1 := 48, drg2 := 314, drs2 := 228, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g3_merge12_uarb1_FMAX_lo : Q := { dqg := 90, drg1 := 245, drs1 := 324, agr1 := 53, aRr1 := 55, agq1 := 63, drg2 := 382, drs2 := 275, agr2 := 56, aRr2 := 57, agq2 := 56 }
def g3_merge12_uarb1_FMAX_hi : Q := { dqg := 90, drg1 := 246, drs1 := 325, agr1 := 53, aRr1 := 55, agq1 := 63, drg2 := 383, drs2 := 276, agr2 := 56, aRr2 := 57, agq2 := 56 }
def g3_merge12_uarb1_SMIN_lo : Q := { dqg := 207, drg1 := 511, drs1 := 640, agr1 := 120, aRr1 := 121, agq1 := 94, drg2 := 801, drs2 := 621, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g3_merge12_uarb1_SMIN_hi : Q := { dqg := 207, drg1 := 512, drs1 := 641, agr1 := 120, aRr1 := 121, agq1 := 94, drg2 := 802, drs2 := 622, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g3_merge12_uarb1_SMAX_lo : Q := { dqg := 254, drg1 := 626, drs1 := 785, agr1 := 153, aRr1 := 154, agq1 := 120, drg2 := 978, drs2 := 754, agr2 := 124, aRr2 := 153, agq2 := 124 }
def g3_merge12_uarb1_SMAX_hi : Q := { dqg := 254, drg1 := 627, drs1 := 786, agr1 := 153, aRr1 := 154, agq1 := 120, drg2 := 979, drs2 := 755, agr2 := 124, aRr2 := 153, agq2 := 124 }
def g3_merge12_uarb2_FMIN_lo : Q := { dqg := 123, drg1 := 203, drs1 := 327, agr1 := 42, aRr1 := 43, agq1 := 48, drg2 := 262, drs2 := 210, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g3_merge12_uarb2_FMIN_hi : Q := { dqg := 124, drg1 := 204, drs1 := 328, agr1 := 42, aRr1 := 43, agq1 := 48, drg2 := 263, drs2 := 210, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g3_merge12_uarb2_FMAX_lo : Q := { dqg := 151, drg1 := 246, drs1 := 396, agr1 := 53, aRr1 := 55, agq1 := 63, drg2 := 323, drs2 := 261, agr2 := 56, aRr2 := 56, agq2 := 56 }
def g3_merge12_uarb2_FMAX_hi : Q := { dqg := 152, drg1 := 247, drs1 := 397, agr1 := 53, aRr1 := 55, agq1 := 63, drg2 := 324, drs2 := 261, agr2 := 56, aRr2 := 56, agq2 := 56 }
def g3_merge12_uarb2_SMIN_lo : Q := { dqg := 321, drg1 := 530, drs1 := 769, agr1 := 120, aRr1 := 121, agq1 := 94, drg2 := 646, drs2 := 530, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g3_merge12_uarb2_SMIN_hi : Q := { dqg := 322, drg1 := 531, drs1 := 770, agr1 := 120, aRr1 := 121, agq1 := 94, drg2 := 647, drs2 := 530, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g3_merge12_uarb2_SMAX_lo : Q := { dqg := 389, drg1 := 644, drs1 := 935, agr1 := 153, aRr1 := 154, agq1 := 120, drg2 := 793, drs2 := 654, agr2 := 124, aRr2 := 154, agq2 := 124 }
def g3_merge12_uarb2_SMAX_hi : Q := { dqg := 390, drg1 := 645, drs1 := 936, agr1 := 153, aRr1 := 154, agq1 := 120, drg2 := 794, drs2 := 654, agr2 := 124, aRr2 := 154, agq2 := 124 }
def g3_merge2_uarb1_FMIN_lo : Q := { dqg := 134, drg1 := 157, drs1 := 147, agr1 := 42, aRr1 := 42, agq1 := 44, drg2 := 85, drs2 := 86, agr2 := 45, aRr2 := 48, agq2 := 45 }
def g3_merge2_uarb1_FMIN_hi : Q := { dqg := 135, drg1 := 158, drs1 := 147, agr1 := 42, aRr1 := 42, agq1 := 44, drg2 := 86, drs2 := 87, agr2 := 45, aRr2 := 48, agq2 := 45 }
def g3_merge2_uarb1_FMAX_lo : Q := { dqg := 164, drg1 := 192, drs1 := 183, agr1 := 53, aRr1 := 53, agq1 := 57, drg2 := 103, drs2 := 104, agr2 := 56, aRr2 := 63, agq2 := 56 }
def g3_merge2_uarb1_FMAX_hi : Q := { dqg := 165, drg1 := 193, drs1 := 183, agr1 := 53, aRr1 := 53, agq1 := 57, drg2 := 104, drs2 := 105, agr2 := 56, aRr2 := 63, agq2 := 56 }
def g3_merge2_uarb1_SMIN_lo : Q := { dqg := 353, drg1 := 404, drs1 := 395, agr1 := 120, aRr1 := 120, agq1 := 120, drg2 := 219, drs2 := 221, agr2 := 100, aRr2 := 94, agq2 := 100 }
def g3_merge2_uarb1_SMIN_hi : Q := { dqg := 354, drg1 := 405, drs1 := 395, agr1 := 120, aRr1 := 120, agq1 := 120, drg2 := 220, drs2 := 222, agr2 := 100, aRr2 := 94, agq2 := 100 }
def g3_merge2_uarb1_SMAX_lo : Q := { dqg := 432, drg1 := 494, drs1 := 487, agr1 := 153, aRr1 := 153, agq1 := 153, drg2 := 264, drs2 := 268, agr2 := 124, aRr2 := 120, agq2 := 124 }
def g3_merge2_uarb1_SMAX_hi : Q := { dqg := 433, drg1 := 495, drs1 := 487, agr1 := 153, aRr1 := 153, agq1 := 153, drg2 := 265, drs2 := 269, agr2 := 124, aRr2 := 120, agq2 := 124 }
def g3_merge3_uarb1_FMIN_lo : Q := { dqg := 123, drg1 := 211, drs1 := 208, agr1 := 44, aRr1 := 43, agq1 := 48, drg2 := 148, drs2 := 219, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g3_merge3_uarb1_FMIN_hi : Q := { dqg := 124, drg1 := 211, drs1 := 208, agr1 := 44, aRr1 := 43, agq1 := 48, drg2 := 148, drs2 := 220, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g3_merge3_uarb1_FMAX_lo : Q := { dqg := 151, drg1 := 262, drs1 := 259, agr1 := 56, aRr1 := 55, agq1 := 63, drg2 := 184, drs2 := 270, agr2 := 56, aRr2 := 56, agq2 := 56 }
def g3_merge3_uarb1_FMAX_hi : Q := { dqg := 152, drg1 := 262, drs1 := 259, agr1 := 56, aRr1 := 55, agq1 := 63, drg2 := 184, drs2 := 271, agr2 := 56, aRr2 := 56, agq2 := 56 }
def g3_merge3_uarb1_SMIN_lo : Q := { dqg := 322, drg1 := 531, drs1 := 523, agr1 := 120, aRr1 := 121, agq1 := 94, drg2 := 397, drs2 := 539, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g3_merge3_uarb1_SMIN_hi : Q := { dqg := 323, drg1 := 531, drs1 := 523, agr1 := 120, aRr1 := 121, agq1 := 94, drg2 := 397, drs2 := 540, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g3_merge3_uarb1_SMAX_lo : Q := { dqg := 391, drg1 := 655, drs1 := 645, agr1 := 154, aRr1 := 154, agq1 := 120, drg2 := 489, drs2 := 663, agr2 := 124, aRr2 := 154, agq2 := 124 }
def g3_merge3_uarb1_SMAX_hi : Q := { dqg := 392, drg1 := 655, drs1 := 645, agr1 := 154, aRr1 := 154, agq1 := 120, drg2 := 489, drs2 := 664, agr2 := 124, aRr2 := 154, agq2 := 124 }
def g3_merge4_uarb1_FMIN_lo : Q := { dqg := 251, drg1 := 215, drs1 := 330, agr1 := 48, aRr1 := 44, agq1 := 43, drg2 := 297, drs2 := 272, agr2 := 45, aRr2 := 46, agq2 := 45 }
def g3_merge4_uarb1_FMIN_hi : Q := { dqg := 252, drg1 := 216, drs1 := 331, agr1 := 48, aRr1 := 44, agq1 := 43, drg2 := 298, drs2 := 273, agr2 := 45, aRr2 := 46, agq2 := 45 }
def g3_merge4_uarb1_FMAX_lo : Q := { dqg := 310, drg1 := 256, drs1 := 399, agr1 := 63, aRr1 := 57, agq1 := 55, drg2 := 340, drs2 := 314, agr2 := 56, aRr2 := 61, agq2 := 56 }
def g3_merge4_uarb1_FMAX_hi : Q := { dqg := 311, drg1 := 257, drs1 := 400, agr1 := 63, aRr1 := 57, agq1 := 55, drg2 := 341, drs2 := 315, agr2 := 56, aRr2 := 61, agq2 := 56 }
def g3_merge4_uarb1_SMIN_lo : Q := { dqg := 634, drg1 := 494, drs1 := 786, agr1 := 94, aRr1 := 118, agq1 := 121, drg2 := 612, drs2 := 566, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g3_merge4_uarb1_SMIN_hi : Q := { dqg := 635, drg1 := 495, drs1 := 787, agr1 := 94, aRr1 := 118, agq1 := 121, drg2 := 613, drs2 := 567, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g3_merge4_uarb1_SMAX_lo : Q := { dqg := 777, drg1 := 593, drs1 := 956, agr1 := 120, aRr1 := 157, agq1 := 154, drg2 := 723, drs2 := 673, agr2 := 124, aRr2 := 153, agq2 := 124 }
def g3_merge4_uarb1_SMAX_hi : Q := { dqg := 778, drg1 := 594, drs1 := 957, agr1 := 120, aRr1 := 157, agq1 := 154, drg2 := 724, drs2 := 674, agr2 := 124, aRr2 := 153, agq2 := 124 }
def g3_merge6_uarb1_FMIN_lo : Q := { dqg := 209, drg1 := 115, drs1 := 119, agr1 := 48, aRr1 := 48, agq1 := 43, drg2 := 148, drs2 := 218, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g3_merge6_uarb1_FMIN_hi : Q := { dqg := 209, drg1 := 116, drs1 := 120, agr1 := 48, aRr1 := 48, agq1 := 43, drg2 := 148, drs2 := 218, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g3_merge6_uarb1_FMAX_lo : Q := { dqg := 260, drg1 := 141, drs1 := 146, agr1 := 63, aRr1 := 61, agq1 := 55, drg2 := 184, drs2 := 272, agr2 := 56, aRr2 := 58, agq2 := 56 }
def g3_merge6_uarb1_FMAX_hi : Q := { dqg := 260, drg1 := 142, drs1 := 147, agr1 := 63, aRr1 := 61, agq1 := 55, drg2 := 184, drs2 := 272, agr2 := 56, aRr2 := 58, agq2 := 56 }
def g3_merge6_uarb1_SMIN_lo : Q := { dqg := 523, drg1 := 331, drs1 := 327, agr1 := 94, aRr1 := 93, agq1 := 121, drg2 := 397, drs2 := 542, agr2 := 100, aRr2 := 121, agq2 := 100 }
def g3_merge6_uarb1_SMIN_hi : Q := { dqg := 523, drg1 := 332, drs1 := 328, agr1 := 94, aRr1 := 93, agq1 := 121, drg2 := 397, drs2 := 542, agr2 := 100, aRr2 := 121, agq2 := 100 }
def g3_merge6_uarb1_SMAX_lo : Q := { dqg := 645, drg1 := 401, drs1 := 396, agr1 := 120, aRr1 := 119, agq1 := 154, drg2 := 489, drs2 := 669, agr2 := 124, aRr2 := 156, agq2 := 124 }
def g3_merge6_uarb1_SMAX_hi : Q := { dqg := 645, drg1 := 402, drs1 := 397, agr1 := 120, aRr1 := 119, agq1 := 154, drg2 := 489, drs2 := 669, agr2 := 124, aRr2 := 156, agq2 := 124 }
def g3_merge9_uarb1_FMIN_lo : Q := { dqg := 210, drg1 := 231, drs1 := 177, agr1 := 44, aRr1 := 44, agq1 := 42, drg2 := 219, drs2 := 85, agr2 := 45, aRr2 := 48, agq2 := 45 }
def g3_merge9_uarb1_FMIN_hi : Q := { dqg := 211, drg1 := 232, drs1 := 178, agr1 := 44, aRr1 := 44, agq1 := 42, drg2 := 220, drs2 := 86, agr2 := 45, aRr2 := 48, agq2 := 45 }
def g3_merge9_uarb1_FMAX_lo : Q := { dqg := 255, drg1 := 279, drs1 := 215, agr1 := 57, aRr1 := 57, agq1 := 53, drg2 := 270, drs2 := 103, agr2 := 56, aRr2 := 63, agq2 := 56 }
def g3_merge9_uarb1_FMAX_hi : Q := { dqg := 256, drg1 := 280, drs1 := 216, agr1 := 57, aRr1 := 57, agq1 := 53, drg2 := 271, drs2 := 104, agr2 := 56, aRr2 := 63, agq2 := 56 }
def g3_merge9_uarb1_SMIN_lo : Q := { dqg := 521, drg1 := 582, drs1 := 464, agr1 := 120, aRr1 := 120, agq1 := 120, drg2 := 539, drs2 := 219, agr2 := 100, aRr2 := 94, agq2 := 100 }
def g3_merge9_uarb1_SMIN_hi : Q := { dqg := 522, drg1 := 583, drs1 := 465, agr1 := 120, aRr1 := 120, agq1 := 120, drg2 := 540, drs2 := 220, agr2 := 100, aRr2 := 94, agq2 := 100 }
def g3_merge9_uarb1_SMAX_lo : Q := { dqg := 634, drg1 := 705, drs1 := 564, agr1 := 153, aRr1 := 153, agq1 := 153, drg2 := 663, drs2 := 264, agr2 := 124, aRr2 := 120, agq2 := 124 }
def g3_merge9_uarb1_SMAX_hi : Q := { dqg := 635, drg1 := 706, drs1 := 565, agr1 := 153, aRr1 := 153, agq1 := 153, drg2 := 664, drs2 := 265, agr2 := 124, aRr2 := 120, agq2 := 124 }
def g4_merge10_uarb1_FMIN_lo : Q := { dqg := 331, drg1 := 191, drs1 := 181, agr1 := 44, aRr1 := 46, agq1 := 44, drg2 := 227, drs2 := 354, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g4_merge10_uarb1_FMIN_hi : Q := { dqg := 332, drg1 := 192, drs1 := 182, agr1 := 44, aRr1 := 46, agq1 := 44, drg2 := 228, drs2 := 355, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g4_merge10_uarb1_FMAX_lo : Q := { dqg := 400, drg1 := 229, drs1 := 222, agr1 := 57, aRr1 := 61, agq1 := 56, drg2 := 270, drs2 := 426, agr2 := 56, aRr2 := 58, agq2 := 56 }
def g4_merge10_uarb1_FMAX_hi : Q := { dqg := 401, drg1 := 230, drs1 := 223, agr1 := 57, aRr1 := 61, agq1 := 56, drg2 := 271, drs2 := 427, agr2 := 56, aRr2 := 58, agq2 := 56 }
def g4_merge10_uarb1_SMIN_lo : Q := { dqg := 781, drg1 := 491, drs1 := 474, agr1 := 120, aRr1 := 120, agq1 := 120, drg2 := 542, drs2 := 773, agr2 := 100, aRr2 := 121, agq2 := 100 }
def g4_merge10_uarb1_SMIN_hi : Q := { dqg := 782, drg1 := 492, drs1 := 475, agr1 := 120, aRr1 := 120, agq1 := 120, drg2 := 543, drs2 := 774, agr2 := 100, aRr2 := 121, agq2 := 100 }
def g4_merge10_uarb1_SMAX_lo : Q := { dqg := 949, drg1 := 594, drs1 := 580, agr1 := 153, aRr1 := 153, agq1 := 154, drg2 := 653, drs2 := 941, agr2 := 124, aRr2 := 156, agq2 := 124 }
def g4_merge10_uarb1_SMAX_hi : Q := { dqg := 950, drg1 := 595, drs1 := 581, agr1 := 153, aRr1 := 153, agq1 := 154, drg2 := 654, drs2 := 942, agr2 := 124, aRr2 := 156, agq2 := 124 }
def g4_merge11_uarb1_FMIN_lo : Q := { dqg := 129, drg1 := 218, drs1 := 213, agr1 := 44, aRr1 := 44, agq1 := 46, drg2 := 152, drs2 := 152, agr2 := 45, aRr2 := 43, agq2 := 45 }
def g4_merge11_uarb1_FMIN_hi : Q := { dqg := 129, drg1 := 218, drs1 := 213, agr1 := 44, aRr1 := 44, agq1 := 46, drg2 := 152, drs2 := 152, agr2 := 45, aRr2 := 43, agq2 := 45 }
def g4_merge11_uarb1_FMAX_lo : Q := { dqg := 160, drg1 := 272, drs1 := 265, agr1 := 58, aRr1 := 58, agq1 := 61, drg2 := 188, drs2 := 188, agr2 := 56, aRr2 := 55, agq2 := 56 }
def g4_merge11_uarb1_FMAX_hi : Q := { dqg := 160, drg1 := 272, drs1 := 265, agr1 := 58, aRr1 := 58, agq1 := 61, drg2 := 188, drs2 := 188, agr2 := 56, aRr2 := 55, agq2 := 56 }
def g4_merge11_uarb1_SMIN_lo : Q := { dqg := 358, drg1 := 542, drs1 := 534, agr1 := 121, aRr1 := 121, agq1 := 120, drg2 := 414, drs2 := 412, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g4_merge11_uarb1_SMIN_hi : Q := { dqg := 358, drg1 := 542, drs1 := 534, agr1 := 121, aRr1 := 121, agq1 := 120, drg2 := 414, drs2 := 412, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g4_merge11_uarb1_SMAX_lo : Q := { dqg := 441, drg1 := 669, drs1 := 659, agr1 := 156, aRr1 := 156, agq1 := 153, drg2 := 510, drs2 := 508, agr2 := 124, aRr2 := 153, agq2 := 124 }
def g4_merge11_uarb1_SMAX_hi : Q := { dqg := 441, drg1 := 669, drs1 := 659, agr1 := 156, aRr1 := 156, agq1 := 153, drg2 := 510, drs2 := 508, agr2 := 124, aRr2 := 153, agq2 := 124 }
def g4_merge12_uarb1_FMIN_lo : Q := { dqg := 267, drg1 := 320, drs1 := 220, agr1 := 42, aRr1 := 48, agq1 := 43, drg2 := 319, drs2 := 264, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g4_merge12_uarb1_FMIN_hi : Q := { dqg := 268, drg1 := 321, drs1 := 221, agr1 := 42, aRr1 := 48, agq1 := 43, drg2 := 320, drs2 := 265, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g4_merge12_uarb1_FMAX_lo : Q := { dqg := 328, drg1 := 386, drs1 := 264, agr1 := 53, aRr1 := 61, agq1 := 55, drg2 := 390, drs2 := 325, agr2 := 56, aRr2 := 57, agq2 := 56 }
def g4_merge12_uarb1_FMAX_hi : Q := { dqg := 329, drg1 := 387, drs1 := 265, agr1 := 53, aRr1 := 61, agq1 := 55, drg2 := 391, drs2 := 326, agr2 := 56, aRr2 := 57, agq2 := 56 }
def g4_merge12_uarb1_SMIN_lo : Q := { dqg := 640, drg1 := 755, drs1 := 519, agr1 := 120, aRr1 := 93, agq1 := 121, drg2 := 765, drs2 := 637, agr2 := 100, aRr2 := 118, agq2 := 100 }
def g4_merge12_uarb1_SMIN_hi : Q := { dqg := 641, drg1 := 756, drs1 := 520, agr1 := 120, aRr1 := 93, agq1 := 121, drg2 := 766, drs2 := 638, agr2 := 100, aRr2 := 118, agq2 := 100 }
def g4_merge12_uarb1_SMAX_lo : Q := { dqg := 785, drg1 := 917, drs1 := 626, agr1 := 153, aRr1 := 119, agq1 := 154, drg2 := 936, drs2 := 782, agr2 := 124, aRr2 := 157, agq2 := 124 }
def g4_merge12_uarb1_SMAX_hi : Q := { dqg := 786, drg1 := 918, drs1 := 627, agr1 := 153, aRr1 := 119, agq1 := 154, drg2 := 937, drs2 := 783, agr2 := 124, aRr2 := 157, agq2 := 124 }
def g4_merge12_uarb2_FMIN_lo : Q := { dqg := 187, drg1 := 78, drs1 := 208, agr1 := 48, aRr1 := 42, agq1 := 46, drg2 := 264, drs2 := 244, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g4_merge12_uarb2_FMIN_hi : Q := { dqg := 188, drg1 := 78, drs1 := 209, agr1 := 48, aRr1 := 42, agq1 := 46, drg2 := 265, drs2 := 245, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g4_merge12_uarb2_FMAX_lo : Q := { dqg := 226, drg1 := 97, drs1 := 252, agr1 := 61, aRr1 := 53, agq1 := 61, drg2 := 325, drs2 := 292, agr2 := 56, aRr2 := 57, agq2 := 56 }
def g4_merge12_uarb2_FMAX_hi : Q := { dqg := 227, drg1 := 97, drs1 := 253, agr1 := 61, aRr1 := 53, agq1 := 61, drg2 := 326, drs2 := 293, agr2 := 56, aRr2 := 57, agq2 := 56 }
def g4_merge12_uarb2_SMIN_lo : Q := { dqg := 497, drg1 := 221, drs1 := 537, agr1 := 93, aRr1 := 120, agq1 := 120, drg2 := 638, drs2 := 610, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g4_merge12_uarb2_SMIN_hi : Q := { dqg := 498, drg1 := 221, drs1 := 538, agr1 := 93, aRr1 := 120, agq1 := 120, drg2 := 639, drs2 := 611, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g4_merge12_uarb2_SMAX_lo : Q := { dqg := 603, drg1 := 271, drs1 := 653, agr1 := 119, aRr1 := 153, agq1 := 153, drg2 := 783, drs2 := 736, agr2 := 124, aRr2 := 153, agq2 := 124 }
def g4_merge12_uarb2_SMAX_hi : Q := { dqg := 604, drg1 := 271, drs1 := 654, agr1 := 119, aRr1 := 153, agq1 := 153, drg2 := 784, drs2 := 737, agr2 := 124, aRr2 := 153, agq2 := 124 }
def g4_merge2_uarb1_FMIN_lo : Q := { dqg := 328, drg1 := 131, drs1 := 269, agr1 := 48, aRr1 := 44, agq1 := 44, drg2 := 415, drs2 := 212, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g4_merge2_uarb1_FMIN_hi : Q := { dqg := 329, drg1 := 132, drs1 := 270, agr1 := 48, aRr1 := 44, agq1 := 44, drg2 := 416, drs2 := 212, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g4_merge2_uarb1_FMAX_lo : Q := { dqg := 377, drg1 := 157, drs1 := 309, agr1 := 63, aRr1 := 57, agq1 := 57, drg2 := 485, drs2 := 263, agr2 := 56, aRr2 := 56, agq2 := 56 }
def g4_merge2_uarb1_FMAX_hi : Q := { dqg := 378, drg1 := 158, drs1 := 310, agr1 := 63, aRr1 := 57, agq1 := 57, drg2 := 486, drs2 := 263, agr2 := 56, aRr2 := 56, agq2 := 56 }
def g4_merge2_uarb1_SMIN_lo : Q := { dqg := 679, drg1 := 333, drs1 := 547, agr1 := 94, aRr1 := 120, agq1 := 120, drg2 := 862, drs2 := 535, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g4_merge2_uarb1_SMIN_hi : Q := { dqg := 680, drg1 := 334, drs1 := 548, agr1 := 94, aRr1 := 120, agq1 := 120, drg2 := 863, drs2 := 535, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g4_merge2_uarb1_SMAX_lo : Q := { dqg := 802, drg1 := 400, drs1 := 649, agr1 := 120, aRr1 := 153, agq1 := 153, drg2 := 1030, drs2 := 660, agr2 := 124, aRr2 := 154, agq2 := 124 }
def g4_merge2_uarb1_SMAX_hi : Q := { dqg := 803, drg1 := 401, drs1 := 650, agr1 := 120, aRr1 := 153, agq1 := 153, drg2 := 1031, drs2 := 660, agr2 := 124, aRr2 := 154, agq2 := 124 }
def g4_merge3_uarb1_FMIN_lo : Q := { dqg := 397, drg1 := 357, drs1 := 157, agr1 := 44, aRr1 := 42, agq1 := 43, drg2 := 178, drs2 := 392, agr2 := 45, aRr2 := 43, agq2 := 45 }
def g4_merge3_uarb1_FMIN_hi : Q := { dqg := 398, drg1 := 358, drs1 := 158, agr1 := 44, aRr1 := 42, agq1 := 43, drg2 := 179, drs2 := 393, agr2 := 45, aRr2 := 43, agq2 := 45 }
def g4_merge3_uarb1_FMAX_lo : Q := { dqg := 464, drg1 := 419, drs1 := 192, agr1 := 56, aRr1 := 53, agq1 := 55, drg2 := 218, drs2 := 459, agr2 := 56, aRr2 := 55, agq2 := 56 }
def g4_merge3_uarb1_FMAX_hi : Q := { dqg := 465, drg1 := 420, drs1 := 193, agr1 := 56, aRr1 := 53, agq1 := 55, drg2 := 219, drs2 := 460, agr2 := 56, aRr2 := 55, agq2 := 56 }
def g4_merge3_uarb1_SMIN_lo : Q := { dqg := 847, drg1 := 746, drs1 := 404, agr1 := 120, aRr1 := 120, agq1 := 121, drg2 := 459, drs2 := 855, agr2 := 100, aRr2 := 121, agq2 := 100 }
def g4_merge3_uarb1_SMIN_hi : Q := { dqg := 848, drg1 := 747, drs1 := 405, agr1 := 120, aRr1 := 120, agq1 := 121, drg2 := 460, drs2 := 856, agr2 := 100, aRr2 := 121, agq2 := 100 }
def g4_merge3_uarb1_SMAX_lo : Q := { dqg := 1012, drg1 := 896, drs1 := 494, agr1 := 154, aRr1 := 153, agq1 := 154, drg2 := 561, drs2 := 1022, agr2 := 124, aRr2 := 154, agq2 := 124 }
def g4_merge3_uarb1_SMAX_hi : Q := { dqg := 1013, drg1 := 897, drs1 := 495, agr1 := 154, aRr1 := 153, agq1 := 154, drg2 := 562, drs2 := 1023, agr2 := 124, aRr2 := 154, agq2 := 124 }
def g4_merge4_uarb1_FMIN_lo : Q := { dqg := 195, drg1 := 275, drs1 := 261, agr1 := 44, aRr1 := 43, agq1 := 44, drg2 := 208, drs2 := 186, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g4_merge4_uarb1_FMIN_hi : Q := { dqg := 196, drg1 := 276, drs1 := 262, agr1 := 44, aRr1 := 43, agq1 := 44, drg2 := 208, drs2 := 187, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g4_merge4_uarb1_FMAX_lo : Q := { dqg := 235, drg1 := 336, drs1 := 322, agr1 := 56, aRr1 := 55, agq1 := 57, drg2 := 259, drs2 := 226, agr2 := 56, aRr2 := 57, agq2 := 56 }
def g4_merge4_uarb1_FMAX_hi : Q := { dqg := 236, drg1 := 337, drs1 := 323, agr1 := 56, aRr1 := 55, agq1 := 57, drg2 := 259, drs2 := 227, agr2 := 56, aRr2 := 57, agq2 := 56 }
def g4_merge4_uarb1_SMIN_lo : Q := { dqg := 512, drg1 := 664, drs1 := 640, agr1 := 120, aRr1 := 121, agq1 := 120, drg2 := 523, drs2 := 501, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g4_merge4_uarb1_SMIN_hi : Q := { dqg := 513, drg1 := 665, drs1 := 641, agr1 := 120, aRr1 := 121, agq1 := 120, drg2 := 523, drs2 := 502, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g4_merge4_uarb1_SMAX_lo : Q := { dqg := 622, drg1 := 812, drs1 := 786, agr1 := 154, aRr1 := 154, agq1 := 153, drg2 := 645, drs2 := 611, agr2 := 124, aRr2 := 153, agq2 := 124 }
def g4_merge4_uarb1_SMAX_hi : Q := { dqg := 623, drg1 := 813, drs1 := 787, agr1 := 154, aRr1 := 154, agq1 := 153, drg2 := 645, drs2 := 612, agr2 := 124, aRr2 := 153, agq2 := 124 }
def g4_merge6_uarb1_FMIN_lo : Q := { dqg := 257, drg1 := 254, drs1 := 314, agr1 := 44, aRr1 := 44, agq1 := 42, drg2 := 183, drs2 := 125, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g4_merge6_uarb1_FMIN_hi : Q := { dqg := 258, drg1 := 255, drs1 := 315, agr1 := 44, aRr1 := 44, agq1 := 42, drg2 := 184, drs2 := 125, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g4_merge6_uarb1_FMAX_lo : Q := { dqg := 313, drg1 := 313, drs1 := 383, agr1 := 56, aRr1 := 56, agq1 := 53, drg2 := 223, drs2 := 155, agr2 := 56, aRr2 := 57, agq2 := 56 }
def g4_merge6_uarb1_FMAX_hi : Q := { dqg := 314, drg1 := 314, drs1 := 384, agr1 := 56, aRr1 := 56, agq1 := 53, drg2 := 224, drs2 := 155, agr2 := 56, aRr2 := 57, agq2 := 56 }
def g4_merge6_uarb1_SMIN_lo : Q := { dqg := 639, drg1 := 642, drs1 := 762, agr1 := 120, aRr1 := 120, agq1 := 120, drg2 := 458, drs2 := 341, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g4_merge6_uarb1_SMIN_hi : Q := { dqg := 640, drg1 := 643, drs1 := 763, agr1 := 120, aRr1 := 120, agq1 := 120, drg2 := 459, drs2 := 341, agr2 := 100, aRr2 := 120, agq2 := 100 }
def g4_merge6_uarb1_SMAX_lo : Q := { dqg := 778, drg1 := 787, drs1 := 930, agr1 := 154, aRr1 := 154, agq1 := 153, drg2 := 559, drs2 := 419, agr2 := 124, aRr2 := 153, agq2 := 124 }
def g4_merge6_uarb1_SMAX_hi : Q := { dqg := 779, drg1 := 788, drs1 := 931, agr1 := 154, aRr1 := 154, agq1 := 153, drg2 := 560, drs2 := 419, agr2 := 124, aRr2 := 153, agq2 := 124 }
def g4_merge9_uarb1_FMIN_lo : Q := { dqg := 212, drg1 := 129, drs1 := 128, agr1 := 46, aRr1 := 46, agq1 := 43, drg2 := 218, drs2 := 213, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g4_merge9_uarb1_FMIN_hi : Q := { dqg := 213, drg1 := 129, drs1 := 128, agr1 := 46, aRr1 := 46, agq1 := 43, drg2 := 218, drs2 := 213, agr2 := 45, aRr2 := 44, agq2 := 45 }
def g4_merge9_uarb1_FMAX_lo : Q := { dqg := 258, drg1 := 160, drs1 := 159, agr1 := 61, aRr1 := 61, agq1 := 55, drg2 := 272, drs2 := 265, agr2 := 56, aRr2 := 58, agq2 := 56 }
def g4_merge9_uarb1_FMAX_hi : Q := { dqg := 259, drg1 := 160, drs1 := 159, agr1 := 61, aRr1 := 61, agq1 := 55, drg2 := 272, drs2 := 265, agr2 := 56, aRr2 := 58, agq2 := 56 }
def g4_merge9_uarb1_SMIN_lo : Q := { dqg := 572, drg1 := 358, drs1 := 356, agr1 := 120, aRr1 := 120, agq1 := 120, drg2 := 542, drs2 := 534, agr2 := 100, aRr2 := 121, agq2 := 100 }
def g4_merge9_uarb1_SMIN_hi : Q := { dqg := 573, drg1 := 358, drs1 := 356, agr1 := 120, aRr1 := 120, agq1 := 120, drg2 := 542, drs2 := 534, agr2 := 100, aRr2 := 121, agq2 := 100 }
def g4_merge9_uarb1_SMAX_lo : Q := { dqg := 699, drg1 := 441, drs1 := 438, agr1 := 153, aRr1 := 153, agq1 := 153, drg2 := 669, drs2 := 659, agr2 := 124, aRr2 := 156, agq2 := 124 }
def g4_merge9_uarb1_SMAX_hi : Q := { dqg := 700, drg1 := 441, drs1 := 438, agr1 := 153, aRr1 := 153, agq1 := 153, drg2 := 669, drs2 := 659, agr2 := 124, aRr2 := 156, agq2 := 124 }
def gd_merge10_uarb1_FMIN_lo : Q := { dqg := 218, drg1 := 129, drs1 := 243, agr1 := 46, aRr1 := 44, agq1 := 44, drg2 := 166, drs2 := 282, agr2 := 45, aRr2 := 43, agq2 := 45 }
def gd_merge10_uarb1_FMIN_hi : Q := { dqg := 218, drg1 := 129, drs1 := 244, agr1 := 46, aRr1 := 44, agq1 := 44, drg2 := 167, drs2 := 283, agr2 := 45, aRr2 := 43, agq2 := 45 }
def gd_merge10_uarb1_FMAX_lo : Q := { dqg := 272, drg1 := 160, drs1 := 343, agr1 := 61, aRr1 := 58, agq1 := 58, drg2 := 193, drs2 := 373, agr2 := 56, aRr2 := 55, agq2 := 56 }
def gd_merge10_uarb1_FMAX_hi : Q := { dqg := 272, drg1 := 160, drs1 := 344, agr1 := 61, aRr1 := 58, agq1 := 58, drg2 := 194, drs2 := 374, agr2 := 56, aRr2 := 55, agq2 := 56 }
def gd_merge10_uarb1_SMIN_lo : Q := { dqg := 542, drg1 := 358, drs1 := 577, agr1 := 120, aRr1 := 121, agq1 := 121, drg2 := 375, drs2 := 643, agr2 := 100, aRr2 := 120, agq2 := 100 }
def gd_merge10_uarb1_SMIN_hi : Q := { dqg := 542, drg1 := 358, drs1 := 578, agr1 := 120, aRr1 := 121, agq1 := 121, drg2 := 376, drs2 := 644, agr2 := 100, aRr2 := 120, agq2 := 100 }
def gd_merge10_uarb1_SMAX_lo : Q := { dqg := 669, drg1 := 441, drs1 := 867, agr1 := 153, aRr1 := 156, agq1 := 156, drg2 := 444, drs2 := 929, agr2 := 124, aRr2 := 153, agq2 := 124 }
def gd_merge10_uarb1_SMAX_hi : Q := { dqg := 669, drg1 := 441, drs1 := 868, agr1 := 153, aRr1 := 156, agq1 := 156, drg2 := 445, drs2 := 930, agr2 := 124, aRr2 := 153, agq2 := 124 }
def gd_merge11_uarb1_FMIN_lo : Q := { dqg := 273, drg1 := 322, drs1 := 270, agr1 := 44, aRr1 := 44, agq1 := 44, drg2 := 152, drs2 := 211, agr2 := 45, aRr2 := 43, agq2 := 45 }
def gd_merge11_uarb1_FMIN_hi : Q := { dqg := 274, drg1 := 323, drs1 := 271, agr1 := 44, aRr1 := 44, agq1 := 44, drg2 := 152, drs2 := 212, agr2 := 45, aRr2 := 43, agq2 := 45 }
def gd_merge11_uarb1_FMAX_lo : Q := { dqg := 335, drg1 := 392, drs1 := 333, agr1 := 58, aRr1 := 58, agq1 := 57, drg2 := 188, drs2 := 258, agr2 := 56, aRr2 := 55, agq2 := 56 }
def gd_merge11_uarb1_FMAX_hi : Q := { dqg := 336, drg1 := 393, drs1 := 334, agr1 := 58, aRr1 := 58, agq1 := 57, drg2 := 188, drs2 := 259, agr2 := 56, aRr2 := 55, agq2 := 56 }
def gd_merge11_uarb1_SMIN_lo : Q := { dqg := 654, drg1 := 780, drs1 := 657, agr1 := 121, aRr1 := 121, agq1 := 118, drg2 := 414, drs2 := 538, agr2 := 100, aRr2 := 120, agq2 := 100 }
def gd_merge11_uarb1_SMIN_hi : Q := { dqg := 655, drg1 := 781, drs1 := 658, agr1 := 121, aRr1 := 121, agq1 := 118, drg2 := 414, drs2 := 539, agr2 := 100, aRr2 := 120, agq2 := 100 }
def gd_merge11_uarb1_SMAX_lo : Q := { dqg := 802, drg1 := 949, drs1 := 807, agr1 := 156, aRr1 := 156, agq1 := 157, drg2 := 510, drs2 := 658, agr2 := 124, aRr2 := 153, agq2 := 124 }
def gd_merge11_uarb1_SMAX_hi : Q := { dqg := 803, drg1 := 950, drs1 := 808, agr1 := 156, aRr1 := 156, agq1 := 157, drg2 := 510, drs2 := 659, agr2 := 124, aRr2 := 153, agq2 := 124 }
def gd_merge12_uarb1_FMIN_lo : Q := { dqg := 262, drg1 := 145, drs1 := 152, agr1 := 42, aRr1 := 43, agq1 := 44, drg2 := 208, drs2 := 129, agr2 := 45, aRr2 := 46, agq2 := 45 }
def gd_merge12_uarb1_FMIN_hi : Q := { dqg := 263, drg1 := 145, drs1 := 152, agr1 := 42, aRr1 := 43, agq1 := 44, drg2 := 208, drs2 := 129, agr2 := 45, aRr2 := 46, agq2 := 45 }
def gd_merge12_uarb1_FMAX_lo : Q := { dqg := 323, drg1 := 180, drs1 := 188, agr1 := 53, aRr1 := 55, agq1 := 56, drg2 := 259, drs2 := 160, agr2 := 56, aRr2 := 61, agq2 := 56 }
def gd_merge12_uarb1_FMAX_hi : Q := { dqg := 324, drg1 := 180, drs1 := 188, agr1 := 53, aRr1 := 55, agq1 := 56, drg2 := 259, drs2 := 160, agr2 := 56, aRr2 := 61, agq2 := 56 }
def gd_merge12_uarb1_SMIN_lo : Q := { dqg := 646, drg1 := 392, drs1 := 414, agr1 := 120, aRr1 := 120, agq1 := 120, drg2 := 523, drs2 := 358, agr2 := 100, aRr2 := 120, agq2 := 100 }
def gd_merge12_uarb1_SMIN_hi : Q := { dqg := 647, drg1 := 392, drs1 := 414, agr1 := 120, aRr1 := 120, agq1 := 120, drg2 := 523, drs2 := 358, agr2 := 100, aRr2 := 120, agq2 := 100 }
def gd_merge12_uarb1_SMAX_lo : Q := { dqg := 793, drg1 := 482, drs1 := 510, agr1 := 153, aRr1 := 153, agq1 := 154, drg2 := 645, drs2 := 441, agr2 := 124, aRr2 := 153, agq2 := 124 }
def gd_merge12_uarb1_SMAX_hi : Q := { dqg := 794, drg1 := 482, drs1 := 510, agr1 := 153, aRr1 := 153, agq1 := 154, drg2 := 645, drs2 := 441, agr2 := 124, aRr2 := 153, agq2 := 124 }
def gd_merge12_uarb2_FMIN_lo : Q := { dqg := 182, drg1 := 240, drs1 := 364, agr1 := 43, aRr1 := 44, agq1 := 48, drg2 := 278, drs2 := 252, agr2 := 45, aRr2 := 43, agq2 := 45 }
def gd_merge12_uarb2_FMIN_hi : Q := { dqg := 183, drg1 := 241, drs1 := 365, agr1 := 43, aRr1 := 44, agq1 := 48, drg2 := 279, drs2 := 253, agr2 := 45, aRr2 := 43, agq2 := 45 }
def gd_merge12_uarb2_FMAX_lo : Q := { dqg := 232, drg1 := 321, drs1 := 439, agr1 := 55, aRr1 := 56, agq1 := 61, drg2 := 386, drs2 := 311, agr2 := 56, aRr2 := 55, agq2 := 56 }
def gd_merge12_uarb2_FMAX_hi : Q := { dqg := 233, drg1 := 322, drs1 := 440, agr1 := 55, aRr1 := 56, agq1 := 61, drg2 := 387, drs2 := 312, agr2 := 56, aRr2 := 55, agq2 := 56 }
def gd_merge12_uarb2_SMIN_lo : Q := { dqg := 461, drg1 := 585, drs1 := 836, agr1 := 120, aRr1 := 120, agq1 := 93, drg2 := 659, drs2 := 634, agr2 := 100, aRr2 := 121, agq2 := 100 }
def gd_merge12_uarb2_SMIN_hi : Q := { dqg := 462, drg1 := 586, drs1 := 837, agr1 := 120, aRr1 := 120, agq1 := 93, drg2 := 660, drs2 := 635, agr2 := 100, aRr2 := 121, agq2 := 100 }
def gd_merge12_uarb2_SMAX_lo : Q := { dqg := 604, drg1 := 822, drs1 := 1015, agr1 := 153, aRr1 := 154, agq1 := 119, drg2 := 965, drs2 := 777, agr2 := 124, aRr2 := 154, agq2 := 124 }
def gd_merge12_uarb2_SMAX_hi : Q := { dqg := 605, drg1 := 823, drs1 := 1016, agr1 := 153, aRr1 := 154, agq1 := 119, drg2 := 966, drs2 := 778, agr2 := 124, aRr2 := 154, agq2 := 124 }
def gd_merge2_uarb1_FMIN_lo : Q := { dqg := 129, drg1 := 218, drs1 := 213, agr1 := 44, aRr1 := 44, agq1 := 46, drg2 := 212, drs2 := 210, agr2 := 45, aRr2 := 44, agq2 := 45 }
def gd_merge2_uarb1_FMIN_hi : Q := { dqg := 129, drg1 := 218, drs1 := 213, agr1 := 44, aRr1 := 44, agq1 := 46, drg2 := 212, drs2 := 210, agr2 := 45, aRr2 := 44, agq2 := 45 }
def gd_merge2_uarb1_FMAX_lo : Q := { dqg := 160, drg1 := 272, drs1 := 265, agr1 := 58, aRr1 := 58, agq1 := 61, drg2 := 263, drs2 := 261, agr2 := 56, aRr2 := 57, agq2 := 56 }
def gd_merge2_uarb1_FMAX_hi : Q := { dqg := 160, drg1 := 272, drs1 := 265, agr1 := 58, aRr1 := 58, agq1 := 61, drg2 := 263, drs2 := 261, agr2 := 56, aRr2 := 57, agq2 := 56 }
def gd_merge2_uarb1_SMIN_lo : Q := { dqg := 358, drg1 := 542, drs1 := 534, agr1 := 121, aRr1 := 121, agq1 := 120, drg2 := 527, drs2 := 520, agr2 := 100, aRr2 := 118, agq2 := 100 }
def gd_merge2_uarb1_SMIN_hi : Q := { dqg := 358, drg1 := 542, drs1 := 534, agr1 := 121, aRr1 := 121, agq1 := 120, drg2 := 527, drs2 := 520, agr2 := 100, aRr2 := 118, agq2 := 100 }
def gd_merge2_uarb1_SMAX_lo : Q := { dqg := 441, drg1 := 669, drs1 := 659, agr1 := 156, aRr1 := 156, agq1 := 153, drg2 := 650, drs2 := 642, agr2 := 124, aRr2 := 157, agq2 := 124 }
def gd_merge2_uarb1_SMAX_hi : Q := { dqg := 441, drg1 := 669, drs1 := 659, agr1 := 156, aRr1 := 156, agq1 := 153, drg2 := 650, drs2 := 642, agr2 := 124, aRr2 := 157, agq2 := 124 }
def gd_merge3_uarb1_FMIN_lo : Q := { dqg := 269, drg1 := 282, drs1 := 212, agr1 := 44, aRr1 := 44, agq1 := 43, drg2 := 148, drs2 := 218, agr2 := 45, aRr2 := 44, agq2 := 45 }
def gd_merge3_uarb1_FMIN_hi : Q := { dqg := 270, drg1 := 283, drs1 := 212, agr1 := 44, aRr1 := 44, agq1 := 43, drg2 := 148, drs2 := 218, agr2 := 45, aRr2 := 44, agq2 := 45 }
def gd_merge3_uarb1_FMAX_lo : Q := { dqg := 330, drg1 := 346, drs1 := 263, agr1 := 56, aRr1 := 57, agq1 := 55, drg2 := 184, drs2 := 272, agr2 := 56, aRr2 := 58, agq2 := 56 }
def gd_merge3_uarb1_FMAX_hi : Q := { dqg := 331, drg1 := 347, drs1 := 263, agr1 := 56, aRr1 := 57, agq1 := 55, drg2 := 184, drs2 := 272, agr2 := 56, aRr2 := 58, agq2 := 56 }
def gd_merge3_uarb1_SMIN_lo : Q := { dqg := 681, drg1 := 684, drs1 := 527, agr1 := 120, aRr1 := 118, agq1 := 121, drg2 := 397, drs2 := 542, agr2 := 100, aRr2 := 121, agq2 := 100 }
def gd_merge3_uarb1_SMIN_hi : Q := { dqg := 682, drg1 := 685, drs1 := 527, agr1 := 120, aRr1 := 118, agq1 := 121, drg2 := 397, drs2 := 542, agr2 := 100, aRr2 := 121, agq2 := 100 }
def gd_merge3_uarb1_SMAX_lo : Q := { dqg := 834, drg1 := 837, drs1 := 650, agr1 := 154, aRr1 := 157, agq1 := 154, drg2 := 489, drs2 := 669, agr2 := 124, aRr2 := 156, agq2 := 124 }
def gd_merge3_uarb1_SMAX_hi : Q := { dqg := 835, drg1 := 838, drs1 := 650, agr1 := 154, aRr1 := 157, agq1 := 154, drg2 := 489, drs2 := 669, agr2 := 124, aRr2 := 156, agq2 := 124 }
def gd_merge4_uarb1_FMIN_lo : Q := { dqg := 272, drg1 := 126, drs1 := 71, agr1 := 44, aRr1 := 48, agq1 := 44, drg2 := 258, drs2 := 211, agr2 := 45, aRr2 := 44, agq2 := 45 }
def gd_merge4_uarb1_FMIN_hi : Q := { dqg := 273, drg1 := 126, drs1 := 71, agr1 := 44, aRr1 := 48, agq1 := 44, drg2 := 259, drs2 := 211, agr2 := 45, aRr2 := 44, agq2 := 45 }
def gd_merge4_uarb1_FMAX_lo : Q := { dqg := 333, drg1 := 156, drs1 := 89, agr1 := 57, aRr1 := 63, agq1 := 56, drg2 := 303, drs2 := 262, agr2 := 56, aRr2 := 56, agq2 := 56 }
def gd_merge4_uarb1_FMAX_hi : Q := { dqg := 334, drg1 := 156, drs1 := 89, agr1 := 57, aRr1 := 63, agq1 := 56, drg2 := 304, drs2 := 262, agr2 := 56, aRr2 := 56, agq2 := 56 }
def gd_merge4_uarb1_SMIN_lo : Q := { dqg := 693, drg1 := 343, drs1 := 206, agr1 := 120, aRr1 := 94, agq1 := 120, drg2 := 567, drs2 := 531, agr2 := 100, aRr2 := 120, agq2 := 100 }
def gd_merge4_uarb1_SMIN_hi : Q := { dqg := 694, drg1 := 343, drs1 := 206, agr1 := 120, aRr1 := 94, agq1 := 120, drg2 := 568, drs2 := 531, agr2 := 100, aRr2 := 120, agq2 := 100 }
def gd_merge4_uarb1_SMAX_lo : Q := { dqg := 849, drg1 := 422, drs1 := 252, agr1 := 153, aRr1 := 120, agq1 := 154, drg2 := 681, drs2 := 655, agr2 := 124, aRr2 := 154, agq2 := 124 }
def gd_merge4_uarb1_SMAX_hi : Q := { dqg := 850, drg1 := 422, drs1 := 252, agr1 := 153, aRr1 := 120, agq1 := 154, drg2 := 682, drs2 := 655, agr2 := 124, aRr2 := 154, agq2 := 124 }
def gd_merge6_uarb1_FMIN_lo : Q := { dqg := 273, drg1 := 128, drs1 := 209, agr1 := 46, aRr1 := 43, agq1 := 44, drg2 := 80, drs2 := 211, agr2 := 45, aRr2 := 44, agq2 := 45 }
def gd_merge6_uarb1_FMIN_hi : Q := { dqg := 274, drg1 := 128, drs1 := 209, agr1 := 46, aRr1 := 43, agq1 := 44, drg2 := 80, drs2 := 211, agr2 := 45, aRr2 := 44, agq2 := 45 }
def gd_merge6_uarb1_FMAX_lo : Q := { dqg := 335, drg1 := 159, drs1 := 260, agr1 := 61, aRr1 := 55, agq1 := 58, drg2 := 99, drs2 := 262, agr2 := 56, aRr2 := 56, agq2 := 56 }
def gd_merge6_uarb1_FMAX_hi : Q := { dqg := 336, drg1 := 159, drs1 := 260, agr1 := 61, aRr1 := 55, agq1 := 58, drg2 := 99, drs2 := 262, agr2 := 56, aRr2 := 56, agq2 := 56 }
def gd_merge6_uarb1_SMIN_lo : Q := { dqg := 692, drg1 := 356, drs1 := 523, agr1 := 120, aRr1 := 121, agq1 := 121, drg2 := 225, drs2 := 531, agr2 := 100, aRr2 := 120, agq2 := 100 }
def gd_merge6_uarb1_SMIN_hi : Q := { dqg := 693, drg1 := 356, drs1 := 523, agr1 := 120, aRr1 := 121, agq1 := 121, drg2 := 225, drs2 := 531, agr2 := 100, aRr2 := 120, agq2 := 100 }
def gd_merge6_uarb1_SMAX_lo : Q := { dqg := 848, drg1 := 438, drs1 := 645, agr1 := 153, aRr1 := 154, agq1 := 156, drg2 := 275, drs2 := 655, agr2 := 124, aRr2 := 154, agq2 := 124 }
def gd_merge6_uarb1_SMAX_hi : Q := { dqg := 849, drg1 := 438, drs1 := 645, agr1 := 153, aRr1 := 154, agq1 := 156, drg2 := 275, drs2 := 655, agr2 := 124, aRr2 := 154, agq2 := 124 }
def gd_merge9_uarb1_FMIN_lo : Q := { dqg := 71, drg1 := 145, drs1 := 76, agr1 := 42, aRr1 := 48, agq1 := 48, drg2 := 210, drs2 := 218, agr2 := 45, aRr2 := 44, agq2 := 45 }
def gd_merge9_uarb1_FMIN_hi : Q := { dqg := 71, drg1 := 145, drs1 := 76, agr1 := 42, aRr1 := 48, agq1 := 48, drg2 := 210, drs2 := 218, agr2 := 45, aRr2 := 44, agq2 := 45 }
def gd_merge9_uarb1_FMAX_lo : Q := { dqg := 89, drg1 := 180, drs1 := 95, agr1 := 53, aRr1 := 61, agq1 := 63, drg2 := 261, drs2 := 272, agr2 := 56, aRr2 := 58, agq2 := 56 }
def gd_merge9_uarb1_FMAX_hi : Q := { dqg := 89, drg1 := 180, drs1 := 95, agr1 := 53, aRr1 := 61, agq1 := 63, drg2 := 261, drs2 := 272, agr2 := 56, aRr2 := 58, agq2 := 56 }
def gd_merge9_uarb1_SMIN_lo : Q := { dqg := 205, drg1 := 392, drs1 := 216, agr1 := 120, aRr1 := 93, agq1 := 94, drg2 := 530, drs2 := 542, agr2 := 100, aRr2 := 121, agq2 := 100 }
def gd_merge9_uarb1_SMIN_hi : Q := { dqg := 205, drg1 := 392, drs1 := 216, agr1 := 120, aRr1 := 93, agq1 := 94, drg2 := 530, drs2 := 542, agr2 := 100, aRr2 := 121, agq2 := 100 }
def gd_merge9_uarb1_SMAX_lo : Q := { dqg := 250, drg1 := 482, drs1 := 264, agr1 := 153, aRr1 := 119, agq1 := 120, drg2 := 654, drs2 := 669, agr2 := 124, aRr2 := 156, agq2 := 124 }
def gd_merge9_uarb1_SMAX_hi : Q := { dqg := 250, drg1 := 482, drs1 := 264, agr1 := 153, aRr1 := 119, agq1 := 120, drg2 := 654, drs2 := 669, agr2 := 124, aRr2 := 156, agq2 := 124 }

/-! ## Per row: RT1 and RT1b hold on the whole hull, for every server

`_ok` gives `okRow` and the exact worst-hull-point margins (m1, m2). -/

theorem g2_merge10_uarb1_FMIN_ok : okRow g2_merge10_uarb1_FMIN_lo g2_merge10_uarb1_FMIN_hi = true ∧
    (mix1 g2_merge10_uarb1_FMIN_lo g2_merge10_uarb1_FMIN_hi).m1 = 172 ∧ (mix2 g2_merge10_uarb1_FMIN_lo g2_merge10_uarb1_FMIN_hi).m2 = 406 := by decide
theorem g2_merge10_uarb1_FMAX_ok : okRow g2_merge10_uarb1_FMAX_lo g2_merge10_uarb1_FMAX_hi = true ∧
    (mix1 g2_merge10_uarb1_FMAX_lo g2_merge10_uarb1_FMAX_hi).m1 = 238 ∧ (mix2 g2_merge10_uarb1_FMAX_lo g2_merge10_uarb1_FMAX_hi).m2 = 543 := by decide
theorem g2_merge10_uarb1_SMIN_ok : okRow g2_merge10_uarb1_SMIN_lo g2_merge10_uarb1_SMIN_hi = true ∧
    (mix1 g2_merge10_uarb1_SMIN_lo g2_merge10_uarb1_SMIN_hi).m1 = 464 ∧ (mix2 g2_merge10_uarb1_SMIN_lo g2_merge10_uarb1_SMIN_hi).m2 = 973 := by decide
theorem g2_merge10_uarb1_SMAX_ok : okRow g2_merge10_uarb1_SMAX_lo g2_merge10_uarb1_SMAX_hi = true ∧
    (mix1 g2_merge10_uarb1_SMAX_lo g2_merge10_uarb1_SMAX_hi).m1 = 659 ∧ (mix2 g2_merge10_uarb1_SMAX_lo g2_merge10_uarb1_SMAX_hi).m2 = 1359 := by decide
theorem g2_merge11_uarb1_FMIN_ok : okRow g2_merge11_uarb1_FMIN_lo g2_merge11_uarb1_FMIN_hi = true ∧
    (mix1 g2_merge11_uarb1_FMIN_lo g2_merge11_uarb1_FMIN_hi).m1 = 947 ∧ (mix2 g2_merge11_uarb1_FMIN_lo g2_merge11_uarb1_FMIN_hi).m2 = 716 := by decide
theorem g2_merge11_uarb1_FMAX_ok : okRow g2_merge11_uarb1_FMAX_lo g2_merge11_uarb1_FMAX_hi = true ∧
    (mix1 g2_merge11_uarb1_FMAX_lo g2_merge11_uarb1_FMAX_hi).m1 = 1089 ∧ (mix2 g2_merge11_uarb1_FMAX_lo g2_merge11_uarb1_FMAX_hi).m2 = 808 := by decide
theorem g2_merge11_uarb1_SMIN_ok : okRow g2_merge11_uarb1_SMIN_lo g2_merge11_uarb1_SMIN_hi = true ∧
    (mix1 g2_merge11_uarb1_SMIN_lo g2_merge11_uarb1_SMIN_hi).m1 = 1798 ∧ (mix2 g2_merge11_uarb1_SMIN_lo g2_merge11_uarb1_SMIN_hi).m2 = 1351 := by decide
theorem g2_merge11_uarb1_SMAX_ok : okRow g2_merge11_uarb1_SMAX_lo g2_merge11_uarb1_SMAX_hi = true ∧
    (mix1 g2_merge11_uarb1_SMAX_lo g2_merge11_uarb1_SMAX_hi).m1 = 2117 ∧ (mix2 g2_merge11_uarb1_SMAX_lo g2_merge11_uarb1_SMAX_hi).m2 = 1574 := by decide
theorem g2_merge12_uarb1_FMIN_ok : okRow g2_merge12_uarb1_FMIN_lo g2_merge12_uarb1_FMIN_hi = true ∧
    (mix1 g2_merge12_uarb1_FMIN_lo g2_merge12_uarb1_FMIN_hi).m1 = 98 ∧ (mix2 g2_merge12_uarb1_FMIN_lo g2_merge12_uarb1_FMIN_hi).m2 = 108 := by decide
theorem g2_merge12_uarb1_FMAX_ok : okRow g2_merge12_uarb1_FMAX_lo g2_merge12_uarb1_FMAX_hi = true ∧
    (mix1 g2_merge12_uarb1_FMAX_lo g2_merge12_uarb1_FMAX_hi).m1 = 117 ∧ (mix2 g2_merge12_uarb1_FMAX_lo g2_merge12_uarb1_FMAX_hi).m2 = 138 := by decide
theorem g2_merge12_uarb1_SMIN_ok : okRow g2_merge12_uarb1_SMIN_lo g2_merge12_uarb1_SMIN_hi = true ∧
    (mix1 g2_merge12_uarb1_SMIN_lo g2_merge12_uarb1_SMIN_hi).m1 = 254 ∧ (mix2 g2_merge12_uarb1_SMIN_lo g2_merge12_uarb1_SMIN_hi).m2 = 326 := by decide
theorem g2_merge12_uarb1_SMAX_ok : okRow g2_merge12_uarb1_SMAX_lo g2_merge12_uarb1_SMAX_hi = true ∧
    (mix1 g2_merge12_uarb1_SMAX_lo g2_merge12_uarb1_SMAX_hi).m1 = 304 ∧ (mix2 g2_merge12_uarb1_SMAX_lo g2_merge12_uarb1_SMAX_hi).m2 = 403 := by decide
theorem g2_merge12_uarb2_FMIN_ok : okRow g2_merge12_uarb2_FMIN_lo g2_merge12_uarb2_FMIN_hi = true ∧
    (mix1 g2_merge12_uarb2_FMIN_lo g2_merge12_uarb2_FMIN_hi).m1 = 395 ∧ (mix2 g2_merge12_uarb2_FMIN_lo g2_merge12_uarb2_FMIN_hi).m2 = 195 := by decide
theorem g2_merge12_uarb2_FMAX_ok : okRow g2_merge12_uarb2_FMAX_lo g2_merge12_uarb2_FMAX_hi = true ∧
    (mix1 g2_merge12_uarb2_FMAX_lo g2_merge12_uarb2_FMAX_hi).m1 = 494 ∧ (mix2 g2_merge12_uarb2_FMAX_lo g2_merge12_uarb2_FMAX_hi).m2 = 246 := by decide
theorem g2_merge12_uarb2_SMIN_ok : okRow g2_merge12_uarb2_SMIN_lo g2_merge12_uarb2_SMIN_hi = true ∧
    (mix1 g2_merge12_uarb2_SMIN_lo g2_merge12_uarb2_SMIN_hi).m1 = 983 ∧ (mix2 g2_merge12_uarb2_SMIN_lo g2_merge12_uarb2_SMIN_hi).m2 = 565 := by decide
theorem g2_merge12_uarb2_SMAX_ok : okRow g2_merge12_uarb2_SMAX_lo g2_merge12_uarb2_SMAX_hi = true ∧
    (mix1 g2_merge12_uarb2_SMAX_lo g2_merge12_uarb2_SMAX_hi).m1 = 1218 ∧ (mix2 g2_merge12_uarb2_SMAX_lo g2_merge12_uarb2_SMAX_hi).m2 = 708 := by decide
theorem g2_merge2_uarb1_FMIN_ok : okRow g2_merge2_uarb1_FMIN_lo g2_merge2_uarb1_FMIN_hi = true ∧
    (mix1 g2_merge2_uarb1_FMIN_lo g2_merge2_uarb1_FMIN_hi).m1 = 93 ∧ (mix2 g2_merge2_uarb1_FMIN_lo g2_merge2_uarb1_FMIN_hi).m2 = 298 := by decide
theorem g2_merge2_uarb1_FMAX_ok : okRow g2_merge2_uarb1_FMAX_lo g2_merge2_uarb1_FMAX_hi = true ∧
    (mix1 g2_merge2_uarb1_FMAX_lo g2_merge2_uarb1_FMAX_hi).m1 = 111 ∧ (mix2 g2_merge2_uarb1_FMAX_lo g2_merge2_uarb1_FMAX_hi).m2 = 368 := by decide
theorem g2_merge2_uarb1_SMIN_ok : okRow g2_merge2_uarb1_SMIN_lo g2_merge2_uarb1_SMIN_hi = true ∧
    (mix1 g2_merge2_uarb1_SMIN_lo g2_merge2_uarb1_SMIN_hi).m1 = 288 ∧ (mix2 g2_merge2_uarb1_SMIN_lo g2_merge2_uarb1_SMIN_hi).m2 = 729 := by decide
theorem g2_merge2_uarb1_SMAX_ok : okRow g2_merge2_uarb1_SMAX_lo g2_merge2_uarb1_SMAX_hi = true ∧
    (mix1 g2_merge2_uarb1_SMAX_lo g2_merge2_uarb1_SMAX_hi).m1 = 345 ∧ (mix2 g2_merge2_uarb1_SMAX_lo g2_merge2_uarb1_SMAX_hi).m2 = 931 := by decide
theorem g2_merge3_uarb1_FMIN_ok : okRow g2_merge3_uarb1_FMIN_lo g2_merge3_uarb1_FMIN_hi = true ∧
    (mix1 g2_merge3_uarb1_FMIN_lo g2_merge3_uarb1_FMIN_hi).m1 = 253 ∧ (mix2 g2_merge3_uarb1_FMIN_lo g2_merge3_uarb1_FMIN_hi).m2 = 35 := by decide
theorem g2_merge3_uarb1_FMAX_ok : okRow g2_merge3_uarb1_FMAX_lo g2_merge3_uarb1_FMAX_hi = true ∧
    (mix1 g2_merge3_uarb1_FMAX_lo g2_merge3_uarb1_FMAX_hi).m1 = 310 ∧ (mix2 g2_merge3_uarb1_FMAX_lo g2_merge3_uarb1_FMAX_hi).m2 = 45 := by decide
theorem g2_merge3_uarb1_SMIN_ok : okRow g2_merge3_uarb1_SMIN_lo g2_merge3_uarb1_SMIN_hi = true ∧
    (mix1 g2_merge3_uarb1_SMIN_lo g2_merge3_uarb1_SMIN_hi).m1 = 606 ∧ (mix2 g2_merge3_uarb1_SMIN_lo g2_merge3_uarb1_SMIN_hi).m2 = 91 := by decide
theorem g2_merge3_uarb1_SMAX_ok : okRow g2_merge3_uarb1_SMAX_lo g2_merge3_uarb1_SMAX_hi = true ∧
    (mix1 g2_merge3_uarb1_SMAX_lo g2_merge3_uarb1_SMAX_hi).m1 = 741 ∧ (mix2 g2_merge3_uarb1_SMAX_lo g2_merge3_uarb1_SMAX_hi).m2 = 110 := by decide
theorem g2_merge4_uarb1_FMIN_ok : okRow g2_merge4_uarb1_FMIN_lo g2_merge4_uarb1_FMIN_hi = true ∧
    (mix1 g2_merge4_uarb1_FMIN_lo g2_merge4_uarb1_FMIN_hi).m1 = 372 ∧ (mix2 g2_merge4_uarb1_FMIN_lo g2_merge4_uarb1_FMIN_hi).m2 = 388 := by decide
theorem g2_merge4_uarb1_FMAX_ok : okRow g2_merge4_uarb1_FMAX_lo g2_merge4_uarb1_FMAX_hi = true ∧
    (mix1 g2_merge4_uarb1_FMAX_lo g2_merge4_uarb1_FMAX_hi).m1 = 456 ∧ (mix2 g2_merge4_uarb1_FMAX_lo g2_merge4_uarb1_FMAX_hi).m2 = 476 := by decide
theorem g2_merge4_uarb1_SMIN_ok : okRow g2_merge4_uarb1_SMIN_lo g2_merge4_uarb1_SMIN_hi = true ∧
    (mix1 g2_merge4_uarb1_SMIN_lo g2_merge4_uarb1_SMIN_hi).m1 = 902 ∧ (mix2 g2_merge4_uarb1_SMIN_lo g2_merge4_uarb1_SMIN_hi).m2 = 942 := by decide
theorem g2_merge4_uarb1_SMAX_ok : okRow g2_merge4_uarb1_SMAX_lo g2_merge4_uarb1_SMAX_hi = true ∧
    (mix1 g2_merge4_uarb1_SMAX_lo g2_merge4_uarb1_SMAX_hi).m1 = 1105 ∧ (mix2 g2_merge4_uarb1_SMAX_lo g2_merge4_uarb1_SMAX_hi).m2 = 1168 := by decide
theorem g2_merge6_uarb1_FMIN_ok : okRow g2_merge6_uarb1_FMIN_lo g2_merge6_uarb1_FMIN_hi = true ∧
    (mix1 g2_merge6_uarb1_FMIN_lo g2_merge6_uarb1_FMIN_hi).m1 = 361 ∧ (mix2 g2_merge6_uarb1_FMIN_lo g2_merge6_uarb1_FMIN_hi).m2 = 234 := by decide
theorem g2_merge6_uarb1_FMAX_ok : okRow g2_merge6_uarb1_FMAX_lo g2_merge6_uarb1_FMAX_hi = true ∧
    (mix1 g2_merge6_uarb1_FMAX_lo g2_merge6_uarb1_FMAX_hi).m1 = 455 ∧ (mix2 g2_merge6_uarb1_FMAX_lo g2_merge6_uarb1_FMAX_hi).m2 = 289 := by decide
theorem g2_merge6_uarb1_SMIN_ok : okRow g2_merge6_uarb1_SMIN_lo g2_merge6_uarb1_SMIN_hi = true ∧
    (mix1 g2_merge6_uarb1_SMIN_lo g2_merge6_uarb1_SMIN_hi).m1 = 830 ∧ (mix2 g2_merge6_uarb1_SMIN_lo g2_merge6_uarb1_SMIN_hi).m2 = 634 := by decide
theorem g2_merge6_uarb1_SMAX_ok : okRow g2_merge6_uarb1_SMAX_lo g2_merge6_uarb1_SMAX_hi = true ∧
    (mix1 g2_merge6_uarb1_SMAX_lo g2_merge6_uarb1_SMAX_hi).m1 = 1061 ∧ (mix2 g2_merge6_uarb1_SMAX_lo g2_merge6_uarb1_SMAX_hi).m2 = 787 := by decide
theorem g2_merge9_uarb1_FMIN_ok : okRow g2_merge9_uarb1_FMIN_lo g2_merge9_uarb1_FMIN_hi = true ∧
    (mix1 g2_merge9_uarb1_FMIN_lo g2_merge9_uarb1_FMIN_hi).m1 = 169 ∧ (mix2 g2_merge9_uarb1_FMIN_lo g2_merge9_uarb1_FMIN_hi).m2 = 166 := by decide
theorem g2_merge9_uarb1_FMAX_ok : okRow g2_merge9_uarb1_FMAX_lo g2_merge9_uarb1_FMAX_hi = true ∧
    (mix1 g2_merge9_uarb1_FMAX_lo g2_merge9_uarb1_FMAX_hi).m1 = 210 ∧ (mix2 g2_merge9_uarb1_FMAX_lo g2_merge9_uarb1_FMAX_hi).m2 = 210 := by decide
theorem g2_merge9_uarb1_SMIN_ok : okRow g2_merge9_uarb1_SMIN_lo g2_merge9_uarb1_SMIN_hi = true ∧
    (mix1 g2_merge9_uarb1_SMIN_lo g2_merge9_uarb1_SMIN_hi).m1 = 442 ∧ (mix2 g2_merge9_uarb1_SMIN_lo g2_merge9_uarb1_SMIN_hi).m2 = 484 := by decide
theorem g2_merge9_uarb1_SMAX_ok : okRow g2_merge9_uarb1_SMAX_lo g2_merge9_uarb1_SMAX_hi = true ∧
    (mix1 g2_merge9_uarb1_SMAX_lo g2_merge9_uarb1_SMAX_hi).m1 = 545 ∧ (mix2 g2_merge9_uarb1_SMAX_lo g2_merge9_uarb1_SMAX_hi).m2 = 607 := by decide
theorem g3_merge10_uarb1_FMIN_ok : okRow g3_merge10_uarb1_FMIN_lo g3_merge10_uarb1_FMIN_hi = true ∧
    (mix1 g3_merge10_uarb1_FMIN_lo g3_merge10_uarb1_FMIN_hi).m1 = 394 ∧ (mix2 g3_merge10_uarb1_FMIN_lo g3_merge10_uarb1_FMIN_hi).m2 = 197 := by decide
theorem g3_merge10_uarb1_FMAX_ok : okRow g3_merge10_uarb1_FMAX_lo g3_merge10_uarb1_FMAX_hi = true ∧
    (mix1 g3_merge10_uarb1_FMAX_lo g3_merge10_uarb1_FMAX_hi).m1 = 477 ∧ (mix2 g3_merge10_uarb1_FMAX_lo g3_merge10_uarb1_FMAX_hi).m2 = 256 := by decide
theorem g3_merge10_uarb1_SMIN_ok : okRow g3_merge10_uarb1_SMIN_lo g3_merge10_uarb1_SMIN_hi = true ∧
    (mix1 g3_merge10_uarb1_SMIN_lo g3_merge10_uarb1_SMIN_hi).m1 = 960 ∧ (mix2 g3_merge10_uarb1_SMIN_lo g3_merge10_uarb1_SMIN_hi).m2 = 563 := by decide
theorem g3_merge10_uarb1_SMAX_ok : okRow g3_merge10_uarb1_SMAX_lo g3_merge10_uarb1_SMAX_hi = true ∧
    (mix1 g3_merge10_uarb1_SMAX_lo g3_merge10_uarb1_SMAX_hi).m1 = 1170 ∧ (mix2 g3_merge10_uarb1_SMAX_lo g3_merge10_uarb1_SMAX_hi).m2 = 714 := by decide
theorem g3_merge11_uarb1_FMIN_ok : okRow g3_merge11_uarb1_FMIN_lo g3_merge11_uarb1_FMIN_hi = true ∧
    (mix1 g3_merge11_uarb1_FMIN_lo g3_merge11_uarb1_FMIN_hi).m1 = 117 ∧ (mix2 g3_merge11_uarb1_FMIN_lo g3_merge11_uarb1_FMIN_hi).m2 = 115 := by decide
theorem g3_merge11_uarb1_FMAX_ok : okRow g3_merge11_uarb1_FMAX_lo g3_merge11_uarb1_FMAX_hi = true ∧
    (mix1 g3_merge11_uarb1_FMAX_lo g3_merge11_uarb1_FMAX_hi).m1 = 146 ∧ (mix2 g3_merge11_uarb1_FMAX_lo g3_merge11_uarb1_FMAX_hi).m2 = 148 := by decide
theorem g3_merge11_uarb1_SMIN_ok : okRow g3_merge11_uarb1_SMIN_lo g3_merge11_uarb1_SMIN_hi = true ∧
    (mix1 g3_merge11_uarb1_SMIN_lo g3_merge11_uarb1_SMIN_hi).m1 = 310 ∧ (mix2 g3_merge11_uarb1_SMIN_lo g3_merge11_uarb1_SMIN_hi).m2 = 316 := by decide
theorem g3_merge11_uarb1_SMAX_ok : okRow g3_merge11_uarb1_SMAX_lo g3_merge11_uarb1_SMAX_hi = true ∧
    (mix1 g3_merge11_uarb1_SMAX_lo g3_merge11_uarb1_SMAX_hi).m1 = 381 ∧ (mix2 g3_merge11_uarb1_SMAX_lo g3_merge11_uarb1_SMAX_hi).m2 = 396 := by decide
theorem g3_merge12_uarb1_FMIN_ok : okRow g3_merge12_uarb1_FMIN_lo g3_merge12_uarb1_FMIN_hi = true ∧
    (mix1 g3_merge12_uarb1_FMIN_lo g3_merge12_uarb1_FMIN_hi).m1 = 181 ∧ (mix2 g3_merge12_uarb1_FMIN_lo g3_merge12_uarb1_FMIN_hi).m2 = 32 := by decide
theorem g3_merge12_uarb1_FMAX_ok : okRow g3_merge12_uarb1_FMAX_lo g3_merge12_uarb1_FMAX_hi = true ∧
    (mix1 g3_merge12_uarb1_FMAX_lo g3_merge12_uarb1_FMAX_hi).m1 = 226 ∧ (mix2 g3_merge12_uarb1_FMAX_lo g3_merge12_uarb1_FMAX_hi).m2 = 46 := by decide
theorem g3_merge12_uarb1_SMIN_ok : okRow g3_merge12_uarb1_SMIN_lo g3_merge12_uarb1_SMIN_hi = true ∧
    (mix1 g3_merge12_uarb1_SMIN_lo g3_merge12_uarb1_SMIN_hi).m1 = 436 ∧ (mix2 g3_merge12_uarb1_SMIN_lo g3_merge12_uarb1_SMIN_hi).m2 = 140 := by decide
theorem g3_merge12_uarb1_SMAX_ok : okRow g3_merge12_uarb1_SMAX_lo g3_merge12_uarb1_SMAX_hi = true ∧
    (mix1 g3_merge12_uarb1_SMAX_lo g3_merge12_uarb1_SMAX_hi).m1 = 537 ∧ (mix2 g3_merge12_uarb1_SMAX_lo g3_merge12_uarb1_SMAX_hi).m2 = 178 := by decide
theorem g3_merge12_uarb2_FMIN_ok : okRow g3_merge12_uarb2_FMIN_lo g3_merge12_uarb2_FMIN_hi = true ∧
    (mix1 g3_merge12_uarb2_FMIN_lo g3_merge12_uarb2_FMIN_hi).m1 = 292 ∧ (mix2 g3_merge12_uarb2_FMIN_lo g3_merge12_uarb2_FMIN_hi).m2 = 117 := by decide
theorem g3_merge12_uarb2_FMAX_ok : okRow g3_merge12_uarb2_FMAX_lo g3_merge12_uarb2_FMAX_hi = true ∧
    (mix1 g3_merge12_uarb2_FMAX_lo g3_merge12_uarb2_FMAX_hi).m1 = 358 ∧ (mix2 g3_merge12_uarb2_FMAX_lo g3_merge12_uarb2_FMAX_hi).m2 = 151 := by decide
theorem g3_merge12_uarb2_SMIN_ok : okRow g3_merge12_uarb2_SMIN_lo g3_merge12_uarb2_SMIN_hi = true ∧
    (mix1 g3_merge12_uarb2_SMIN_lo g3_merge12_uarb2_SMIN_hi).m1 = 660 ∧ (mix2 g3_merge12_uarb2_SMIN_lo g3_merge12_uarb2_SMIN_hi).m2 = 318 := by decide
theorem g3_merge12_uarb2_SMAX_ok : okRow g3_merge12_uarb2_SMAX_lo g3_merge12_uarb2_SMAX_hi = true ∧
    (mix1 g3_merge12_uarb2_SMAX_lo g3_merge12_uarb2_SMAX_hi).m1 = 804 ∧ (mix2 g3_merge12_uarb2_SMAX_lo g3_merge12_uarb2_SMAX_hi).m2 = 399 := by decide
theorem g3_merge2_uarb1_FMIN_ok : okRow g3_merge2_uarb1_FMIN_lo g3_merge2_uarb1_FMIN_hi = true ∧
    (mix1 g3_merge2_uarb1_FMIN_lo g3_merge2_uarb1_FMIN_hi).m1 = 168 ∧ (mix2 g3_merge2_uarb1_FMIN_lo g3_merge2_uarb1_FMIN_hi).m2 = 181 := by decide
theorem g3_merge2_uarb1_FMAX_ok : okRow g3_merge2_uarb1_FMAX_lo g3_merge2_uarb1_FMAX_hi = true ∧
    (mix1 g3_merge2_uarb1_FMAX_lo g3_merge2_uarb1_FMAX_hi).m1 = 210 ∧ (mix2 g3_merge2_uarb1_FMAX_lo g3_merge2_uarb1_FMAX_hi).m2 = 228 := by decide
theorem g3_merge2_uarb1_SMIN_ok : okRow g3_merge2_uarb1_SMIN_lo g3_merge2_uarb1_SMIN_hi = true ∧
    (mix1 g3_merge2_uarb1_SMIN_lo g3_merge2_uarb1_SMIN_hi).m1 = 443 ∧ (mix2 g3_merge2_uarb1_SMIN_lo g3_merge2_uarb1_SMIN_hi).m2 = 468 := by decide
theorem g3_merge2_uarb1_SMAX_ok : okRow g3_merge2_uarb1_SMAX_lo g3_merge2_uarb1_SMAX_hi = true ∧
    (mix1 g3_merge2_uarb1_SMAX_lo g3_merge2_uarb1_SMAX_hi).m1 = 548 ∧ (mix2 g3_merge2_uarb1_SMAX_lo g3_merge2_uarb1_SMAX_hi).m2 = 584 := by decide
theorem g3_merge3_uarb1_FMIN_ok : okRow g3_merge3_uarb1_FMIN_lo g3_merge3_uarb1_FMIN_hi = true ∧
    (mix1 g3_merge3_uarb1_FMIN_lo g3_merge3_uarb1_FMIN_hi).m1 = 164 ∧ (mix2 g3_merge3_uarb1_FMIN_lo g3_merge3_uarb1_FMIN_hi).m2 = 241 := by decide
theorem g3_merge3_uarb1_FMAX_ok : okRow g3_merge3_uarb1_FMAX_lo g3_merge3_uarb1_FMAX_hi = true ∧
    (mix1 g3_merge3_uarb1_FMAX_lo g3_merge3_uarb1_FMAX_hi).m1 = 203 ∧ (mix2 g3_merge3_uarb1_FMAX_lo g3_merge3_uarb1_FMAX_hi).m2 = 300 := by decide
theorem g3_merge3_uarb1_SMIN_ok : okRow g3_merge3_uarb1_SMIN_lo g3_merge3_uarb1_SMIN_hi = true ∧
    (mix1 g3_merge3_uarb1_SMIN_lo g3_merge3_uarb1_SMIN_hi).m1 = 415 ∧ (mix2 g3_merge3_uarb1_SMIN_lo g3_merge3_uarb1_SMIN_hi).m2 = 578 := by decide
theorem g3_merge3_uarb1_SMAX_ok : okRow g3_merge3_uarb1_SMAX_lo g3_merge3_uarb1_SMAX_hi = true ∧
    (mix1 g3_merge3_uarb1_SMAX_lo g3_merge3_uarb1_SMAX_hi).m1 = 505 ∧ (mix2 g3_merge3_uarb1_SMAX_lo g3_merge3_uarb1_SMAX_hi).m2 = 715 := by decide
theorem g3_merge4_uarb1_FMIN_ok : okRow g3_merge4_uarb1_FMIN_lo g3_merge4_uarb1_FMIN_hi = true ∧
    (mix1 g3_merge4_uarb1_FMIN_lo g3_merge4_uarb1_FMIN_hi).m1 = 406 ∧ (mix2 g3_merge4_uarb1_FMIN_lo g3_merge4_uarb1_FMIN_hi).m2 = 269 := by decide
theorem g3_merge4_uarb1_FMAX_ok : okRow g3_merge4_uarb1_FMAX_lo g3_merge4_uarb1_FMAX_hi = true ∧
    (mix1 g3_merge4_uarb1_FMAX_lo g3_merge4_uarb1_FMAX_hi).m1 = 502 ∧ (mix2 g3_merge4_uarb1_FMAX_lo g3_merge4_uarb1_FMAX_hi).m2 = 343 := by decide
theorem g3_merge4_uarb1_SMIN_ok : okRow g3_merge4_uarb1_SMIN_lo g3_merge4_uarb1_SMIN_hi = true ∧
    (mix1 g3_merge4_uarb1_SMIN_lo g3_merge4_uarb1_SMIN_hi).m1 = 1049 ∧ (mix2 g3_merge4_uarb1_SMIN_lo g3_merge4_uarb1_SMIN_hi).m2 = 728 := by decide
theorem g3_merge4_uarb1_SMAX_ok : okRow g3_merge4_uarb1_SMAX_lo g3_merge4_uarb1_SMAX_hi = true ∧
    (mix1 g3_merge4_uarb1_SMAX_lo g3_merge4_uarb1_SMAX_hi).m1 = 1300 ∧ (mix2 g3_merge4_uarb1_SMAX_lo g3_merge4_uarb1_SMAX_hi).m2 = 909 := by decide
theorem g3_merge6_uarb1_FMIN_ok : okRow g3_merge6_uarb1_FMIN_lo g3_merge6_uarb1_FMIN_hi = true ∧
    (mix1 g3_merge6_uarb1_FMIN_lo g3_merge6_uarb1_FMIN_hi).m1 = 257 ∧ (mix2 g3_merge6_uarb1_FMIN_lo g3_merge6_uarb1_FMIN_hi).m2 = 321 := by decide
theorem g3_merge6_uarb1_FMAX_ok : okRow g3_merge6_uarb1_FMAX_lo g3_merge6_uarb1_FMAX_hi = true ∧
    (mix1 g3_merge6_uarb1_FMAX_lo g3_merge6_uarb1_FMAX_hi).m1 = 318 ∧ (mix2 g3_merge6_uarb1_FMAX_lo g3_merge6_uarb1_FMAX_hi).m2 = 405 := by decide
theorem g3_merge6_uarb1_SMIN_ok : okRow g3_merge6_uarb1_SMIN_lo g3_merge6_uarb1_SMIN_hi = true ∧
    (mix1 g3_merge6_uarb1_SMIN_lo g3_merge6_uarb1_SMIN_hi).m1 = 617 ∧ (mix2 g3_merge6_uarb1_SMIN_lo g3_merge6_uarb1_SMIN_hi).m2 = 810 := by decide
theorem g3_merge6_uarb1_SMAX_ok : okRow g3_merge6_uarb1_SMAX_lo g3_merge6_uarb1_SMAX_hi = true ∧
    (mix1 g3_merge6_uarb1_SMAX_lo g3_merge6_uarb1_SMAX_hi).m1 = 762 ∧ (mix2 g3_merge6_uarb1_SMAX_lo g3_merge6_uarb1_SMAX_hi).m2 = 1011 := by decide
theorem g3_merge9_uarb1_FMIN_ok : okRow g3_merge9_uarb1_FMIN_lo g3_merge9_uarb1_FMIN_hi = true ∧
    (mix1 g3_merge9_uarb1_FMIN_lo g3_merge9_uarb1_FMIN_hi).m1 = 200 ∧ (mix2 g3_merge9_uarb1_FMIN_lo g3_merge9_uarb1_FMIN_hi).m2 = 120 := by decide
theorem g3_merge9_uarb1_FMAX_ok : okRow g3_merge9_uarb1_FMAX_lo g3_merge9_uarb1_FMAX_hi = true ∧
    (mix1 g3_merge9_uarb1_FMAX_lo g3_merge9_uarb1_FMAX_hi).m1 = 246 ∧ (mix2 g3_merge9_uarb1_FMAX_lo g3_merge9_uarb1_FMAX_hi).m2 = 147 := by decide
theorem g3_merge9_uarb1_SMIN_ok : okRow g3_merge9_uarb1_SMIN_lo g3_merge9_uarb1_SMIN_hi = true ∧
    (mix1 g3_merge9_uarb1_SMIN_lo g3_merge9_uarb1_SMIN_hi).m1 = 502 ∧ (mix2 g3_merge9_uarb1_SMIN_lo g3_merge9_uarb1_SMIN_hi).m2 = 314 := by decide
theorem g3_merge9_uarb1_SMAX_ok : okRow g3_merge9_uarb1_SMAX_lo g3_merge9_uarb1_SMAX_hi = true ∧
    (mix1 g3_merge9_uarb1_SMAX_lo g3_merge9_uarb1_SMAX_hi).m1 = 616 ∧ (mix2 g3_merge9_uarb1_SMAX_lo g3_merge9_uarb1_SMAX_hi).m2 = 383 := by decide
theorem g4_merge10_uarb1_FMIN_ok : okRow g4_merge10_uarb1_FMIN_lo g4_merge10_uarb1_FMIN_hi = true ∧
    (mix1 g4_merge10_uarb1_FMIN_lo g4_merge10_uarb1_FMIN_hi).m1 = 367 ∧ (mix2 g4_merge10_uarb1_FMIN_lo g4_merge10_uarb1_FMIN_hi).m2 = 500 := by decide
theorem g4_merge10_uarb1_FMAX_ok : okRow g4_merge10_uarb1_FMAX_lo g4_merge10_uarb1_FMAX_hi = true ∧
    (mix1 g4_merge10_uarb1_FMAX_lo g4_merge10_uarb1_FMAX_hi).m1 = 452 ∧ (mix2 g4_merge10_uarb1_FMAX_lo g4_merge10_uarb1_FMAX_hi).m2 = 613 := by decide
theorem g4_merge10_uarb1_SMIN_ok : okRow g4_merge10_uarb1_SMIN_lo g4_merge10_uarb1_SMIN_hi = true ∧
    (mix1 g4_merge10_uarb1_SMIN_lo g4_merge10_uarb1_SMIN_hi).m1 = 863 ∧ (mix2 g4_merge10_uarb1_SMIN_lo g4_merge10_uarb1_SMIN_hi).m2 = 1152 := by decide
theorem g4_merge10_uarb1_SMAX_ok : okRow g4_merge10_uarb1_SMAX_lo g4_merge10_uarb1_SMAX_hi = true ∧
    (mix1 g4_merge10_uarb1_SMAX_lo g4_merge10_uarb1_SMAX_hi).m1 = 1058 ∧ (mix2 g4_merge10_uarb1_SMAX_lo g4_merge10_uarb1_SMAX_hi).m2 = 1422 := by decide
theorem g4_merge11_uarb1_FMIN_ok : okRow g4_merge11_uarb1_FMIN_lo g4_merge11_uarb1_FMIN_hi = true ∧
    (mix1 g4_merge11_uarb1_FMIN_lo g4_merge11_uarb1_FMIN_hi).m1 = 169 ∧ (mix2 g4_merge11_uarb1_FMIN_lo g4_merge11_uarb1_FMIN_hi).m2 = 173 := by decide
theorem g4_merge11_uarb1_FMAX_ok : okRow g4_merge11_uarb1_FMAX_lo g4_merge11_uarb1_FMAX_hi = true ∧
    (mix1 g4_merge11_uarb1_FMAX_lo g4_merge11_uarb1_FMAX_hi).m1 = 209 ∧ (mix2 g4_merge11_uarb1_FMAX_lo g4_merge11_uarb1_FMAX_hi).m2 = 220 := by decide
theorem g4_merge11_uarb1_SMIN_ok : okRow g4_merge11_uarb1_SMIN_lo g4_merge11_uarb1_SMIN_hi = true ∧
    (mix1 g4_merge11_uarb1_SMIN_lo g4_merge11_uarb1_SMIN_hi).m1 = 450 ∧ (mix2 g4_merge11_uarb1_SMIN_lo g4_merge11_uarb1_SMIN_hi).m2 = 496 := by decide
theorem g4_merge11_uarb1_SMAX_ok : okRow g4_merge11_uarb1_SMAX_lo g4_merge11_uarb1_SMAX_hi = true ∧
    (mix1 g4_merge11_uarb1_SMAX_lo g4_merge11_uarb1_SMAX_hi).m1 = 555 ∧ (mix2 g4_merge11_uarb1_SMAX_lo g4_merge11_uarb1_SMAX_hi).m2 = 621 := by decide
theorem g4_merge12_uarb1_FMIN_ok : okRow g4_merge12_uarb1_FMIN_lo g4_merge12_uarb1_FMIN_hi = true ∧
    (mix1 g4_merge12_uarb1_FMIN_lo g4_merge12_uarb1_FMIN_hi).m1 = 217 ∧ (mix2 g4_merge12_uarb1_FMIN_lo g4_merge12_uarb1_FMIN_hi).m2 = 253 := by decide
theorem g4_merge12_uarb1_FMAX_ok : okRow g4_merge12_uarb1_FMAX_lo g4_merge12_uarb1_FMAX_hi = true ∧
    (mix1 g4_merge12_uarb1_FMAX_lo g4_merge12_uarb1_FMAX_hi).m1 = 269 ∧ (mix2 g4_merge12_uarb1_FMAX_lo g4_merge12_uarb1_FMAX_hi).m2 = 318 := by decide
theorem g4_merge12_uarb1_SMIN_ok : okRow g4_merge12_uarb1_SMIN_lo g4_merge12_uarb1_SMIN_hi = true ∧
    (mix1 g4_merge12_uarb1_SMIN_lo g4_merge12_uarb1_SMIN_hi).m1 = 476 ∧ (mix2 g4_merge12_uarb1_SMIN_lo g4_merge12_uarb1_SMIN_hi).m2 = 650 := by decide
theorem g4_merge12_uarb1_SMAX_ok : okRow g4_merge12_uarb1_SMAX_lo g4_merge12_uarb1_SMAX_hi = true ∧
    (mix1 g4_merge12_uarb1_SMAX_lo g4_merge12_uarb1_SMAX_hi).m1 = 583 ∧ (mix2 g4_merge12_uarb1_SMAX_lo g4_merge12_uarb1_SMAX_hi).m2 = 817 := by decide
theorem g4_merge12_uarb2_FMIN_ok : okRow g4_merge12_uarb2_FMIN_lo g4_merge12_uarb2_FMIN_hi = true ∧
    (mix1 g4_merge12_uarb2_FMIN_lo g4_merge12_uarb2_FMIN_hi).m1 = 356 ∧ (mix2 g4_merge12_uarb2_FMIN_lo g4_merge12_uarb2_FMIN_hi).m2 = 211 := by decide
theorem g4_merge12_uarb2_FMAX_ok : okRow g4_merge12_uarb2_FMAX_lo g4_merge12_uarb2_FMAX_hi = true ∧
    (mix1 g4_merge12_uarb2_FMAX_lo g4_merge12_uarb2_FMAX_hi).m1 = 429 ∧ (mix2 g4_merge12_uarb2_FMAX_lo g4_merge12_uarb2_FMAX_hi).m2 = 254 := by decide
theorem g4_merge12_uarb2_SMIN_ok : okRow g4_merge12_uarb2_SMIN_lo g4_merge12_uarb2_SMIN_hi = true ∧
    (mix1 g4_merge12_uarb2_SMIN_lo g4_merge12_uarb2_SMIN_hi).m1 = 940 ∧ (mix2 g4_merge12_uarb2_SMIN_lo g4_merge12_uarb2_SMIN_hi).m2 = 608 := by decide
theorem g4_merge12_uarb2_SMAX_ok : okRow g4_merge12_uarb2_SMAX_lo g4_merge12_uarb2_SMAX_hi = true ∧
    (mix1 g4_merge12_uarb2_SMAX_lo g4_merge12_uarb2_SMAX_hi).m1 = 1143 ∧ (mix2 g4_merge12_uarb2_SMAX_lo g4_merge12_uarb2_SMAX_hi).m2 = 737 := by decide
theorem g4_merge2_uarb1_FMIN_ok : okRow g4_merge2_uarb1_FMIN_lo g4_merge2_uarb1_FMIN_hi = true ∧
    (mix1 g4_merge2_uarb1_FMIN_lo g4_merge2_uarb1_FMIN_hi).m1 = 506 ∧ (mix2 g4_merge2_uarb1_FMIN_lo g4_merge2_uarb1_FMIN_hi).m2 = 167 := by decide
theorem g4_merge2_uarb1_FMAX_ok : okRow g4_merge2_uarb1_FMAX_lo g4_merge2_uarb1_FMAX_hi = true ∧
    (mix1 g4_merge2_uarb1_FMAX_lo g4_merge2_uarb1_FMAX_hi).m1 = 578 ∧ (mix2 g4_merge2_uarb1_FMAX_lo g4_merge2_uarb1_FMAX_hi).m2 = 211 := by decide
theorem g4_merge2_uarb1_SMIN_ok : okRow g4_merge2_uarb1_SMIN_lo g4_merge2_uarb1_SMIN_hi = true ∧
    (mix1 g4_merge2_uarb1_SMIN_lo g4_merge2_uarb1_SMIN_hi).m1 = 1018 ∧ (mix2 g4_merge2_uarb1_SMIN_lo g4_merge2_uarb1_SMIN_hi).m2 = 491 := by decide
theorem g4_merge2_uarb1_SMAX_ok : okRow g4_merge2_uarb1_SMAX_lo g4_merge2_uarb1_SMAX_hi = true ∧
    (mix1 g4_merge2_uarb1_SMAX_lo g4_merge2_uarb1_SMAX_hi).m1 = 1207 ∧ (mix2 g4_merge2_uarb1_SMAX_lo g4_merge2_uarb1_SMAX_hi).m2 = 614 := by decide
theorem g4_merge3_uarb1_FMIN_ok : okRow g4_merge3_uarb1_FMIN_lo g4_merge3_uarb1_FMIN_hi = true ∧
    (mix1 g4_merge3_uarb1_FMIN_lo g4_merge3_uarb1_FMIN_hi).m1 = 239 ∧ (mix2 g4_merge3_uarb1_FMIN_lo g4_merge3_uarb1_FMIN_hi).m2 = 651 := by decide
theorem g4_merge3_uarb1_FMAX_ok : okRow g4_merge3_uarb1_FMAX_lo g4_merge3_uarb1_FMAX_hi = true ∧
    (mix1 g4_merge3_uarb1_FMAX_lo g4_merge3_uarb1_FMAX_hi).m1 = 289 ∧ (mix2 g4_merge3_uarb1_FMAX_lo g4_merge3_uarb1_FMAX_hi).m2 = 758 := by decide
theorem g4_merge3_uarb1_SMIN_ok : okRow g4_merge3_uarb1_SMIN_lo g4_merge3_uarb1_SMIN_hi = true ∧
    (mix1 g4_merge3_uarb1_SMIN_lo g4_merge3_uarb1_SMIN_hi).m1 = 604 ∧ (mix2 g4_merge3_uarb1_SMIN_lo g4_merge3_uarb1_SMIN_hi).m2 = 1384 := by decide
theorem g4_merge3_uarb1_SMAX_ok : okRow g4_merge3_uarb1_SMAX_lo g4_merge3_uarb1_SMAX_hi = true ∧
    (mix1 g4_merge3_uarb1_SMAX_lo g4_merge3_uarb1_SMAX_hi).m1 = 732 ∧ (mix2 g4_merge3_uarb1_SMAX_lo g4_merge3_uarb1_SMAX_hi).m2 = 1656 := by decide
theorem g4_merge4_uarb1_FMIN_ok : okRow g4_merge4_uarb1_FMIN_lo g4_merge4_uarb1_FMIN_hi = true ∧
    (mix1 g4_merge4_uarb1_FMIN_lo g4_merge4_uarb1_FMIN_hi).m1 = 224 ∧ (mix2 g4_merge4_uarb1_FMIN_lo g4_merge4_uarb1_FMIN_hi).m2 = 216 := by decide
theorem g4_merge4_uarb1_FMAX_ok : okRow g4_merge4_uarb1_FMAX_lo g4_merge4_uarb1_FMAX_hi = true ∧
    (mix1 g4_merge4_uarb1_FMAX_lo g4_merge4_uarb1_FMAX_hi).m1 = 275 ∧ (mix2 g4_merge4_uarb1_FMAX_lo g4_merge4_uarb1_FMAX_hi).m2 = 260 := by decide
theorem g4_merge4_uarb1_SMIN_ok : okRow g4_merge4_uarb1_SMIN_lo g4_merge4_uarb1_SMIN_hi = true ∧
    (mix1 g4_merge4_uarb1_SMIN_lo g4_merge4_uarb1_SMIN_hi).m1 = 588 ∧ (mix2 g4_merge4_uarb1_SMIN_lo g4_merge4_uarb1_SMIN_hi).m2 = 630 := by decide
theorem g4_merge4_uarb1_SMAX_ok : okRow g4_merge4_uarb1_SMAX_lo g4_merge4_uarb1_SMAX_hi = true ∧
    (mix1 g4_merge4_uarb1_SMAX_lo g4_merge4_uarb1_SMAX_hi).m1 = 719 ∧ (mix2 g4_merge4_uarb1_SMAX_lo g4_merge4_uarb1_SMAX_hi).m2 = 770 := by decide
theorem g4_merge6_uarb1_FMIN_ok : okRow g4_merge6_uarb1_FMIN_lo g4_merge6_uarb1_FMIN_hi = true ∧
    (mix1 g4_merge6_uarb1_FMIN_lo g4_merge6_uarb1_FMIN_hi).m1 = 361 ∧ (mix2 g4_merge6_uarb1_FMIN_lo g4_merge6_uarb1_FMIN_hi).m2 = 239 := by decide
theorem g4_merge6_uarb1_FMAX_ok : okRow g4_merge6_uarb1_FMAX_lo g4_merge6_uarb1_FMAX_hi = true ∧
    (mix1 g4_merge6_uarb1_FMAX_lo g4_merge6_uarb1_FMAX_hi).m1 = 438 ∧ (mix2 g4_merge6_uarb1_FMAX_lo g4_merge6_uarb1_FMAX_hi).m2 = 298 := by decide
theorem g4_merge6_uarb1_SMIN_ok : okRow g4_merge6_uarb1_SMIN_lo g4_merge6_uarb1_SMIN_hi = true ∧
    (mix1 g4_merge6_uarb1_SMIN_lo g4_merge6_uarb1_SMIN_hi).m1 = 858 ∧ (mix2 g4_merge6_uarb1_SMIN_lo g4_merge6_uarb1_SMIN_hi).m2 = 661 := by decide
theorem g4_merge6_uarb1_SMAX_ok : okRow g4_merge6_uarb1_SMAX_lo g4_merge6_uarb1_SMAX_hi = true ∧
    (mix1 g4_merge6_uarb1_SMAX_lo g4_merge6_uarb1_SMAX_hi).m1 = 1044 ∧ (mix2 g4_merge6_uarb1_SMAX_lo g4_merge6_uarb1_SMAX_hi).m2 = 819 := by decide
theorem g4_merge9_uarb1_FMIN_ok : okRow g4_merge9_uarb1_FMIN_lo g4_merge9_uarb1_FMIN_hi = true ∧
    (mix1 g4_merge9_uarb1_FMIN_lo g4_merge9_uarb1_FMIN_hi).m1 = 256 ∧ (mix2 g4_merge9_uarb1_FMIN_lo g4_merge9_uarb1_FMIN_hi).m2 = 249 := by decide
theorem g4_merge9_uarb1_FMAX_ok : okRow g4_merge9_uarb1_FMAX_lo g4_merge9_uarb1_FMAX_hi = true ∧
    (mix1 g4_merge9_uarb1_FMAX_lo g4_merge9_uarb1_FMAX_hi).m1 = 313 ∧ (mix2 g4_merge9_uarb1_FMAX_lo g4_merge9_uarb1_FMAX_hi).m2 = 308 := by decide
theorem g4_merge9_uarb1_SMIN_ok : okRow g4_merge9_uarb1_SMIN_lo g4_merge9_uarb1_SMIN_hi = true ∧
    (mix1 g4_merge9_uarb1_SMIN_lo g4_merge9_uarb1_SMIN_hi).m1 = 670 ∧ (mix2 g4_merge9_uarb1_SMIN_lo g4_merge9_uarb1_SMIN_hi).m2 = 705 := by decide
theorem g4_merge9_uarb1_SMAX_ok : okRow g4_merge9_uarb1_SMAX_lo g4_merge9_uarb1_SMAX_hi = true ∧
    (mix1 g4_merge9_uarb1_SMAX_lo g4_merge9_uarb1_SMAX_hi).m1 = 820 ∧ (mix2 g4_merge9_uarb1_SMAX_lo g4_merge9_uarb1_SMAX_hi).m2 = 874 := by decide
theorem gd_merge10_uarb1_FMIN_ok : okRow gd_merge10_uarb1_FMIN_lo gd_merge10_uarb1_FMIN_hi = true ∧
    (mix1 gd_merge10_uarb1_FMIN_lo gd_merge10_uarb1_FMIN_hi).m1 = 375 ∧ (mix2 gd_merge10_uarb1_FMIN_lo gd_merge10_uarb1_FMIN_hi).m2 = 375 := by decide
theorem gd_merge10_uarb1_FMAX_ok : okRow gd_merge10_uarb1_FMAX_lo gd_merge10_uarb1_FMAX_hi = true ∧
    (mix1 gd_merge10_uarb1_FMAX_lo gd_merge10_uarb1_FMAX_hi).m1 = 508 ∧ (mix2 gd_merge10_uarb1_FMAX_lo gd_merge10_uarb1_FMAX_hi).m2 = 508 := by decide
theorem gd_merge10_uarb1_SMIN_ok : okRow gd_merge10_uarb1_SMIN_lo gd_merge10_uarb1_SMIN_hi = true ∧
    (mix1 gd_merge10_uarb1_SMIN_lo gd_merge10_uarb1_SMIN_hi).m1 = 862 ∧ (mix2 gd_merge10_uarb1_SMIN_lo gd_merge10_uarb1_SMIN_hi).m2 = 950 := by decide
theorem gd_merge10_uarb1_SMAX_ok : okRow gd_merge10_uarb1_SMAX_lo gd_merge10_uarb1_SMAX_hi = true ∧
    (mix1 gd_merge10_uarb1_SMAX_lo gd_merge10_uarb1_SMAX_hi).m1 = 1222 ∧ (mix2 gd_merge10_uarb1_SMAX_lo gd_merge10_uarb1_SMAX_hi).m2 = 1338 := by decide
theorem gd_merge11_uarb1_FMIN_ok : okRow gd_merge11_uarb1_FMIN_lo gd_merge11_uarb1_FMIN_hi = true ∧
    (mix1 gd_merge11_uarb1_FMIN_lo gd_merge11_uarb1_FMIN_hi).m1 = 265 ∧ (mix2 gd_merge11_uarb1_FMIN_lo gd_merge11_uarb1_FMIN_hi).m2 = 374 := by decide
theorem gd_merge11_uarb1_FMAX_ok : okRow gd_merge11_uarb1_FMAX_lo gd_merge11_uarb1_FMAX_hi = true ∧
    (mix1 gd_merge11_uarb1_FMAX_lo gd_merge11_uarb1_FMAX_hi).m1 = 331 ∧ (mix2 gd_merge11_uarb1_FMAX_lo gd_merge11_uarb1_FMAX_hi).m2 = 461 := by decide
theorem gd_merge11_uarb1_SMIN_ok : okRow gd_merge11_uarb1_SMIN_lo gd_merge11_uarb1_SMIN_hi = true ∧
    (mix1 gd_merge11_uarb1_SMIN_lo gd_merge11_uarb1_SMIN_hi).m1 = 630 ∧ (mix2 gd_merge11_uarb1_SMIN_lo gd_merge11_uarb1_SMIN_hi).m2 = 916 := by decide
theorem gd_merge11_uarb1_SMAX_ok : okRow gd_merge11_uarb1_SMAX_lo gd_merge11_uarb1_SMAX_hi = true ∧
    (mix1 gd_merge11_uarb1_SMAX_lo gd_merge11_uarb1_SMAX_hi).m1 = 783 ∧ (mix2 gd_merge11_uarb1_SMAX_lo gd_merge11_uarb1_SMAX_hi).m2 = 1136 := by decide
theorem gd_merge12_uarb1_FMIN_ok : okRow gd_merge12_uarb1_FMIN_lo gd_merge12_uarb1_FMIN_hi = true ∧
    (mix1 gd_merge12_uarb1_FMIN_lo gd_merge12_uarb1_FMIN_hi).m1 = 315 ∧ (mix2 gd_merge12_uarb1_FMIN_lo gd_merge12_uarb1_FMIN_hi).m2 = 228 := by decide
theorem gd_merge12_uarb1_FMAX_ok : okRow gd_merge12_uarb1_FMAX_lo gd_merge12_uarb1_FMAX_hi = true ∧
    (mix1 gd_merge12_uarb1_FMAX_lo gd_merge12_uarb1_FMAX_hi).m1 = 389 ∧ (mix2 gd_merge12_uarb1_FMAX_lo gd_merge12_uarb1_FMAX_hi).m2 = 285 := by decide
theorem gd_merge12_uarb1_SMIN_ok : okRow gd_merge12_uarb1_SMIN_lo gd_merge12_uarb1_SMIN_hi = true ∧
    (mix1 gd_merge12_uarb1_SMIN_lo gd_merge12_uarb1_SMIN_hi).m1 = 768 ∧ (mix2 gd_merge12_uarb1_SMIN_lo gd_merge12_uarb1_SMIN_hi).m2 = 621 := by decide
theorem gd_merge12_uarb1_SMAX_ok : okRow gd_merge12_uarb1_SMAX_lo gd_merge12_uarb1_SMAX_hi = true ∧
    (mix1 gd_merge12_uarb1_SMAX_lo gd_merge12_uarb1_SMAX_hi).m1 = 945 ∧ (mix2 gd_merge12_uarb1_SMAX_lo gd_merge12_uarb1_SMAX_hi).m2 = 772 := by decide
theorem gd_merge12_uarb2_FMIN_ok : okRow gd_merge12_uarb2_FMIN_lo gd_merge12_uarb2_FMIN_hi = true ∧
    (mix1 gd_merge12_uarb2_FMIN_lo gd_merge12_uarb2_FMIN_hi).m1 = 351 ∧ (mix2 gd_merge12_uarb2_FMIN_lo gd_merge12_uarb2_FMIN_hi).m2 = 201 := by decide
theorem gd_merge12_uarb2_FMAX_ok : okRow gd_merge12_uarb2_FMAX_lo gd_merge12_uarb2_FMAX_hi = true ∧
    (mix1 gd_merge12_uarb2_FMAX_lo gd_merge12_uarb2_FMAX_hi).m1 = 406 ∧ (mix2 gd_merge12_uarb2_FMAX_lo gd_merge12_uarb2_FMAX_hi).m2 = 216 := by decide
theorem gd_merge12_uarb2_SMIN_ok : okRow gd_merge12_uarb2_SMIN_lo gd_merge12_uarb2_SMIN_hi = true ∧
    (mix1 gd_merge12_uarb2_SMIN_lo gd_merge12_uarb2_SMIN_hi).m1 = 811 ∧ (mix2 gd_merge12_uarb2_SMIN_lo gd_merge12_uarb2_SMIN_hi).m2 = 549 := by decide
theorem gd_merge12_uarb2_SMAX_ok : okRow gd_merge12_uarb2_SMAX_lo gd_merge12_uarb2_SMAX_hi = true ∧
    (mix1 gd_merge12_uarb2_SMAX_lo gd_merge12_uarb2_SMAX_hi).m1 = 921 ∧ (mix2 gd_merge12_uarb2_SMAX_lo gd_merge12_uarb2_SMAX_hi).m2 = 564 := by decide
theorem gd_merge2_uarb1_FMIN_ok : okRow gd_merge2_uarb1_FMIN_lo gd_merge2_uarb1_FMIN_hi = true ∧
    (mix1 gd_merge2_uarb1_FMIN_lo gd_merge2_uarb1_FMIN_hi).m1 = 169 ∧ (mix2 gd_merge2_uarb1_FMIN_lo gd_merge2_uarb1_FMIN_hi).m2 = 172 := by decide
theorem gd_merge2_uarb1_FMAX_ok : okRow gd_merge2_uarb1_FMAX_lo gd_merge2_uarb1_FMAX_hi = true ∧
    (mix1 gd_merge2_uarb1_FMAX_lo gd_merge2_uarb1_FMAX_hi).m1 = 209 ∧ (mix2 gd_merge2_uarb1_FMAX_lo gd_merge2_uarb1_FMAX_hi).m2 = 220 := by decide
theorem gd_merge2_uarb1_SMIN_ok : okRow gd_merge2_uarb1_SMIN_lo gd_merge2_uarb1_SMIN_hi = true ∧
    (mix1 gd_merge2_uarb1_SMIN_lo gd_merge2_uarb1_SMIN_hi).m1 = 450 ∧ (mix2 gd_merge2_uarb1_SMIN_lo gd_merge2_uarb1_SMIN_hi).m2 = 489 := by decide
theorem gd_merge2_uarb1_SMAX_ok : okRow gd_merge2_uarb1_SMAX_lo gd_merge2_uarb1_SMAX_hi = true ∧
    (mix1 gd_merge2_uarb1_SMAX_lo gd_merge2_uarb1_SMAX_hi).m1 = 555 ∧ (mix2 gd_merge2_uarb1_SMAX_lo gd_merge2_uarb1_SMAX_hi).m2 = 619 := by decide
theorem gd_merge3_uarb1_FMIN_ok : okRow gd_merge3_uarb1_FMIN_lo gd_merge3_uarb1_FMIN_hi = true ∧
    (mix1 gd_merge3_uarb1_FMIN_lo gd_merge3_uarb1_FMIN_hi).m1 = 243 ∧ (mix2 gd_merge3_uarb1_FMIN_lo gd_merge3_uarb1_FMIN_hi).m2 = 381 := by decide
theorem gd_merge3_uarb1_FMAX_ok : okRow gd_merge3_uarb1_FMAX_lo gd_merge3_uarb1_FMAX_hi = true ∧
    (mix1 gd_merge3_uarb1_FMAX_lo gd_merge3_uarb1_FMAX_hi).m1 = 303 ∧ (mix2 gd_merge3_uarb1_FMAX_lo gd_merge3_uarb1_FMAX_hi).m2 = 475 := by decide
theorem gd_merge3_uarb1_SMIN_ok : okRow gd_merge3_uarb1_SMIN_lo gd_merge3_uarb1_SMIN_hi = true ∧
    (mix1 gd_merge3_uarb1_SMIN_lo gd_merge3_uarb1_SMIN_hi).m1 = 621 ∧ (mix2 gd_merge3_uarb1_SMIN_lo gd_merge3_uarb1_SMIN_hi).m2 = 968 := by decide
theorem gd_merge3_uarb1_SMAX_ok : okRow gd_merge3_uarb1_SMAX_lo gd_merge3_uarb1_SMAX_hi = true ∧
    (mix1 gd_merge3_uarb1_SMAX_lo gd_merge3_uarb1_SMAX_hi).m1 = 773 ∧ (mix2 gd_merge3_uarb1_SMAX_lo gd_merge3_uarb1_SMAX_hi).m2 = 1200 := by decide
theorem gd_merge4_uarb1_FMIN_ok : okRow gd_merge4_uarb1_FMIN_lo gd_merge4_uarb1_FMIN_hi = true ∧
    (mix1 gd_merge4_uarb1_FMIN_lo gd_merge4_uarb1_FMIN_hi).m1 = 266 ∧ (mix2 gd_merge4_uarb1_FMIN_lo gd_merge4_uarb1_FMIN_hi).m2 = 267 := by decide
theorem gd_merge4_uarb1_FMAX_ok : okRow gd_merge4_uarb1_FMAX_lo gd_merge4_uarb1_FMAX_hi = true ∧
    (mix1 gd_merge4_uarb1_FMAX_lo gd_merge4_uarb1_FMAX_hi).m1 = 328 ∧ (mix2 gd_merge4_uarb1_FMAX_lo gd_merge4_uarb1_FMAX_hi).m2 = 347 := by decide
theorem gd_merge4_uarb1_SMIN_ok : okRow gd_merge4_uarb1_SMIN_lo gd_merge4_uarb1_SMIN_hi = true ∧
    (mix1 gd_merge4_uarb1_SMIN_lo gd_merge4_uarb1_SMIN_hi).m1 = 630 ∧ (mix2 gd_merge4_uarb1_SMIN_lo gd_merge4_uarb1_SMIN_hi).m2 = 796 := by decide
theorem gd_merge4_uarb1_SMAX_ok : okRow gd_merge4_uarb1_SMAX_lo gd_merge4_uarb1_SMAX_hi = true ∧
    (mix1 gd_merge4_uarb1_SMAX_lo gd_merge4_uarb1_SMAX_hi).m1 = 770 ∧ (mix2 gd_merge4_uarb1_SMAX_lo gd_merge4_uarb1_SMAX_hi).m2 = 1006 := by decide
theorem gd_merge6_uarb1_FMIN_ok : okRow gd_merge6_uarb1_FMIN_lo gd_merge6_uarb1_FMIN_hi = true ∧
    (mix1 gd_merge6_uarb1_FMIN_lo gd_merge6_uarb1_FMIN_hi).m1 = 396 ∧ (mix2 gd_merge6_uarb1_FMIN_lo gd_merge6_uarb1_FMIN_hi).m2 = 447 := by decide
theorem gd_merge6_uarb1_FMAX_ok : okRow gd_merge6_uarb1_FMAX_lo gd_merge6_uarb1_FMAX_hi = true ∧
    (mix1 gd_merge6_uarb1_FMAX_lo gd_merge6_uarb1_FMAX_hi).m1 = 486 ∧ (mix2 gd_merge6_uarb1_FMAX_lo gd_merge6_uarb1_FMAX_hi).m2 = 556 := by decide
theorem gd_merge6_uarb1_SMIN_ok : okRow gd_merge6_uarb1_SMIN_lo gd_merge6_uarb1_SMIN_hi = true ∧
    (mix1 gd_merge6_uarb1_SMIN_lo gd_merge6_uarb1_SMIN_hi).m1 = 960 ∧ (mix2 gd_merge6_uarb1_SMIN_lo gd_merge6_uarb1_SMIN_hi).m2 = 1139 := by decide
theorem gd_merge6_uarb1_SMAX_ok : okRow gd_merge6_uarb1_SMAX_lo gd_merge6_uarb1_SMAX_hi = true ∧
    (mix1 gd_merge6_uarb1_SMAX_lo gd_merge6_uarb1_SMAX_hi).m1 = 1180 ∧ (mix2 gd_merge6_uarb1_SMAX_lo gd_merge6_uarb1_SMAX_hi).m2 = 1414 := by decide
theorem gd_merge9_uarb1_FMIN_ok : okRow gd_merge9_uarb1_FMIN_lo gd_merge9_uarb1_FMIN_hi = true ∧
    (mix1 gd_merge9_uarb1_FMIN_lo gd_merge9_uarb1_FMIN_hi).m1 = 53 ∧ (mix2 gd_merge9_uarb1_FMIN_lo gd_merge9_uarb1_FMIN_hi).m2 = 126 := by decide
theorem gd_merge9_uarb1_FMAX_ok : okRow gd_merge9_uarb1_FMAX_lo gd_merge9_uarb1_FMAX_hi = true ∧
    (mix1 gd_merge9_uarb1_FMAX_lo gd_merge9_uarb1_FMAX_hi).m1 = 68 ∧ (mix2 gd_merge9_uarb1_FMAX_lo gd_merge9_uarb1_FMAX_hi).m2 = 165 := by decide
theorem gd_merge9_uarb1_SMIN_ok : okRow gd_merge9_uarb1_SMIN_lo gd_merge9_uarb1_SMIN_hi = true ∧
    (mix1 gd_merge9_uarb1_SMIN_lo gd_merge9_uarb1_SMIN_hi).m1 = 102 ∧ (mix2 gd_merge9_uarb1_SMIN_lo gd_merge9_uarb1_SMIN_hi).m2 = 332 := by decide
theorem gd_merge9_uarb1_SMAX_ok : okRow gd_merge9_uarb1_SMAX_lo gd_merge9_uarb1_SMAX_hi = true ∧
    (mix1 gd_merge9_uarb1_SMAX_lo gd_merge9_uarb1_SMAX_hi).m1 = 122 ∧ (mix2 gd_merge9_uarb1_SMAX_lo gd_merge9_uarb1_SMAX_hi).m2 = 417 := by decide

/-- All 36 arbiters x 4 corners (hull rows). -/
def cornerRows : List (Q × Q) :=
  [(g2_merge10_uarb1_FMIN_lo, g2_merge10_uarb1_FMIN_hi),
   (g2_merge10_uarb1_FMAX_lo, g2_merge10_uarb1_FMAX_hi),
   (g2_merge10_uarb1_SMIN_lo, g2_merge10_uarb1_SMIN_hi),
   (g2_merge10_uarb1_SMAX_lo, g2_merge10_uarb1_SMAX_hi),
   (g2_merge11_uarb1_FMIN_lo, g2_merge11_uarb1_FMIN_hi),
   (g2_merge11_uarb1_FMAX_lo, g2_merge11_uarb1_FMAX_hi),
   (g2_merge11_uarb1_SMIN_lo, g2_merge11_uarb1_SMIN_hi),
   (g2_merge11_uarb1_SMAX_lo, g2_merge11_uarb1_SMAX_hi),
   (g2_merge12_uarb1_FMIN_lo, g2_merge12_uarb1_FMIN_hi),
   (g2_merge12_uarb1_FMAX_lo, g2_merge12_uarb1_FMAX_hi),
   (g2_merge12_uarb1_SMIN_lo, g2_merge12_uarb1_SMIN_hi),
   (g2_merge12_uarb1_SMAX_lo, g2_merge12_uarb1_SMAX_hi),
   (g2_merge12_uarb2_FMIN_lo, g2_merge12_uarb2_FMIN_hi),
   (g2_merge12_uarb2_FMAX_lo, g2_merge12_uarb2_FMAX_hi),
   (g2_merge12_uarb2_SMIN_lo, g2_merge12_uarb2_SMIN_hi),
   (g2_merge12_uarb2_SMAX_lo, g2_merge12_uarb2_SMAX_hi),
   (g2_merge2_uarb1_FMIN_lo, g2_merge2_uarb1_FMIN_hi),
   (g2_merge2_uarb1_FMAX_lo, g2_merge2_uarb1_FMAX_hi),
   (g2_merge2_uarb1_SMIN_lo, g2_merge2_uarb1_SMIN_hi),
   (g2_merge2_uarb1_SMAX_lo, g2_merge2_uarb1_SMAX_hi),
   (g2_merge3_uarb1_FMIN_lo, g2_merge3_uarb1_FMIN_hi),
   (g2_merge3_uarb1_FMAX_lo, g2_merge3_uarb1_FMAX_hi),
   (g2_merge3_uarb1_SMIN_lo, g2_merge3_uarb1_SMIN_hi),
   (g2_merge3_uarb1_SMAX_lo, g2_merge3_uarb1_SMAX_hi),
   (g2_merge4_uarb1_FMIN_lo, g2_merge4_uarb1_FMIN_hi),
   (g2_merge4_uarb1_FMAX_lo, g2_merge4_uarb1_FMAX_hi),
   (g2_merge4_uarb1_SMIN_lo, g2_merge4_uarb1_SMIN_hi),
   (g2_merge4_uarb1_SMAX_lo, g2_merge4_uarb1_SMAX_hi),
   (g2_merge6_uarb1_FMIN_lo, g2_merge6_uarb1_FMIN_hi),
   (g2_merge6_uarb1_FMAX_lo, g2_merge6_uarb1_FMAX_hi),
   (g2_merge6_uarb1_SMIN_lo, g2_merge6_uarb1_SMIN_hi),
   (g2_merge6_uarb1_SMAX_lo, g2_merge6_uarb1_SMAX_hi),
   (g2_merge9_uarb1_FMIN_lo, g2_merge9_uarb1_FMIN_hi),
   (g2_merge9_uarb1_FMAX_lo, g2_merge9_uarb1_FMAX_hi),
   (g2_merge9_uarb1_SMIN_lo, g2_merge9_uarb1_SMIN_hi),
   (g2_merge9_uarb1_SMAX_lo, g2_merge9_uarb1_SMAX_hi),
   (g3_merge10_uarb1_FMIN_lo, g3_merge10_uarb1_FMIN_hi),
   (g3_merge10_uarb1_FMAX_lo, g3_merge10_uarb1_FMAX_hi),
   (g3_merge10_uarb1_SMIN_lo, g3_merge10_uarb1_SMIN_hi),
   (g3_merge10_uarb1_SMAX_lo, g3_merge10_uarb1_SMAX_hi),
   (g3_merge11_uarb1_FMIN_lo, g3_merge11_uarb1_FMIN_hi),
   (g3_merge11_uarb1_FMAX_lo, g3_merge11_uarb1_FMAX_hi),
   (g3_merge11_uarb1_SMIN_lo, g3_merge11_uarb1_SMIN_hi),
   (g3_merge11_uarb1_SMAX_lo, g3_merge11_uarb1_SMAX_hi),
   (g3_merge12_uarb1_FMIN_lo, g3_merge12_uarb1_FMIN_hi),
   (g3_merge12_uarb1_FMAX_lo, g3_merge12_uarb1_FMAX_hi),
   (g3_merge12_uarb1_SMIN_lo, g3_merge12_uarb1_SMIN_hi),
   (g3_merge12_uarb1_SMAX_lo, g3_merge12_uarb1_SMAX_hi),
   (g3_merge12_uarb2_FMIN_lo, g3_merge12_uarb2_FMIN_hi),
   (g3_merge12_uarb2_FMAX_lo, g3_merge12_uarb2_FMAX_hi),
   (g3_merge12_uarb2_SMIN_lo, g3_merge12_uarb2_SMIN_hi),
   (g3_merge12_uarb2_SMAX_lo, g3_merge12_uarb2_SMAX_hi),
   (g3_merge2_uarb1_FMIN_lo, g3_merge2_uarb1_FMIN_hi),
   (g3_merge2_uarb1_FMAX_lo, g3_merge2_uarb1_FMAX_hi),
   (g3_merge2_uarb1_SMIN_lo, g3_merge2_uarb1_SMIN_hi),
   (g3_merge2_uarb1_SMAX_lo, g3_merge2_uarb1_SMAX_hi),
   (g3_merge3_uarb1_FMIN_lo, g3_merge3_uarb1_FMIN_hi),
   (g3_merge3_uarb1_FMAX_lo, g3_merge3_uarb1_FMAX_hi),
   (g3_merge3_uarb1_SMIN_lo, g3_merge3_uarb1_SMIN_hi),
   (g3_merge3_uarb1_SMAX_lo, g3_merge3_uarb1_SMAX_hi),
   (g3_merge4_uarb1_FMIN_lo, g3_merge4_uarb1_FMIN_hi),
   (g3_merge4_uarb1_FMAX_lo, g3_merge4_uarb1_FMAX_hi),
   (g3_merge4_uarb1_SMIN_lo, g3_merge4_uarb1_SMIN_hi),
   (g3_merge4_uarb1_SMAX_lo, g3_merge4_uarb1_SMAX_hi),
   (g3_merge6_uarb1_FMIN_lo, g3_merge6_uarb1_FMIN_hi),
   (g3_merge6_uarb1_FMAX_lo, g3_merge6_uarb1_FMAX_hi),
   (g3_merge6_uarb1_SMIN_lo, g3_merge6_uarb1_SMIN_hi),
   (g3_merge6_uarb1_SMAX_lo, g3_merge6_uarb1_SMAX_hi),
   (g3_merge9_uarb1_FMIN_lo, g3_merge9_uarb1_FMIN_hi),
   (g3_merge9_uarb1_FMAX_lo, g3_merge9_uarb1_FMAX_hi),
   (g3_merge9_uarb1_SMIN_lo, g3_merge9_uarb1_SMIN_hi),
   (g3_merge9_uarb1_SMAX_lo, g3_merge9_uarb1_SMAX_hi),
   (g4_merge10_uarb1_FMIN_lo, g4_merge10_uarb1_FMIN_hi),
   (g4_merge10_uarb1_FMAX_lo, g4_merge10_uarb1_FMAX_hi),
   (g4_merge10_uarb1_SMIN_lo, g4_merge10_uarb1_SMIN_hi),
   (g4_merge10_uarb1_SMAX_lo, g4_merge10_uarb1_SMAX_hi),
   (g4_merge11_uarb1_FMIN_lo, g4_merge11_uarb1_FMIN_hi),
   (g4_merge11_uarb1_FMAX_lo, g4_merge11_uarb1_FMAX_hi),
   (g4_merge11_uarb1_SMIN_lo, g4_merge11_uarb1_SMIN_hi),
   (g4_merge11_uarb1_SMAX_lo, g4_merge11_uarb1_SMAX_hi),
   (g4_merge12_uarb1_FMIN_lo, g4_merge12_uarb1_FMIN_hi),
   (g4_merge12_uarb1_FMAX_lo, g4_merge12_uarb1_FMAX_hi),
   (g4_merge12_uarb1_SMIN_lo, g4_merge12_uarb1_SMIN_hi),
   (g4_merge12_uarb1_SMAX_lo, g4_merge12_uarb1_SMAX_hi),
   (g4_merge12_uarb2_FMIN_lo, g4_merge12_uarb2_FMIN_hi),
   (g4_merge12_uarb2_FMAX_lo, g4_merge12_uarb2_FMAX_hi),
   (g4_merge12_uarb2_SMIN_lo, g4_merge12_uarb2_SMIN_hi),
   (g4_merge12_uarb2_SMAX_lo, g4_merge12_uarb2_SMAX_hi),
   (g4_merge2_uarb1_FMIN_lo, g4_merge2_uarb1_FMIN_hi),
   (g4_merge2_uarb1_FMAX_lo, g4_merge2_uarb1_FMAX_hi),
   (g4_merge2_uarb1_SMIN_lo, g4_merge2_uarb1_SMIN_hi),
   (g4_merge2_uarb1_SMAX_lo, g4_merge2_uarb1_SMAX_hi),
   (g4_merge3_uarb1_FMIN_lo, g4_merge3_uarb1_FMIN_hi),
   (g4_merge3_uarb1_FMAX_lo, g4_merge3_uarb1_FMAX_hi),
   (g4_merge3_uarb1_SMIN_lo, g4_merge3_uarb1_SMIN_hi),
   (g4_merge3_uarb1_SMAX_lo, g4_merge3_uarb1_SMAX_hi),
   (g4_merge4_uarb1_FMIN_lo, g4_merge4_uarb1_FMIN_hi),
   (g4_merge4_uarb1_FMAX_lo, g4_merge4_uarb1_FMAX_hi),
   (g4_merge4_uarb1_SMIN_lo, g4_merge4_uarb1_SMIN_hi),
   (g4_merge4_uarb1_SMAX_lo, g4_merge4_uarb1_SMAX_hi),
   (g4_merge6_uarb1_FMIN_lo, g4_merge6_uarb1_FMIN_hi),
   (g4_merge6_uarb1_FMAX_lo, g4_merge6_uarb1_FMAX_hi),
   (g4_merge6_uarb1_SMIN_lo, g4_merge6_uarb1_SMIN_hi),
   (g4_merge6_uarb1_SMAX_lo, g4_merge6_uarb1_SMAX_hi),
   (g4_merge9_uarb1_FMIN_lo, g4_merge9_uarb1_FMIN_hi),
   (g4_merge9_uarb1_FMAX_lo, g4_merge9_uarb1_FMAX_hi),
   (g4_merge9_uarb1_SMIN_lo, g4_merge9_uarb1_SMIN_hi),
   (g4_merge9_uarb1_SMAX_lo, g4_merge9_uarb1_SMAX_hi),
   (gd_merge10_uarb1_FMIN_lo, gd_merge10_uarb1_FMIN_hi),
   (gd_merge10_uarb1_FMAX_lo, gd_merge10_uarb1_FMAX_hi),
   (gd_merge10_uarb1_SMIN_lo, gd_merge10_uarb1_SMIN_hi),
   (gd_merge10_uarb1_SMAX_lo, gd_merge10_uarb1_SMAX_hi),
   (gd_merge11_uarb1_FMIN_lo, gd_merge11_uarb1_FMIN_hi),
   (gd_merge11_uarb1_FMAX_lo, gd_merge11_uarb1_FMAX_hi),
   (gd_merge11_uarb1_SMIN_lo, gd_merge11_uarb1_SMIN_hi),
   (gd_merge11_uarb1_SMAX_lo, gd_merge11_uarb1_SMAX_hi),
   (gd_merge12_uarb1_FMIN_lo, gd_merge12_uarb1_FMIN_hi),
   (gd_merge12_uarb1_FMAX_lo, gd_merge12_uarb1_FMAX_hi),
   (gd_merge12_uarb1_SMIN_lo, gd_merge12_uarb1_SMIN_hi),
   (gd_merge12_uarb1_SMAX_lo, gd_merge12_uarb1_SMAX_hi),
   (gd_merge12_uarb2_FMIN_lo, gd_merge12_uarb2_FMIN_hi),
   (gd_merge12_uarb2_FMAX_lo, gd_merge12_uarb2_FMAX_hi),
   (gd_merge12_uarb2_SMIN_lo, gd_merge12_uarb2_SMIN_hi),
   (gd_merge12_uarb2_SMAX_lo, gd_merge12_uarb2_SMAX_hi),
   (gd_merge2_uarb1_FMIN_lo, gd_merge2_uarb1_FMIN_hi),
   (gd_merge2_uarb1_FMAX_lo, gd_merge2_uarb1_FMAX_hi),
   (gd_merge2_uarb1_SMIN_lo, gd_merge2_uarb1_SMIN_hi),
   (gd_merge2_uarb1_SMAX_lo, gd_merge2_uarb1_SMAX_hi),
   (gd_merge3_uarb1_FMIN_lo, gd_merge3_uarb1_FMIN_hi),
   (gd_merge3_uarb1_FMAX_lo, gd_merge3_uarb1_FMAX_hi),
   (gd_merge3_uarb1_SMIN_lo, gd_merge3_uarb1_SMIN_hi),
   (gd_merge3_uarb1_SMAX_lo, gd_merge3_uarb1_SMAX_hi),
   (gd_merge4_uarb1_FMIN_lo, gd_merge4_uarb1_FMIN_hi),
   (gd_merge4_uarb1_FMAX_lo, gd_merge4_uarb1_FMAX_hi),
   (gd_merge4_uarb1_SMIN_lo, gd_merge4_uarb1_SMIN_hi),
   (gd_merge4_uarb1_SMAX_lo, gd_merge4_uarb1_SMAX_hi),
   (gd_merge6_uarb1_FMIN_lo, gd_merge6_uarb1_FMIN_hi),
   (gd_merge6_uarb1_FMAX_lo, gd_merge6_uarb1_FMAX_hi),
   (gd_merge6_uarb1_SMIN_lo, gd_merge6_uarb1_SMIN_hi),
   (gd_merge6_uarb1_SMAX_lo, gd_merge6_uarb1_SMAX_hi),
   (gd_merge9_uarb1_FMIN_lo, gd_merge9_uarb1_FMIN_hi),
   (gd_merge9_uarb1_FMAX_lo, gd_merge9_uarb1_FMAX_hi),
   (gd_merge9_uarb1_SMIN_lo, gd_merge9_uarb1_SMIN_hi),
   (gd_merge9_uarb1_SMAX_lo, gd_merge9_uarb1_SMAX_hi)]

theorem cornerRows_length : cornerRows.length = 144 := by rfl

set_option maxRecDepth 100000 in
theorem cornerRows_ok : cornerRows.all (fun p => okRow p.1 p.2) = true := by decide

/-- **Headline, client-1 release.** On every routed gcd_hw arbiter (4 seeds x 9) at
every consistent prjxray corner, with the corrected net split, for every 7h delay record
in the row's rounding hull (any r1 prefix, any q prefix `cq ≥ 0`, any A0 branch, any
ustate O6 arc, ANY server `smin ≥ 0`), every run of the gate relations through the
handover keeps g1 and g2 exclusive. -/
theorem gcd_rt1_all : ∀ p ∈ cornerRows, ∀ {D : Dl} {s : Sigs} {t0 ta TA TA2 Hz cr cq : Int},
    BoxReal1 p.1 p.2 cr cq D → Run D s → Scn D s t0 ta TA TA2 Hz →
    ∀ t, t < Hz → (s.g1 t && s.g2 t) = false := by
  intro p hp D s t0 ta TA TA2 Hz cr cq h R S
  have hok := okRow_sound _ _ (List.all_eq_true.mp cornerRows_ok p hp)
  exact hull_excl1 _ _ hok.2.2.2.1 h R S

/-- **Headline, client-2 release** (7j's mirror). -/
theorem gcd_rt1b_all : ∀ p ∈ cornerRows, ∀ {D : Dl} {s : Sigs} {t0 ta TA TA2 Hz cr cq : Int},
    BoxReal2 p.1 p.2 cr cq D → Run D s → Scn2 D s t0 ta TA TA2 Hz →
    ∀ t, t < Hz → (s.g1 t && s.g2 t) = false := by
  intro p hp D s t0 ta TA TA2 Hz cr cq h R S
  have hok := okRow_sound _ _ (List.all_eq_true.mp cornerRows_ok p hp)
  exact hull_excl2 _ _ hok.2.2.2.2 h R S

/-- Non-vacuity of the instantiation hypothesis on every row: for every server
`sm ≥ 0` a valid 7h record lies in the hull (it is the worst point). The model's own
non-vacuity (a `Run` with `Scn`/`Scn2`) is `ArbCorners.nonvacuous_corners`. -/
theorem cornerRows_sat : ∀ p ∈ cornerRows, ∀ sm : Int, 0 ≤ sm →
    (∃ D : Dl, BoxReal1 p.1 p.2 0 0 D ∧ D.smin = sm) ∧
    (∃ D : Dl, BoxReal2 p.1 p.2 0 0 D ∧ D.smin = sm) := by
  intro p hp sm hs
  have hok := okRow_sound _ _ (List.all_eq_true.mp cornerRows_ok p hp)
  exact ⟨⟨_, mix1_in _ _ hok.1 hok.2.1 sm hs, rfl⟩, ⟨_, mix2_in _ _ hok.1 hok.2.2.1 sm hs, rfl⟩⟩

/-! ## The independent box (H_INDEP: each element in [⌊FMIN⌋, ⌈SMAX⌉]), per arbiter

`_box` gives the exact worst-point server-free margins (m1, m2). `box_rt1`/`box_rt1b`:
every box record satisfies RT1/RT1b once `smin + wa0s + qf + cq ≥ need` (RT1b: `qr`).
When a margin is negative, `_cex1`/`_cex2` give a valid box record with that sum
`= need - 1` (`wa0s = qf = cq = 0`) violating RT1/RT1b; with a server answering in
exactly `smin`, 7h's `rt1_counter_minserver` / 7j's `rt1_counter2_minserver` give an
overlap. So `need = max(0, -m1, -m2)` is exact. -/

theorem g2_merge10_uarb1_box : g2_merge10_uarb1_FMIN_lo.le g2_merge10_uarb1_SMAX_hi = true ∧ (mix1 g2_merge10_uarb1_FMIN_lo g2_merge10_uarb1_SMAX_hi).m1 = -596 ∧
    (mix2 g2_merge10_uarb1_FMIN_lo g2_merge10_uarb1_SMAX_hi).m2 = -10 := by decide
theorem g2_merge10_uarb1_cex1 : ∃ D : Dl, BoxReal1 g2_merge10_uarb1_FMIN_lo g2_merge10_uarb1_SMAX_hi 0 0 D ∧ D.smin = 595 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 595 (by decide) (by decide)
theorem g2_merge10_uarb1_cex2 : ∃ D : Dl, BoxReal2 g2_merge10_uarb1_FMIN_lo g2_merge10_uarb1_SMAX_hi 0 0 D ∧ D.smin = 9 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 9 (by decide) (by decide)
theorem g2_merge11_uarb1_box : g2_merge11_uarb1_FMIN_lo.le g2_merge11_uarb1_SMAX_hi = true ∧ (mix1 g2_merge11_uarb1_FMIN_lo g2_merge11_uarb1_SMAX_hi).m1 = 261 ∧
    (mix2 g2_merge11_uarb1_FMIN_lo g2_merge11_uarb1_SMAX_hi).m2 = 96 := by decide
theorem g2_merge12_uarb1_box : g2_merge12_uarb1_FMIN_lo.le g2_merge12_uarb1_SMAX_hi = true ∧ (mix1 g2_merge12_uarb1_FMIN_lo g2_merge12_uarb1_SMAX_hi).m1 = -449 ∧
    (mix2 g2_merge12_uarb1_FMIN_lo g2_merge12_uarb1_SMAX_hi).m2 = -588 := by decide
theorem g2_merge12_uarb1_cex1 : ∃ D : Dl, BoxReal1 g2_merge12_uarb1_FMIN_lo g2_merge12_uarb1_SMAX_hi 0 0 D ∧ D.smin = 448 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 448 (by decide) (by decide)
theorem g2_merge12_uarb1_cex2 : ∃ D : Dl, BoxReal2 g2_merge12_uarb1_FMIN_lo g2_merge12_uarb1_SMAX_hi 0 0 D ∧ D.smin = 587 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 587 (by decide) (by decide)
theorem g2_merge12_uarb2_box : g2_merge12_uarb2_FMIN_lo.le g2_merge12_uarb2_SMAX_hi = true ∧ (mix1 g2_merge12_uarb2_FMIN_lo g2_merge12_uarb2_SMAX_hi).m1 = 131 ∧
    (mix2 g2_merge12_uarb2_FMIN_lo g2_merge12_uarb2_SMAX_hi).m2 = -403 := by decide
theorem g2_merge12_uarb2_cex2 : ∃ D : Dl, BoxReal2 g2_merge12_uarb2_FMIN_lo g2_merge12_uarb2_SMAX_hi 0 0 D ∧ D.smin = 402 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 402 (by decide) (by decide)
theorem g2_merge2_uarb1_box : g2_merge2_uarb1_FMIN_lo.le g2_merge2_uarb1_SMAX_hi = true ∧ (mix1 g2_merge2_uarb1_FMIN_lo g2_merge2_uarb1_SMAX_hi).m1 = -557 ∧
    (mix2 g2_merge2_uarb1_FMIN_lo g2_merge2_uarb1_SMAX_hi).m2 = -139 := by decide
theorem g2_merge2_uarb1_cex1 : ∃ D : Dl, BoxReal1 g2_merge2_uarb1_FMIN_lo g2_merge2_uarb1_SMAX_hi 0 0 D ∧ D.smin = 556 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 556 (by decide) (by decide)
theorem g2_merge2_uarb1_cex2 : ∃ D : Dl, BoxReal2 g2_merge2_uarb1_FMIN_lo g2_merge2_uarb1_SMAX_hi 0 0 D ∧ D.smin = 138 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 138 (by decide) (by decide)
theorem g2_merge3_uarb1_box : g2_merge3_uarb1_FMIN_lo.le g2_merge3_uarb1_SMAX_hi = true ∧ (mix1 g2_merge3_uarb1_FMIN_lo g2_merge3_uarb1_SMAX_hi).m1 = -166 ∧
    (mix2 g2_merge3_uarb1_FMIN_lo g2_merge3_uarb1_SMAX_hi).m2 = -495 := by decide
theorem g2_merge3_uarb1_cex1 : ∃ D : Dl, BoxReal1 g2_merge3_uarb1_FMIN_lo g2_merge3_uarb1_SMAX_hi 0 0 D ∧ D.smin = 165 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 165 (by decide) (by decide)
theorem g2_merge3_uarb1_cex2 : ∃ D : Dl, BoxReal2 g2_merge3_uarb1_FMIN_lo g2_merge3_uarb1_SMAX_hi 0 0 D ∧ D.smin = 494 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 494 (by decide) (by decide)
theorem g2_merge4_uarb1_box : g2_merge4_uarb1_FMIN_lo.le g2_merge4_uarb1_SMAX_hi = true ∧ (mix1 g2_merge4_uarb1_FMIN_lo g2_merge4_uarb1_SMAX_hi).m1 = -138 ∧
    (mix2 g2_merge4_uarb1_FMIN_lo g2_merge4_uarb1_SMAX_hi).m2 = 32 := by decide
theorem g2_merge4_uarb1_cex1 : ∃ D : Dl, BoxReal1 g2_merge4_uarb1_FMIN_lo g2_merge4_uarb1_SMAX_hi 0 0 D ∧ D.smin = 137 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 137 (by decide) (by decide)
theorem g2_merge6_uarb1_box : g2_merge6_uarb1_FMIN_lo.le g2_merge6_uarb1_SMAX_hi = true ∧ (mix1 g2_merge6_uarb1_FMIN_lo g2_merge6_uarb1_SMAX_hi).m1 = -138 ∧
    (mix2 g2_merge6_uarb1_FMIN_lo g2_merge6_uarb1_SMAX_hi).m2 = -340 := by decide
theorem g2_merge6_uarb1_cex1 : ∃ D : Dl, BoxReal1 g2_merge6_uarb1_FMIN_lo g2_merge6_uarb1_SMAX_hi 0 0 D ∧ D.smin = 137 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 137 (by decide) (by decide)
theorem g2_merge6_uarb1_cex2 : ∃ D : Dl, BoxReal2 g2_merge6_uarb1_FMIN_lo g2_merge6_uarb1_SMAX_hi 0 0 D ∧ D.smin = 339 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 339 (by decide) (by decide)
theorem g2_merge9_uarb1_box : g2_merge9_uarb1_FMIN_lo.le g2_merge9_uarb1_SMAX_hi = true ∧ (mix1 g2_merge9_uarb1_FMIN_lo g2_merge9_uarb1_SMAX_hi).m1 = -379 ∧
    (mix2 g2_merge9_uarb1_FMIN_lo g2_merge9_uarb1_SMAX_hi).m2 = -357 := by decide
theorem g2_merge9_uarb1_cex1 : ∃ D : Dl, BoxReal1 g2_merge9_uarb1_FMIN_lo g2_merge9_uarb1_SMAX_hi 0 0 D ∧ D.smin = 378 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 378 (by decide) (by decide)
theorem g2_merge9_uarb1_cex2 : ∃ D : Dl, BoxReal2 g2_merge9_uarb1_FMIN_lo g2_merge9_uarb1_SMAX_hi 0 0 D ∧ D.smin = 356 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 356 (by decide) (by decide)
theorem g3_merge10_uarb1_box : g3_merge10_uarb1_FMIN_lo.le g3_merge10_uarb1_SMAX_hi = true ∧ (mix1 g3_merge10_uarb1_FMIN_lo g3_merge10_uarb1_SMAX_hi).m1 = -13 ∧
    (mix2 g3_merge10_uarb1_FMIN_lo g3_merge10_uarb1_SMAX_hi).m2 = -491 := by decide
theorem g3_merge10_uarb1_cex1 : ∃ D : Dl, BoxReal1 g3_merge10_uarb1_FMIN_lo g3_merge10_uarb1_SMAX_hi 0 0 D ∧ D.smin = 12 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 12 (by decide) (by decide)
theorem g3_merge10_uarb1_cex2 : ∃ D : Dl, BoxReal2 g3_merge10_uarb1_FMIN_lo g3_merge10_uarb1_SMAX_hi 0 0 D ∧ D.smin = 490 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 490 (by decide) (by decide)
theorem g3_merge11_uarb1_box : g3_merge11_uarb1_FMIN_lo.le g3_merge11_uarb1_SMAX_hi = true ∧ (mix1 g3_merge11_uarb1_FMIN_lo g3_merge11_uarb1_SMAX_hi).m1 = -437 ∧
    (mix2 g3_merge11_uarb1_FMIN_lo g3_merge11_uarb1_SMAX_hi).m2 = -305 := by decide
theorem g3_merge11_uarb1_cex1 : ∃ D : Dl, BoxReal1 g3_merge11_uarb1_FMIN_lo g3_merge11_uarb1_SMAX_hi 0 0 D ∧ D.smin = 436 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 436 (by decide) (by decide)
theorem g3_merge11_uarb1_cex2 : ∃ D : Dl, BoxReal2 g3_merge11_uarb1_FMIN_lo g3_merge11_uarb1_SMAX_hi 0 0 D ∧ D.smin = 304 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 304 (by decide) (by decide)
theorem g3_merge12_uarb1_box : g3_merge12_uarb1_FMIN_lo.le g3_merge12_uarb1_SMAX_hi = true ∧ (mix1 g3_merge12_uarb1_FMIN_lo g3_merge12_uarb1_SMAX_hi).m1 = -357 ∧
    (mix2 g3_merge12_uarb1_FMIN_lo g3_merge12_uarb1_SMAX_hi).m2 = -712 := by decide
theorem g3_merge12_uarb1_cex1 : ∃ D : Dl, BoxReal1 g3_merge12_uarb1_FMIN_lo g3_merge12_uarb1_SMAX_hi 0 0 D ∧ D.smin = 356 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 356 (by decide) (by decide)
theorem g3_merge12_uarb1_cex2 : ∃ D : Dl, BoxReal2 g3_merge12_uarb1_FMIN_lo g3_merge12_uarb1_SMAX_hi 0 0 D ∧ D.smin = 711 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 711 (by decide) (by decide)
theorem g3_merge12_uarb2_box : g3_merge12_uarb2_FMIN_lo.le g3_merge12_uarb2_SMAX_hi = true ∧ (mix1 g3_merge12_uarb2_FMIN_lo g3_merge12_uarb2_SMAX_hi).m1 = -260 ∧
    (mix2 g3_merge12_uarb2_FMIN_lo g3_merge12_uarb2_SMAX_hi).m2 = -493 := by decide
theorem g3_merge12_uarb2_cex1 : ∃ D : Dl, BoxReal1 g3_merge12_uarb2_FMIN_lo g3_merge12_uarb2_SMAX_hi 0 0 D ∧ D.smin = 259 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 259 (by decide) (by decide)
theorem g3_merge12_uarb2_cex2 : ∃ D : Dl, BoxReal2 g3_merge12_uarb2_FMIN_lo g3_merge12_uarb2_SMAX_hi 0 0 D ∧ D.smin = 492 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 492 (by decide) (by decide)
theorem g3_merge2_uarb1_box : g3_merge2_uarb1_FMIN_lo.le g3_merge2_uarb1_SMAX_hi = true ∧ (mix1 g3_merge2_uarb1_FMIN_lo g3_merge2_uarb1_SMAX_hi).m1 = -280 ∧
    (mix2 g3_merge2_uarb1_FMIN_lo g3_merge2_uarb1_SMAX_hi).m2 = -77 := by decide
theorem g3_merge2_uarb1_cex1 : ∃ D : Dl, BoxReal1 g3_merge2_uarb1_FMIN_lo g3_merge2_uarb1_SMAX_hi 0 0 D ∧ D.smin = 279 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 279 (by decide) (by decide)
theorem g3_merge2_uarb1_cex2 : ∃ D : Dl, BoxReal2 g3_merge2_uarb1_FMIN_lo g3_merge2_uarb1_SMAX_hi 0 0 D ∧ D.smin = 76 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 76 (by decide) (by decide)
theorem g3_merge3_uarb1_box : g3_merge3_uarb1_FMIN_lo.le g3_merge3_uarb1_SMAX_hi = true ∧ (mix1 g3_merge3_uarb1_FMIN_lo g3_merge3_uarb1_SMAX_hi).m1 = -390 ∧
    (mix2 g3_merge3_uarb1_FMIN_lo g3_merge3_uarb1_SMAX_hi).m2 = -179 := by decide
theorem g3_merge3_uarb1_cex1 : ∃ D : Dl, BoxReal1 g3_merge3_uarb1_FMIN_lo g3_merge3_uarb1_SMAX_hi 0 0 D ∧ D.smin = 389 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 389 (by decide) (by decide)
theorem g3_merge3_uarb1_cex2 : ∃ D : Dl, BoxReal2 g3_merge3_uarb1_FMIN_lo g3_merge3_uarb1_SMAX_hi 0 0 D ∧ D.smin = 178 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 178 (by decide) (by decide)
theorem g3_merge4_uarb1_box : g3_merge4_uarb1_FMIN_lo.le g3_merge4_uarb1_SMAX_hi = true ∧ (mix1 g3_merge4_uarb1_FMIN_lo g3_merge4_uarb1_SMAX_hi).m1 = -44 ∧
    (mix2 g3_merge4_uarb1_FMIN_lo g3_merge4_uarb1_SMAX_hi).m2 = -236 := by decide
theorem g3_merge4_uarb1_cex1 : ∃ D : Dl, BoxReal1 g3_merge4_uarb1_FMIN_lo g3_merge4_uarb1_SMAX_hi 0 0 D ∧ D.smin = 43 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 43 (by decide) (by decide)
theorem g3_merge4_uarb1_cex2 : ∃ D : Dl, BoxReal2 g3_merge4_uarb1_FMIN_lo g3_merge4_uarb1_SMAX_hi 0 0 D ∧ D.smin = 235 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 235 (by decide) (by decide)
theorem g3_merge6_uarb1_box : g3_merge6_uarb1_FMIN_lo.le g3_merge6_uarb1_SMAX_hi = true ∧ (mix1 g3_merge6_uarb1_FMIN_lo g3_merge6_uarb1_SMAX_hi).m1 = -101 ∧
    (mix2 g3_merge6_uarb1_FMIN_lo g3_merge6_uarb1_SMAX_hi).m2 = -99 := by decide
theorem g3_merge6_uarb1_cex1 : ∃ D : Dl, BoxReal1 g3_merge6_uarb1_FMIN_lo g3_merge6_uarb1_SMAX_hi 0 0 D ∧ D.smin = 100 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 100 (by decide) (by decide)
theorem g3_merge6_uarb1_cex2 : ∃ D : Dl, BoxReal2 g3_merge6_uarb1_FMIN_lo g3_merge6_uarb1_SMAX_hi 0 0 D ∧ D.smin = 98 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 98 (by decide) (by decide)
theorem g3_merge9_uarb1_box : g3_merge9_uarb1_FMIN_lo.le g3_merge9_uarb1_SMAX_hi = true ∧ (mix1 g3_merge9_uarb1_FMIN_lo g3_merge9_uarb1_SMAX_hi).m1 = -383 ∧
    (mix2 g3_merge9_uarb1_FMIN_lo g3_merge9_uarb1_SMAX_hi).m2 = -403 := by decide
theorem g3_merge9_uarb1_cex1 : ∃ D : Dl, BoxReal1 g3_merge9_uarb1_FMIN_lo g3_merge9_uarb1_SMAX_hi 0 0 D ∧ D.smin = 382 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 382 (by decide) (by decide)
theorem g3_merge9_uarb1_cex2 : ∃ D : Dl, BoxReal2 g3_merge9_uarb1_FMIN_lo g3_merge9_uarb1_SMAX_hi 0 0 D ∧ D.smin = 402 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 402 (by decide) (by decide)
theorem g4_merge10_uarb1_box : g4_merge10_uarb1_FMIN_lo.le g4_merge10_uarb1_SMAX_hi = true ∧ (mix1 g4_merge10_uarb1_FMIN_lo g4_merge10_uarb1_SMAX_hi).m1 = -145 ∧
    (mix2 g4_merge10_uarb1_FMIN_lo g4_merge10_uarb1_SMAX_hi).m2 = -5 := by decide
theorem g4_merge10_uarb1_cex1 : ∃ D : Dl, BoxReal1 g4_merge10_uarb1_FMIN_lo g4_merge10_uarb1_SMAX_hi 0 0 D ∧ D.smin = 144 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 144 (by decide) (by decide)
theorem g4_merge10_uarb1_cex2 : ∃ D : Dl, BoxReal2 g4_merge10_uarb1_FMIN_lo g4_merge10_uarb1_SMAX_hi 0 0 D ∧ D.smin = 4 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 4 (by decide) (by decide)
theorem g4_merge11_uarb1_box : g4_merge11_uarb1_FMIN_lo.le g4_merge11_uarb1_SMAX_hi = true ∧ (mix1 g4_merge11_uarb1_FMIN_lo g4_merge11_uarb1_SMAX_hi).m1 = -394 ∧
    (mix2 g4_merge11_uarb1_FMIN_lo g4_merge11_uarb1_SMAX_hi).m2 = -264 := by decide
theorem g4_merge11_uarb1_cex1 : ∃ D : Dl, BoxReal1 g4_merge11_uarb1_FMIN_lo g4_merge11_uarb1_SMAX_hi 0 0 D ∧ D.smin = 393 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 393 (by decide) (by decide)
theorem g4_merge11_uarb1_cex2 : ∃ D : Dl, BoxReal2 g4_merge11_uarb1_FMIN_lo g4_merge11_uarb1_SMAX_hi 0 0 D ∧ D.smin = 263 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 263 (by decide) (by decide)
theorem g4_merge12_uarb1_box : g4_merge12_uarb1_FMIN_lo.le g4_merge12_uarb1_SMAX_hi = true ∧ (mix1 g4_merge12_uarb1_FMIN_lo g4_merge12_uarb1_SMAX_hi).m1 = -491 ∧
    (mix2 g4_merge12_uarb1_FMIN_lo g4_merge12_uarb1_SMAX_hi).m2 = -443 := by decide
theorem g4_merge12_uarb1_cex1 : ∃ D : Dl, BoxReal1 g4_merge12_uarb1_FMIN_lo g4_merge12_uarb1_SMAX_hi 0 0 D ∧ D.smin = 490 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 490 (by decide) (by decide)
theorem g4_merge12_uarb1_cex2 : ∃ D : Dl, BoxReal2 g4_merge12_uarb1_FMIN_lo g4_merge12_uarb1_SMAX_hi 0 0 D ∧ D.smin = 442 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 442 (by decide) (by decide)
theorem g4_merge12_uarb2_box : g4_merge12_uarb2_FMIN_lo.le g4_merge12_uarb2_SMAX_hi = true ∧ (mix1 g4_merge12_uarb2_FMIN_lo g4_merge12_uarb2_SMAX_hi).m1 = 92 ∧
    (mix2 g4_merge12_uarb2_FMIN_lo g4_merge12_uarb2_SMAX_hi).m2 = -387 := by decide
theorem g4_merge12_uarb2_cex2 : ∃ D : Dl, BoxReal2 g4_merge12_uarb2_FMIN_lo g4_merge12_uarb2_SMAX_hi 0 0 D ∧ D.smin = 386 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 386 (by decide) (by decide)
theorem g4_merge2_uarb1_box : g4_merge2_uarb1_FMIN_lo.le g4_merge2_uarb1_SMAX_hi = true ∧ (mix1 g4_merge2_uarb1_FMIN_lo g4_merge2_uarb1_SMAX_hi).m1 = 165 ∧
    (mix2 g4_merge2_uarb1_FMIN_lo g4_merge2_uarb1_SMAX_hi).m2 = -527 := by decide
theorem g4_merge2_uarb1_cex2 : ∃ D : Dl, BoxReal2 g4_merge2_uarb1_FMIN_lo g4_merge2_uarb1_SMAX_hi 0 0 D ∧ D.smin = 526 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 526 (by decide) (by decide)
theorem g4_merge3_uarb1_box : g4_merge3_uarb1_FMIN_lo.le g4_merge3_uarb1_SMAX_hi = true ∧ (mix1 g4_merge3_uarb1_FMIN_lo g4_merge3_uarb1_SMAX_hi).m1 = -410 ∧
    (mix2 g4_merge3_uarb1_FMIN_lo g4_merge3_uarb1_SMAX_hi).m2 = 189 := by decide
theorem g4_merge3_uarb1_cex1 : ∃ D : Dl, BoxReal1 g4_merge3_uarb1_FMIN_lo g4_merge3_uarb1_SMAX_hi 0 0 D ∧ D.smin = 409 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 409 (by decide) (by decide)
theorem g4_merge4_uarb1_box : g4_merge4_uarb1_FMIN_lo.le g4_merge4_uarb1_SMAX_hi = true ∧ (mix1 g4_merge4_uarb1_FMIN_lo g4_merge4_uarb1_SMAX_hi).m1 = -423 ∧
    (mix2 g4_merge4_uarb1_FMIN_lo g4_merge4_uarb1_SMAX_hi).m2 = -300 := by decide
theorem g4_merge4_uarb1_cex1 : ∃ D : Dl, BoxReal1 g4_merge4_uarb1_FMIN_lo g4_merge4_uarb1_SMAX_hi 0 0 D ∧ D.smin = 422 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 422 (by decide) (by decide)
theorem g4_merge4_uarb1_cex2 : ∃ D : Dl, BoxReal2 g4_merge4_uarb1_FMIN_lo g4_merge4_uarb1_SMAX_hi 0 0 D ∧ D.smin = 299 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 299 (by decide) (by decide)
theorem g4_merge6_uarb1_box : g4_merge6_uarb1_FMIN_lo.le g4_merge6_uarb1_SMAX_hi = true ∧ (mix1 g4_merge6_uarb1_FMIN_lo g4_merge6_uarb1_SMAX_hi).m1 = -282 ∧
    (mix2 g4_merge6_uarb1_FMIN_lo g4_merge6_uarb1_SMAX_hi).m2 = -216 := by decide
theorem g4_merge6_uarb1_cex1 : ∃ D : Dl, BoxReal1 g4_merge6_uarb1_FMIN_lo g4_merge6_uarb1_SMAX_hi 0 0 D ∧ D.smin = 281 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 281 (by decide) (by decide)
theorem g4_merge6_uarb1_cex2 : ∃ D : Dl, BoxReal2 g4_merge6_uarb1_FMIN_lo g4_merge6_uarb1_SMAX_hi 0 0 D ∧ D.smin = 215 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 215 (by decide) (by decide)
theorem g4_merge9_uarb1_box : g4_merge9_uarb1_FMIN_lo.le g4_merge9_uarb1_SMAX_hi = true ∧ (mix1 g4_merge9_uarb1_FMIN_lo g4_merge9_uarb1_SMAX_hi).m1 = -163 ∧
    (mix2 g4_merge9_uarb1_FMIN_lo g4_merge9_uarb1_SMAX_hi).m2 = -281 := by decide
theorem g4_merge9_uarb1_cex1 : ∃ D : Dl, BoxReal1 g4_merge9_uarb1_FMIN_lo g4_merge9_uarb1_SMAX_hi 0 0 D ∧ D.smin = 162 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 162 (by decide) (by decide)
theorem g4_merge9_uarb1_cex2 : ∃ D : Dl, BoxReal2 g4_merge9_uarb1_FMIN_lo g4_merge9_uarb1_SMAX_hi 0 0 D ∧ D.smin = 280 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 280 (by decide) (by decide)
theorem gd_merge10_uarb1_box : gd_merge10_uarb1_FMIN_lo.le gd_merge10_uarb1_SMAX_hi = true ∧ (mix1 gd_merge10_uarb1_FMIN_lo gd_merge10_uarb1_SMAX_hi).m1 = -44 ∧
    (mix2 gd_merge10_uarb1_FMIN_lo gd_merge10_uarb1_SMAX_hi).m2 = 18 := by decide
theorem gd_merge10_uarb1_cex1 : ∃ D : Dl, BoxReal1 gd_merge10_uarb1_FMIN_lo gd_merge10_uarb1_SMAX_hi 0 0 D ∧ D.smin = 43 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 43 (by decide) (by decide)
theorem gd_merge11_uarb1_box : gd_merge11_uarb1_FMIN_lo.le gd_merge11_uarb1_SMAX_hi = true ∧ (mix1 gd_merge11_uarb1_FMIN_lo gd_merge11_uarb1_SMAX_hi).m1 = -474 ∧
    (mix2 gd_merge11_uarb1_FMIN_lo gd_merge11_uarb1_SMAX_hi).m2 = -63 := by decide
theorem gd_merge11_uarb1_cex1 : ∃ D : Dl, BoxReal1 gd_merge11_uarb1_FMIN_lo gd_merge11_uarb1_SMAX_hi 0 0 D ∧ D.smin = 473 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 473 (by decide) (by decide)
theorem gd_merge11_uarb1_cex2 : ∃ D : Dl, BoxReal2 gd_merge11_uarb1_FMIN_lo gd_merge11_uarb1_SMAX_hi 0 0 D ∧ D.smin = 62 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 62 (by decide) (by decide)
theorem gd_merge12_uarb1_box : gd_merge12_uarb1_FMIN_lo.le gd_merge12_uarb1_SMAX_hi = true ∧ (mix1 gd_merge12_uarb1_FMIN_lo gd_merge12_uarb1_SMAX_hi).m1 = -133 ∧
    (mix2 gd_merge12_uarb1_FMIN_lo gd_merge12_uarb1_SMAX_hi).m2 = -288 := by decide
theorem gd_merge12_uarb1_cex1 : ∃ D : Dl, BoxReal1 gd_merge12_uarb1_FMIN_lo gd_merge12_uarb1_SMAX_hi 0 0 D ∧ D.smin = 132 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 132 (by decide) (by decide)
theorem gd_merge12_uarb1_cex2 : ∃ D : Dl, BoxReal2 gd_merge12_uarb1_FMIN_lo gd_merge12_uarb1_SMAX_hi 0 0 D ∧ D.smin = 287 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 287 (by decide) (by decide)
theorem gd_merge12_uarb2_box : gd_merge12_uarb2_FMIN_lo.le gd_merge12_uarb2_SMAX_hi = true ∧ (mix1 gd_merge12_uarb2_FMIN_lo gd_merge12_uarb2_SMAX_hi).m1 = -341 ∧
    (mix2 gd_merge12_uarb2_FMIN_lo gd_merge12_uarb2_SMAX_hi).m2 = -565 := by decide
theorem gd_merge12_uarb2_cex1 : ∃ D : Dl, BoxReal1 gd_merge12_uarb2_FMIN_lo gd_merge12_uarb2_SMAX_hi 0 0 D ∧ D.smin = 340 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 340 (by decide) (by decide)
theorem gd_merge12_uarb2_cex2 : ∃ D : Dl, BoxReal2 gd_merge12_uarb2_FMIN_lo gd_merge12_uarb2_SMAX_hi 0 0 D ∧ D.smin = 564 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 564 (by decide) (by decide)
theorem gd_merge2_uarb1_box : gd_merge2_uarb1_FMIN_lo.le gd_merge2_uarb1_SMAX_hi = true ∧ (mix1 gd_merge2_uarb1_FMIN_lo gd_merge2_uarb1_SMAX_hi).m1 = -394 ∧
    (mix2 gd_merge2_uarb1_FMIN_lo gd_merge2_uarb1_SMAX_hi).m2 = -345 := by decide
theorem gd_merge2_uarb1_cex1 : ∃ D : Dl, BoxReal1 gd_merge2_uarb1_FMIN_lo gd_merge2_uarb1_SMAX_hi 0 0 D ∧ D.smin = 393 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 393 (by decide) (by decide)
theorem gd_merge2_uarb1_cex2 : ∃ D : Dl, BoxReal2 gd_merge2_uarb1_FMIN_lo gd_merge2_uarb1_SMAX_hi 0 0 D ∧ D.smin = 344 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 344 (by decide) (by decide)
theorem gd_merge3_uarb1_box : gd_merge3_uarb1_FMIN_lo.le gd_merge3_uarb1_SMAX_hi = true ∧ (mix1 gd_merge3_uarb1_FMIN_lo gd_merge3_uarb1_SMAX_hi).m1 = -422 ∧
    (mix2 gd_merge3_uarb1_FMIN_lo gd_merge3_uarb1_SMAX_hi).m2 = -39 := by decide
theorem gd_merge3_uarb1_cex1 : ∃ D : Dl, BoxReal1 gd_merge3_uarb1_FMIN_lo gd_merge3_uarb1_SMAX_hi 0 0 D ∧ D.smin = 421 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 421 (by decide) (by decide)
theorem gd_merge3_uarb1_cex2 : ∃ D : Dl, BoxReal2 gd_merge3_uarb1_FMIN_lo gd_merge3_uarb1_SMAX_hi 0 0 D ∧ D.smin = 38 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 38 (by decide) (by decide)
theorem gd_merge4_uarb1_box : gd_merge4_uarb1_FMIN_lo.le gd_merge4_uarb1_SMAX_hi = true ∧ (mix1 gd_merge4_uarb1_FMIN_lo gd_merge4_uarb1_SMAX_hi).m1 = -139 ∧
    (mix2 gd_merge4_uarb1_FMIN_lo gd_merge4_uarb1_SMAX_hi).m2 = -235 := by decide
theorem gd_merge4_uarb1_cex1 : ∃ D : Dl, BoxReal1 gd_merge4_uarb1_FMIN_lo gd_merge4_uarb1_SMAX_hi 0 0 D ∧ D.smin = 138 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 138 (by decide) (by decide)
theorem gd_merge4_uarb1_cex2 : ∃ D : Dl, BoxReal2 gd_merge4_uarb1_FMIN_lo gd_merge4_uarb1_SMAX_hi 0 0 D ∧ D.smin = 234 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 234 (by decide) (by decide)
theorem gd_merge6_uarb1_box : gd_merge6_uarb1_FMIN_lo.le gd_merge6_uarb1_SMAX_hi = true ∧ (mix1 gd_merge6_uarb1_FMIN_lo gd_merge6_uarb1_SMAX_hi).m1 = -21 ∧
    (mix2 gd_merge6_uarb1_FMIN_lo gd_merge6_uarb1_SMAX_hi).m2 = 173 := by decide
theorem gd_merge6_uarb1_cex1 : ∃ D : Dl, BoxReal1 gd_merge6_uarb1_FMIN_lo gd_merge6_uarb1_SMAX_hi 0 0 D ∧ D.smin = 20 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 20 (by decide) (by decide)
theorem gd_merge9_uarb1_box : gd_merge9_uarb1_FMIN_lo.le gd_merge9_uarb1_SMAX_hi = true ∧ (mix1 gd_merge9_uarb1_FMIN_lo gd_merge9_uarb1_SMAX_hi).m1 = -395 ∧
    (mix2 gd_merge9_uarb1_FMIN_lo gd_merge9_uarb1_SMAX_hi).m2 = -397 := by decide
theorem gd_merge9_uarb1_cex1 : ∃ D : Dl, BoxReal1 gd_merge9_uarb1_FMIN_lo gd_merge9_uarb1_SMAX_hi 0 0 D ∧ D.smin = 394 ∧ D.wa0s = 0 ∧
    D.qf = 0 ∧ ¬ RT1 D :=
  box_cex1 _ _ (by decide) (by decide) (by decide) 394 (by decide) (by decide)
theorem gd_merge9_uarb1_cex2 : ∃ D : Dl, BoxReal2 gd_merge9_uarb1_FMIN_lo gd_merge9_uarb1_SMAX_hi 0 0 D ∧ D.smin = 396 ∧ D.wa0s = 0 ∧
    D.qr = 0 ∧ ¬ RT1b D :=
  box_cex2 _ _ (by decide) (by decide) (by decide) 396 (by decide) (by decide)

end Formal.Cells.OnGcdArbFix
