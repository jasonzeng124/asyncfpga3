import Formal.Cells.ArbHandover
import Formal.Cells.ArbHeldTimed
import Formal.Cells.ArbHeldTimed2
import Formal.Cells.ArbA0Fork

/-!
# Probe Bc: corner-consistent arc numbers for the arbiter probes (7e, 7g, 7h, 7j)

`formal/notes/B-gls-compare.md` §1 found (and checked against prjxray's
`utils/makesdf.py`) that prjxray writes every cell arc as

    (IOPATH in out (FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX))

so the two groups are the FAST and SLOW speed corners of ONE arc, not a
rise/fall split. Probes 7e (`ArbHandover`), 7h (`ArbHeldTimed`), 7j
(`ArbHeldTimed2`) read `(0.045::0.056)(0.100::0.124)` as "rise 56, fall 124",
which puts FAST_MAX and SLOW_MAX of one arc into one run. Their theorems are
parametric and stay true; their numeric instances are corner-mixed. This file
(the old files are untouched and only imported):

* §0  the exact prjxray numbers (`CLBLL_L.sdf`, SLICEL, read from the file in
       the scratchpad; see the notes), a consistent `Corner` and the named,
       UNMEASURED rise/fall asymmetry `RF` (H_RF_ASYM);
* §1  7e re-instantiated: handover overlap, `sim_overlap`, the skew caps,
       the exact skew thresholds per corner, the full box;
* §2  7h / 7j re-instantiated: every arc condition as `arc part + wire part`,
       the corner values, the box worst case, the old `prj` shown to be the
       corner mix, the runt band;
* §3  corner sign changes: cells and wires scale differently between corners;
       the exact routing window where a margin flips sign, as a theorem over the
       wire ratio `k = kn / kd`; applied to RT1/RT2 (7h/7j), the 7e overlap and
       rule J (7g, on its real run semantics `client{1,2}_iff`);
* §4  non-vacuity at the SLOW_MAX and FAST_MIN corners (explicit runs).

Fidelity: the LUT functions are the real INITs (inherited from 7e/7h/7j/7g:
`lutB`/`o5B`/`o6B`); the LUT timing is the old probes' channels unchanged
(rise-fast OR pure-delay channel of 7e/7h, per-pin transport of 7g). Only the
numbers they are instantiated with change.
-/

namespace Formal.Cells.ArbCorners
open Formal.Cells

/-! ## §0 The prjxray numbers -/

/-- One prjxray IOPATH, in ps: `(FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX)`.
Source: prjxray `CLBLL_L.sdf` (cell SLICEL), the file
`utils/makesdf.py` writes. There is NO rise/fall information in it. -/
structure Col where
  fmin : Int
  fmax : Int
  smin : Int
  smax : Int

/-- `SLICEL/A6LUT (IOPATH A1..A6 O6 (0.045::0.056)(0.100::0.124))`: flat over pins. -/
def O6 : Col := ⟨45, 56, 100, 124⟩
/-- `SLICEL/A5LUT (IOPATH A1 O5 (0.044::0.055)(0.122::0.152))` (logical I0 under the identity pin map). -/
def O5_I0 : Col := ⟨44, 55, 122, 152⟩
/-- `SLICEL/A5LUT (IOPATH A2 O5 (0.044::0.055)(0.122::0.152))` (I1). -/
def O5_I1 : Col := ⟨44, 55, 122, 152⟩
/-- `SLICEL/A5LUT (IOPATH A3 O5 (0.042::0.052)(0.121::0.150))` (I2, the q pin). -/
def O5_I2 : Col := ⟨42, 52, 121, 150⟩

theorem O5_I0_eq_I1 : O5_I0 = O5_I1 := rfl

/-- A CONSISTENT corner: every arc of the arbiter taken from the same column.
Three arc classes suffice for bd_arbiter: any pin to O6 (`o6`), I0/I1 to O5
(`o5a`), I2 to O5 (`o5q`). Rise and fall equal within the corner unless an
explicit `RF` asymmetry is added. -/
structure Corner where
  o6 : Int
  o5a : Int
  o5q : Int
  H_pos : 0 < o6 ∧ 0 ≤ o5a ∧ 0 ≤ o5q

def Corner.of (sel : Col → Int) (h : 0 < sel O6 ∧ 0 ≤ sel O5_I0 ∧ 0 ≤ sel O5_I2) : Corner :=
  ⟨sel O6, sel O5_I0, sel O5_I2, h⟩

/-- Every arc at SLOW_MAX (the column nextpnr's SDF and every post-route rule use). -/
def slowMax : Corner := Corner.of Col.smax (by decide)
/-- Every arc at FAST_MIN. -/
def fastMin : Corner := Corner.of Col.fmin (by decide)
/-- Every arc at FAST_MAX. -/
def fastMax : Corner := Corner.of Col.fmax (by decide)
/-- Every arc at SLOW_MIN. -/
def slowMin : Corner := Corner.of Col.smin (by decide)

theorem slowMax_vals : slowMax.o6 = 124 ∧ slowMax.o5a = 152 ∧ slowMax.o5q = 150 := by decide
theorem fastMin_vals : fastMin.o6 = 45 ∧ fastMin.o5a = 44 ∧ fastMin.o5q = 42 := by decide
theorem fastMax_vals : fastMax.o6 = 56 ∧ fastMax.o5a = 55 ∧ fastMax.o5q = 52 := by decide
theorem slowMin_vals : slowMin.o6 = 100 ∧ slowMin.o5a = 122 ∧ slowMin.o5q = 121 := by decide

/-- **H_RF_ASYM** (named, UNMEASURED): fall arc minus rise arc, per arc class.
Nothing in the repo or in prjxray measures it (prjxray dumps only the Vivado
speed-model corners FAST_MIN/FAST_MAX/SLOW_MIN/SLOW_MAX, no edge split).
Physical fact it stands for: the NMOS/PMOS imbalance of the LUT output stage.
Test (board): ring oscillators with an odd number of inverting LUTs vs. the
same ring of buffers; the period difference per stage is (fall − rise).
Only `0 ≤ d` can be expressed: the 7e/7h channel is the rise-FAST OR channel
and needs rise ≤ fall (`H_rise_le_fall`/`H_RISE_LE_FALL`). The consistent
default is `RF.sym` (all zero), which is what the research GLS writes. -/
structure RF where
  d6 : Int
  d5a : Int
  d5q : Int
  H_nonneg : 0 ≤ d6 ∧ 0 ≤ d5a ∧ 0 ≤ d5q

/-- No rise/fall asymmetry (the prjxray data, and the research GLS). -/
def RF.sym : RF := ⟨0, 0, 0, by decide⟩

/-- The corner MIX the old instances used: rise = FAST_MAX, fall = SLOW_MAX.
Its "asymmetry" 68/97/98 ps is the fast-to-slow corner spread, not an edge
property. -/
def mixRise : Corner := fastMax
def mixRF : RF := ⟨124 - 56, 152 - 55, 150 - 52, by decide⟩

/-! ## §1 Probe 7e (`ArbHandover`): the bare-cell handover -/

section Handover
open ArbHandover

/-- 7e's `Arcs` at a corner `c` with asymmetry `r`. -/
def arcsC (c : Corner) (r : RF) (w wfb : Int) (hw : 0 ≤ w) (hfb : 0 ≤ wfb) : Arcs where
  qr := c.o6
  qf := c.o6 + r.d6
  w := w
  wfb := wfb
  g1r_q := c.o5q
  g1f_q := c.o5q + r.d5q
  g1r_r1 := c.o5a
  g1f_r1 := c.o5a + r.d5a
  g2r := c.o6
  g2f := c.o6 + r.d6
  H_nonneg := by have := c.H_pos; omega
  H_rise_le_fall := by have := r.H_nonneg; omega

/-- **The old instance is the corner mix.** 7e's `prjArcs w` is exactly
`arcsC` at rise = FAST_MAX with the fast-to-slow spread used as "fall − rise". -/
theorem prjArcs_is_mix (w : Int) (hw : 0 ≤ w) :
    prjArcs w hw = arcsC mixRise mixRF w 0 hw (by decide) := rfl

/-- **Handover overlap r2 → r1 at any corner, any asymmetry**: the number of ps
with both grants high is `max 0 (d6 − o5q − w)`. The arcs of the two O6 LUTs
cancel; an overlap needs a rise/fall asymmetry larger than a whole O5 arc. -/
theorem overlap_C (c : Corner) (r : RF) (w wfb : Int) (hw : 0 ≤ w) (hfb : 0 ≤ wfb)
    (t0 : Int) (r1 r2 q g1 g2 : Sig) (C : Cell (arcsC c r w wfb hw hfb) r1 r2 q g1 g2)
    (H_r1 : ∀ t, r1 t = true) (H_r2 : ∀ t, r2 t = decide (t < t0))
    (H_init : ∀ t, t < t0 → q t = false) (n : Nat) (hn : c.o6 + r.d6 ≤ n) :
    (countTrue (fun t => g1 t && g2 t) t0 n : Int) = max 0 (r.d6 - c.o5q - w) := by
  have := overlap_duration_r2_to_r1 _ t0 r1 r2 q g1 g2 C H_r1 H_r2 H_init n hn
  rw [this]; simp only [arcsC]; omega

/-- **Corrected `header_16ps` / `header_routed`**: at every consistent corner
(rise = fall), for every q routing `w ≥ 0`, the r2 → r1 handover has NO grant
overlap. -/
theorem corner_no_overlap (c : Corner) (w wfb : Int) (hw : 0 ≤ w) (hfb : 0 ≤ wfb)
    (t0 : Int) (r1 r2 q g1 g2 : Sig) (C : Cell (arcsC c RF.sym w wfb hw hfb) r1 r2 q g1 g2)
    (H_r1 : ∀ t, r1 t = true) (H_r2 : ∀ t, r2 t = decide (t < t0))
    (H_init : ∀ t, t < t0 → q t = false) :
    ∀ t, (g1 t && g2 t) = false := by
  have := c.H_pos
  exact no_overlap_r2_to_r1 _ t0 r1 r2 q g1 g2 C H_r1 H_r2 H_init
    (by simp only [arcsC, RF.sym]; omega)

/-- The header's 16 ps, re-read: it is `overlap_C` with the corner spread used
as an asymmetry, `d6 − o5q − w = 68 − 52 − 0`. As a statement about H_RF_ASYM:
an r2 → r1 overlap exists iff `d6 > o5q + w`. -/
theorem header_needs_asym (c : Corner) (r : RF) (w wfb : Int) (hw : 0 ≤ w) (hfb : 0 ≤ wfb)
    (t0 : Int) (r1 r2 q g1 g2 : Sig) (C : Cell (arcsC c r w wfb hw hfb) r1 r2 q g1 g2)
    (H_r1 : ∀ t, r1 t = true) (H_r2 : ∀ t, r2 t = decide (t < t0))
    (H_init : ∀ t, t < t0 → q t = false) :
    (∃ t, (g1 t && g2 t) = true) ↔ c.o5q + w < r.d6 := by
  have h := overlap_r2_to_r1 _ t0 r1 r2 q g1 g2 C H_r1 H_r2 H_init
  constructor
  · rintro ⟨t, ht⟩
    have := (h t).1 ht
    simp only [arcsC] at this; omega
  · intro hd
    refine ⟨t0 + (c.o6 + w + c.o5q), (h _).2 ?_⟩
    simp only [arcsC]; omega

theorem mix_header_16 : mixRF.d6 - mixRise.o5q - 0 = 16 := by decide

/-- Numeric instances: SLOW_MAX and FAST_MIN, zero routing: 0 ps (was 16). -/
theorem slow_header (t0 : Int) (r1 r2 q g1 g2 : Sig)
    (C : Cell (arcsC slowMax RF.sym 0 0 (by decide) (by decide)) r1 r2 q g1 g2)
    (H_r1 : ∀ t, r1 t = true) (H_r2 : ∀ t, r2 t = decide (t < t0))
    (H_init : ∀ t, t < t0 → q t = false) :
    countTrue (fun t => g1 t && g2 t) t0 124 = 0 := by
  have := overlap_C slowMax RF.sym 0 0 (by decide) (by decide) t0 r1 r2 q g1 g2 C
    H_r1 H_r2 H_init 124 (by decide)
  have h2 : max 0 (RF.sym.d6 - slowMax.o5q - 0) = 0 := by decide
  omega

theorem fast_header (t0 : Int) (r1 r2 q g1 g2 : Sig)
    (C : Cell (arcsC fastMin RF.sym 0 0 (by decide) (by decide)) r1 r2 q g1 g2)
    (H_r1 : ∀ t, r1 t = true) (H_r2 : ∀ t, r2 t = decide (t < t0))
    (H_init : ∀ t, t < t0 → q t = false) :
    countTrue (fun t => g1 t && g2 t) t0 45 = 0 := by
  have := overlap_C fastMin RF.sym 0 0 (by decide) (by decide) t0 r1 r2 q g1 g2 C
    H_r1 H_r2 H_init 45 (by decide)
  have h2 : max 0 (RF.sym.d6 - fastMin.o5q - 0) = 0 := by decide
  omega

/-- `cells/sim`'s `BD_ROUTE_PS = R` adds `R` to every arc (7e's `simArcs`), here
at a corner with asymmetry `r`. -/
def simArcsC (c : Corner) (r : RF) (R : Int) (hR : 0 ≤ R) : Arcs where
  qr := c.o6 + R
  qf := c.o6 + r.d6 + R
  w := 0
  wfb := 0
  g1r_q := c.o5q + R
  g1f_q := c.o5q + r.d5q + R
  g1r_r1 := c.o5a + R
  g1f_r1 := c.o5a + r.d5a + R
  g2r := c.o6 + R
  g2f := c.o6 + r.d6 + R
  H_nonneg := by have := c.H_pos; omega
  H_rise_le_fall := by have := r.H_nonneg; omega

/-- **Corrected `sim_overlap`**: the overlap is `max 0 (d6 − o5q − R)`; with
the corner mix (7e's `simArcs`) that is `max 0 (16 − R)`, and with consistent
arcs (`RF.sym`) it is 0 for every `R ≥ 0`. -/
theorem sim_overlap_C (c : Corner) (r : RF) (R : Int) (hR : 0 ≤ R) (t0 : Int)
    (r1 r2 q g1 g2 : Sig) (C : Cell (simArcsC c r R hR) r1 r2 q g1 g2)
    (H_r1 : ∀ t, r1 t = true) (H_r2 : ∀ t, r2 t = decide (t < t0))
    (H_init : ∀ t, t < t0 → q t = false) (n : Nat) (hn : c.o6 + r.d6 + R ≤ n) :
    (countTrue (fun t => g1 t && g2 t) t0 n : Int) = max 0 (r.d6 - c.o5q - R) := by
  have := overlap_duration_r2_to_r1 _ t0 r1 r2 q g1 g2 C H_r1 H_r2 H_init n hn
  rw [this]; simp only [simArcsC]; omega

theorem simArcs_is_mix (R : Int) (hR : 0 ≤ R) : simArcs R hR = simArcsC mixRise mixRF R hR := by
  simp only [simArcs, simArcsC, mixRise, mixRF, fastMax, Corner.of, O6, O5_I0, O5_I2]
  congr 1 <;> omega

/-- **Reverse direction r1 → r2 at a consistent corner**: no overlap iff
`o5a ≤ 2·o6 + w`; true at all four columns for every `w ≥ 0`
(margins 96 + w at SLOW_MAX, 46 + w at FAST_MIN; was 28 + w). -/
theorem corner_r1_to_r2 (c : Corner) (w wfb : Int) (hw : 0 ≤ w) (hfb : 0 ≤ wfb)
    (t0 : Int) (r1 r2 q g1 g2 : Sig) (C : Cell (arcsC c RF.sym w wfb hw hfb) r1 r2 q g1 g2)
    (H_r2 : ∀ t, r2 t = true) (H_r1 : ∀ t, r1 t = decide (t < t0))
    (H_init : ∀ t, t < t0 → q t = true)
    (H_g1_by_r1 : c.o5a ≤ c.o6 + w + c.o5q) :
    (∃ t, (g1 t && g2 t) = true) ↔ 2 * c.o6 + w < c.o5a := by
  have h := overlap_r1_to_r2 _ t0 r1 r2 q g1 g2 C H_r2 H_r1 H_init
    (by simp only [arcsC, RF.sym]; omega)
  constructor
  · rintro ⟨t, ht⟩
    have := (h t).1 ht
    simp only [arcsC, RF.sym] at this; omega
  · intro hd
    refine ⟨t0 + (c.o6 + w + c.o6), (h _).2 ?_⟩
    simp only [arcsC, RF.sym]; omega

theorem r1_to_r2_margins :
    2 * slowMax.o6 - slowMax.o5a = 96 ∧ 2 * fastMin.o6 - fastMin.o5a = 46 ∧
    2 * fastMax.o6 - fastMax.o5a = 57 ∧ 2 * slowMin.o6 - slowMin.o5a = 78 ∧
    slowMax.o5a ≤ slowMax.o6 + slowMax.o5q ∧ fastMin.o5a ≤ fastMin.o6 + fastMin.o5q ∧
    fastMax.o5a ≤ fastMax.o6 + fastMax.o5q ∧ slowMin.o5a ≤ slowMin.o6 + slowMin.o5q := by
  decide

/-! ### Request-fork skew at a consistent corner: exact thresholds

With the request reaching ugrant `σ` after ustate (7e's skew theorems), the
overlap is no longer zero at every corner, and WHICH direction can overlap
depends on the corner: the sign of `o6 − o5q` flips between SLOW_MAX (−26)
and FAST_MIN (+3). This is a pure-arc sign change (no wire ratio involved). -/

theorem skew_r2_to_r1_C (c : Corner) (w wfb : Int) (hw : 0 ≤ w) (hfb : 0 ≤ wfb)
    (t0 σ : Int) (r1 r2s r2g q g1 g2 : Sig)
    (Hs : LutOut3 stateF r1 r2s (fun s => q (s - wfb)) c.o6 c.o6 c.o6 c.o6 c.o6 c.o6 q)
    (H_g1 : LutOut3 g1F r1 r2g (fun s => q (s - w)) c.o5a c.o5a c.o5q c.o5a c.o5a c.o5q g1)
    (H_g2 : LutOut3 g2F r1 r2g (fun s => q (s - w)) c.o6 c.o6 c.o6 c.o6 c.o6 c.o6 g2)
    (H_r1 : ∀ t, r1 t = true) (H_r2s : ∀ t, r2s t = decide (t < t0))
    (H_r2g : ∀ t, r2g t = decide (t < t0 + σ))
    (H_init : ∀ t, t < t0 → q t = false) :
    (∃ t, (g1 t && g2 t) = true) ↔ (c.o5q < c.o6 ∧ c.o5q + w < σ) := by
  have := c.H_pos
  have h := overlap_skew_r2_to_r1 (arcsC c RF.sym w wfb hw hfb) t0 σ r1 r2s r2g q g1 g2
    (by simpa [arcsC, RF.sym] using Hs) (by simpa [arcsC, RF.sym] using H_g1)
    (by simpa [arcsC, RF.sym] using H_g2) H_r1 H_r2s H_r2g H_init
  constructor
  · rintro ⟨t, ht⟩
    have := (h t).1 ht
    simp only [arcsC, RF.sym] at this; omega
  · intro hd
    refine ⟨t0 + (c.o6 + w + c.o5q), (h _).2 ?_⟩
    simp only [arcsC, RF.sym]; omega

theorem skew_r1_to_r2_C (c : Corner) (w wfb : Int) (hw : 0 ≤ w) (hfb : 0 ≤ wfb)
    (t0 σ : Int) (r1s r1g r2 q g1 g2 : Sig)
    (Hs : LutOut3 stateF r1s r2 (fun s => q (s - wfb)) c.o6 c.o6 c.o6 c.o6 c.o6 c.o6 q)
    (H_g1 : LutOut3 g1F r1g r2 (fun s => q (s - w)) c.o5a c.o5a c.o5q c.o5a c.o5a c.o5q g1)
    (H_g2 : LutOut3 g2F r1g r2 (fun s => q (s - w)) c.o6 c.o6 c.o6 c.o6 c.o6 c.o6 g2)
    (H_r2 : ∀ t, r2 t = true) (H_r1s : ∀ t, r1s t = decide (t < t0))
    (H_r1g : ∀ t, r1g t = decide (t < t0 + σ))
    (H_init : ∀ t, t < t0 → q t = true) :
    (∃ t, (g1 t && g2 t) = true) ↔ (c.o6 < c.o5q ∧ 2 * c.o6 + w - c.o5a < σ) := by
  have := c.H_pos
  have h := overlap_skew_r1_to_r2 (arcsC c RF.sym w wfb hw hfb) t0 σ r1s r1g r2 q g1 g2
    (by simpa [arcsC, RF.sym] using Hs) (by simpa [arcsC, RF.sym] using H_g1)
    (by simpa [arcsC, RF.sym] using H_g2) H_r2 H_r1s H_r1g H_init
  constructor
  · rintro ⟨t, ht⟩
    have := (h t).1 ht
    simp only [arcsC, RF.sym] at this; omega
  · intro hd
    refine ⟨t0 + (c.o6 + w + c.o6), (h _).2 ?_⟩
    simp only [arcsC, RF.sym]; omega

/-- **Corrected skew caps** (7e's `prj_overlap_caps` said 72 / 94 ps).
For every skew and routing the overlap is at most `max 0 (o6 − o5q)` (r2 → r1)
and `max 0 (o5q − o6)` (r1 → r2): SLOW_MAX 0 / 26 ps, FAST_MIN 3 / 0 ps,
FAST_MAX 4 / 0, SLOW_MIN 0 / 21. Note B-gls-compare's table said 0 / 0
("all arcs equal d"): with prjxray's real O5-vs-O6 difference it is not 0. -/
theorem corner_caps :
    max 0 (slowMax.o6 - slowMax.o5q) = 0 ∧ max 0 (slowMax.o5q - slowMax.o6) = 26 ∧
    max 0 (fastMin.o6 - fastMin.o5q) = 3 ∧ max 0 (fastMin.o5q - fastMin.o6) = 0 ∧
    max 0 (fastMax.o6 - fastMax.o5q) = 4 ∧ max 0 (fastMax.o5q - fastMax.o6) = 0 ∧
    max 0 (slowMin.o6 - slowMin.o5q) = 0 ∧ max 0 (slowMin.o5q - slowMin.o6) = 21 := by
  decide

/-- The caps of 7e applied to `arcsC`: they are `o6 − o5q` and `o5q − o6`. -/
theorem caps_are (c : Corner) (w wfb : Int) (hw : 0 ≤ w) (hfb : 0 ≤ wfb) :
    (arcsC c RF.sym w wfb hw hfb).g2f - (arcsC c RF.sym w wfb hw hfb).g1r_q = c.o6 - c.o5q ∧
    (arcsC c RF.sym w wfb hw hfb).g1f_q - (arcsC c RF.sym w wfb hw hfb).g2r = c.o5q - c.o6 := by
  simp [arcsC, RF.sym]

/-! ### The full box: every arc independently in [FAST_MIN, SLOW_MAX] -/

/-- H_DELAY_BOX for 7e: each arc independently anywhere in its prjxray
[FAST_MIN, SLOW_MAX] interval, rise = fall per arc (H_RF_ASYM excluded). -/
def InBoxA (A : Arcs) : Prop :=
  A.qr = A.qf ∧ A.g2r = A.g2f ∧ A.g1r_q = A.g1f_q ∧ A.g1r_r1 = A.g1f_r1 ∧
  O6.fmin ≤ A.qr ∧ A.qr ≤ O6.smax ∧ O6.fmin ≤ A.g2r ∧ A.g2r ≤ O6.smax ∧
  O5_I2.fmin ≤ A.g1r_q ∧ A.g1r_q ≤ O5_I2.smax ∧ O5_I0.fmin ≤ A.g1r_r1 ∧ A.g1r_r1 ≤ O5_I0.smax

/-- **Box, zero skew, r2 → r1**: overlap at most `max 0 (37 − w)` ps. -/
theorem box_overlap_le (A : Arcs) (hb : InBoxA A) (t0 : Int) (r1 r2 q g1 g2 : Sig)
    (C : Cell A r1 r2 q g1 g2)
    (H_r1 : ∀ t, r1 t = true) (H_r2 : ∀ t, r2 t = decide (t < t0))
    (H_init : ∀ t, t < t0 → q t = false) (n : Nat) (hn : A.g2f ≤ n) :
    (countTrue (fun t => g1 t && g2 t) t0 n : Int) ≤ max 0 (37 - A.w) := by
  have := overlap_duration_r2_to_r1 A t0 r1 r2 q g1 g2 C H_r1 H_r2 H_init n hn
  unfold InBoxA at hb; simp only [O6, O5_I0, O5_I2] at hb
  omega

/-- The box worst corner for 7e: g2's arc at SLOW_MAX, q's and g1's q-pin arc
at FAST_MIN. -/
def worstA (w : Int) (hw : 0 ≤ w) : Arcs where
  qr := 45
  qf := 45
  w := w
  wfb := 0
  g1r_q := 42
  g1f_q := 42
  g1r_r1 := 152
  g1f_r1 := 152
  g2r := 124
  g2f := 124
  H_nonneg := by omega
  H_rise_le_fall := by omega

theorem worstA_inBox (w : Int) (hw : 0 ≤ w) : InBoxA (worstA w hw) := by
  simp [InBoxA, worstA, O6, O5_I0, O5_I2]

/-- The box bound is attained: `max 0 (37 − w)` exactly (B-gls-compare's 37). -/
theorem box_overlap_worst (w : Int) (hw : 0 ≤ w) (t0 : Int) (r1 r2 q g1 g2 : Sig)
    (C : Cell (worstA w hw) r1 r2 q g1 g2)
    (H_r1 : ∀ t, r1 t = true) (H_r2 : ∀ t, r2 t = decide (t < t0))
    (H_init : ∀ t, t < t0 → q t = false) (n : Nat) (hn : (124 : Int) ≤ n) :
    (countTrue (fun t => g1 t && g2 t) t0 n : Int) = max 0 (37 - w) := by
  have := overlap_duration_r2_to_r1 _ t0 r1 r2 q g1 g2 C H_r1 H_r2 H_init n hn
  rw [this]; simp only [worstA]; omega

/-- **Box skew caps**: for every arc set in the box, 82 ps (r2 → r1) and 105 ps
(r1 → r2), attained by the box corners (B-gls-compare's numbers). -/
theorem box_caps (A : Arcs) (hb : InBoxA A) :
    A.g2f - A.g1r_q ≤ 82 ∧ A.g1f_q - A.g2r ≤ 105 := by
  unfold InBoxA at hb; simp only [O6, O5_I0, O5_I2] at hb; omega

theorem box_caps_attained :
    O6.smax - O5_I2.fmin = 82 ∧ O5_I2.smax - O6.fmin = 105 := by decide

/-- **Box, zero skew, r1 → r2**: the overlap is at most `max 0 (62 − w)` ps
(7e's `header_r1_to_r2` "never" holds only for its corner mix). -/
theorem box_r1_to_r2_le (A : Arcs) (hb : InBoxA A) (t0 : Int) (r1 r2 q g1 g2 : Sig)
    (C : Cell A r1 r2 q g1 g2)
    (H_r2 : ∀ t, r2 t = true) (H_r1 : ∀ t, r1 t = decide (t < t0))
    (H_init : ∀ t, t < t0 → q t = true) (n : Nat) :
    (countTrue (fun t => g1 t && g2 t) t0 n : Int) ≤ max 0 (62 - A.w) := by
  have hov := overlap_skew_r1_to_r2 A t0 0 r1 r1 r2 q g1 g2 C.H_state C.H_g1 C.H_g2 H_r2 H_r1
    (by intro t; rw [H_r1]; simp) H_init
  unfold InBoxA at hb; simp only [O6, O5_I0, O5_I2] at hb
  have := countTrue_interval _ t0 _ _ hov (by have := A.H_nonneg; omega) n
  omega

end Handover

/-! ## §2 Probes 7h / 7j (`ArbHeldTimed`, `ArbHeldTimed2`): held bd_arbiter -/

section Held
open ArbHeldTimed ArbHeldTimed2

/-- Routes (ps, each including the site-pin delay of its physical pin, as in
7h's `Dl`) and the server's minimum response `smin` (H_SERVER_MIN). -/
structure Rt where
  wr1s : Int
  wr2s : Int
  wr1g : Int
  wr2g : Int
  wfb : Int
  wa0s : Int
  wq : Int
  wg1 : Int
  wa01 : Int
  wfa1 : Int
  wg2 : Int
  wa02 : Int
  wfa2 : Int
  smin : Int
  H_nonneg : 0 ≤ wr1s ∧ 0 ≤ wr2s ∧ 0 ≤ wr1g ∧ 0 ≤ wr2g ∧ 0 ≤ wfb ∧ 0 ≤ wa0s ∧
    0 ≤ wq ∧ 0 ≤ wg1 ∧ 0 ≤ wa01 ∧ 0 ≤ wfa1 ∧ 0 ≤ wg2 ∧ 0 ≤ wa02 ∧ 0 ≤ wfa2 ∧ 0 ≤ smin

/-- 7h's `Dl` at corner `c` with asymmetry `r` (rise = the corner value,
fall = rise + d) and routes `x`. -/
def cDl (c : Corner) (r : RF) (x : Rt) : Dl where
  wr1s := x.wr1s
  wr2s := x.wr2s
  wr1g := x.wr1g
  wr2g := x.wr2g
  wfb := x.wfb
  wa0s := x.wa0s
  wq := x.wq
  wg1 := x.wg1
  wa01 := x.wa01
  wfa1 := x.wfa1
  wg2 := x.wg2
  wa02 := x.wa02
  wfa2 := x.wfa2
  qr := c.o6
  qf := c.o6 + r.d6
  Rr1 := c.o5a
  Rf1 := c.o5a + r.d5a
  Rr2 := c.o5a
  Rf2 := c.o5a + r.d5a
  Rrq := c.o5q
  Rfq := c.o5q + r.d5q
  g1r1 := c.o5a
  g1f1 := c.o5a + r.d5a
  g1r2 := c.o5a
  g1f2 := c.o5a + r.d5a
  g1rq := c.o5q
  g1fq := c.o5q + r.d5q
  g2r := c.o6
  g2f := c.o6 + r.d6
  c1r := c.o6
  c1f := c.o6 + r.d6
  c2r := c.o6
  c2f := c.o6 + r.d6
  smin := x.smin
  H_NONNEG := by have := c.H_pos; have := x.H_nonneg; omega
  H_RISE_LE_FALL := by have := r.H_nonneg; omega
  H_LOOP_POS := by have := c.H_pos; have := x.H_nonneg; omega

/-- **The old instance is the corner mix.** 7h's `prj` (used by 7h and 7j) is
`cDl` at rise = FAST_MAX with the fast-to-slow spread as "fall − rise". -/
theorem prj_is_mix (x : Rt) :
    prj x.wr1s x.wr2s x.wr1g x.wr2g x.wfb x.wa0s x.wq x.wg1 x.wa01 x.wfa1 x.wg2 x.wa02 x.wfa2
      x.smin x.H_nonneg = cDl mixRise mixRF x := rfl

/-! ### Margins: each arc condition is `0 ≤ m D`, and `m = arc part + wire part` -/

/-- 7h RT1 (race disjunct), RHS − LHS. -/
def mRT1 (D : Dl) : Int := D.wr1s + D.Rf1 + D.smin + D.wa0s + D.qf + D.wq + D.g2r - (D.wr1g + D.g1f1)
/-- 7h RT1 (structural disjunct `g1fq ≤ g2r`). -/
def mRT1s (D : Dl) : Int := D.g2r - D.g1fq
def mPulse (D : Dl) : Int := D.wa0s + D.qf + D.wfb + D.Rrq + D.smin - (D.c1f + D.wfa1)
def mG1 (D : Dl) : Int := D.wr1s + D.Rf1 + 2 * D.smin + D.wa0s + D.qf + D.wfb + D.Rrq + D.wa01 -
  (D.wr1g + D.g1f1 + D.wg1 + D.c1f + D.wfa1)
def mForkA (D : Dl) : Int := D.wa0s + D.qf + D.wfb + D.Rrq + D.smin + D.wa02 + D.c2r - (D.wa01 + D.c1f)
def mForkG (D : Dl) : Int := D.wr1s + D.Rf1 + 2 * D.smin + D.wa0s + D.qf + D.wfb + D.Rrq + D.wa02 +
  D.c2r - (D.wr1g + D.g1f1 + D.wg1 + D.c1f)
def mFork (D : Dl) : Int := D.wa0s + D.qf + D.wq + D.g2r + D.wg2 - D.wa02
/-- 7j RT1b (race disjunct) and its structural disjunct `g2f ≤ g1rq`. -/
def mRT1b (D : Dl) : Int := D.wr2s + D.Rf2 + D.smin + D.wa0s + D.qr + D.wq + D.g1rq - (D.wr2g + D.g2f)
def mRT1bs (D : Dl) : Int := D.g1rq - D.g2f
def mPulse2 (D : Dl) : Int := D.wa0s + D.qr + D.wfb + D.Rrq + D.smin - (D.c2f + D.wfa2)
def mG2 (D : Dl) : Int := D.wr2s + D.Rf2 + 2 * D.smin + D.wa0s + D.qr + D.wfb + D.Rrq + D.wa02 -
  (D.wr2g + D.g2f + D.wg2 + D.c2f + D.wfa2)
def mForkA2 (D : Dl) : Int := D.wa0s + D.qr + D.wfb + D.Rrq + D.smin + D.wa01 + D.c1r - (D.wa02 + D.c2f)
def mForkG2 (D : Dl) : Int := D.wr2s + D.Rf2 + 2 * D.smin + D.wa0s + D.qr + D.wfb + D.Rrq + D.wa01 +
  D.c1r - (D.wr2g + D.g2f + D.wg2 + D.c2f)
def mFork2 (D : Dl) : Int := D.wa0s + D.qr + D.wq + D.g1rq + D.wg1 - D.wa01

theorem RT1_iff (D : Dl) : RT1 D ↔ (0 ≤ mRT1 D ∨ 0 ≤ mRT1s D) := by
  unfold RT1 mRT1 mRT1s; omega
theorem RT2_iff (D : Dl) : RT2 D ↔
    (0 ≤ mPulse D ∧ 0 ≤ mG1 D ∧ 0 ≤ mForkA D ∧ 0 ≤ mForkG D) := by
  unfold mPulse mG1 mForkA mForkG
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; omega
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨by omega, by omega, by omega, by omega⟩
theorem A0Fork_iff (D : Dl) : A0Fork D ↔ 0 ≤ mFork D := by unfold A0Fork mFork; omega
theorem RT1b_iff (D : Dl) : RT1b D ↔ (0 ≤ mRT1b D ∨ 0 ≤ mRT1bs D) := by
  unfold RT1b mRT1b mRT1bs; omega
theorem RT2b_iff (D : Dl) : RT2b D ↔
    (0 ≤ mPulse2 D ∧ 0 ≤ mG2 D ∧ 0 ≤ mForkA2 D ∧ 0 ≤ mForkG2 D) := by
  unfold mPulse2 mG2 mForkA2 mForkG2
  constructor
  · rintro ⟨h1, h2, h3, h4⟩; omega
  · rintro ⟨h1, h2, h3, h4⟩; exact ⟨by omega, by omega, by omega, by omega⟩
theorem A0Fork2_iff (D : Dl) : A0Fork2 D ↔ 0 ≤ mFork2 D := by unfold A0Fork2 mFork2; omega

/-! Wire parts (corner-independent route/server sums, signed). -/
def wRT1 (x : Rt) : Int := x.smin + x.wa0s + x.wq + x.wr1s - x.wr1g
def wPulse (x : Rt) : Int := x.smin + x.wa0s + x.wfb - x.wfa1
def wG1 (x : Rt) : Int := 2 * x.smin + x.wa0s + x.wfb + x.wa01 + x.wr1s - x.wr1g - x.wg1 - x.wfa1
def wForkA (x : Rt) : Int := x.smin + x.wa0s + x.wfb + x.wa02 - x.wa01
def wForkG (x : Rt) : Int := 2 * x.smin + x.wa0s + x.wfb + x.wa02 + x.wr1s - x.wr1g - x.wg1
def wFork (x : Rt) : Int := x.wa0s + x.wq + x.wg2 - x.wa02
def wRT1b (x : Rt) : Int := x.smin + x.wa0s + x.wq + x.wr2s - x.wr2g
def wPulse2 (x : Rt) : Int := x.smin + x.wa0s + x.wfb - x.wfa2
def wG2 (x : Rt) : Int := 2 * x.smin + x.wa0s + x.wfb + x.wa02 + x.wr2s - x.wr2g - x.wg2 - x.wfa2
def wForkA2 (x : Rt) : Int := x.smin + x.wa0s + x.wfb + x.wa01 - x.wa02
def wForkG2 (x : Rt) : Int := 2 * x.smin + x.wa0s + x.wfb + x.wa01 + x.wr2s - x.wr2g - x.wg2
def wFork2 (x : Rt) : Int := x.wa0s + x.wq + x.wg1 - x.wa01

/-- **Arc parts of every condition, at any corner with any asymmetry.**
Each margin of 7h/7j is `arc part + wire part`. With the corner mix
(`mixRise`, `mixRF`) these give back 7h/7j's `prj_*` constants (180, 52, 52,
108, 108, 180; 136, −16, 12, 40, 68, 108). -/
theorem decomp (c : Corner) (r : RF) (x : Rt) :
    mRT1 (cDl c r x) = (2 * c.o6 + r.d6) + wRT1 x ∧
    mRT1s (cDl c r x) = c.o6 - c.o5q - r.d5q ∧
    mPulse (cDl c r x) = c.o5q + wPulse x ∧
    mG1 (cDl c r x) = c.o5q + wG1 x ∧
    mForkA (cDl c r x) = (c.o6 + c.o5q) + wForkA x ∧
    mForkG (cDl c r x) = (c.o6 + c.o5q) + wForkG x ∧
    mFork (cDl c r x) = (2 * c.o6 + r.d6) + wFork x ∧
    mRT1b (cDl c r x) = (c.o5a + c.o5q + r.d5a - r.d6) + wRT1b x ∧
    mRT1bs (cDl c r x) = c.o5q - c.o6 - r.d6 ∧
    mPulse2 (cDl c r x) = (c.o5q - r.d6) + wPulse2 x ∧
    mG2 (cDl c r x) = (c.o5a + c.o5q - c.o6 + r.d5a - 2 * r.d6) + wG2 x ∧
    mForkA2 (cDl c r x) = (c.o6 + c.o5q - r.d6) + wForkA2 x ∧
    mForkG2 (cDl c r x) = (c.o5a + c.o5q + r.d5a - 2 * r.d6) + wForkG2 x ∧
    mFork2 (cDl c r x) = (c.o6 + c.o5q) + wFork2 x := by
  simp only [mRT1, mRT1s, mPulse, mG1, mForkA, mForkG, mFork, mRT1b, mRT1bs, mPulse2, mG2,
    mForkA2, mForkG2, mFork2, wRT1, wPulse, wG1, wForkA, wForkG, wFork, wRT1b, wPulse2, wG2,
    wForkA2, wForkG2, wFork2, cDl]
  omega

/-- The old constants are recovered exactly from the corner mix (sanity check
that `decomp` reads the conditions the same way 7h/7j did). -/
theorem mix_constants :
    2 * mixRise.o6 + mixRF.d6 = 180 ∧ mixRise.o5q = 52 ∧ mixRise.o6 + mixRise.o5q = 108 ∧
    mixRise.o5a + mixRise.o5q + mixRF.d5a - mixRF.d6 = 136 ∧ mixRise.o5q - mixRF.d6 = -16 ∧
    mixRise.o5a + mixRise.o5q - mixRise.o6 + mixRF.d5a - 2 * mixRF.d6 = 12 ∧
    mixRise.o6 + mixRise.o5q - mixRF.d6 = 40 ∧
    mixRise.o5a + mixRise.o5q + mixRF.d5a - 2 * mixRF.d6 = 68 := by decide

/-- **Corrected arc parts, SLOW_MAX (rise = fall).** RT1 248, RT1-structural −26,
pulse 150, g1 150, forkA 274, forkG 274, fork 248; RT1b 302,
RT1b-structural +26 (so RT1b holds STRUCTURALLY at SLOW_MAX), pulse2 150
(was −16), g2 178, forkA2 274, forkG2 302, fork2 274. -/
theorem arcs_slowMax :
    2 * slowMax.o6 + RF.sym.d6 = 248 ∧ slowMax.o6 - slowMax.o5q - RF.sym.d5q = -26 ∧
    slowMax.o5q = 150 ∧ slowMax.o6 + slowMax.o5q = 274 ∧
    slowMax.o5a + slowMax.o5q + RF.sym.d5a - RF.sym.d6 = 302 ∧
    slowMax.o5q - slowMax.o6 - RF.sym.d6 = 26 ∧ slowMax.o5q - RF.sym.d6 = 150 ∧
    slowMax.o5a + slowMax.o5q - slowMax.o6 + RF.sym.d5a - 2 * RF.sym.d6 = 178 ∧
    slowMax.o6 + slowMax.o5q - RF.sym.d6 = 274 ∧
    slowMax.o5a + slowMax.o5q + RF.sym.d5a - 2 * RF.sym.d6 = 302 := by decide

/-- **Corrected arc parts, FAST_MIN (rise = fall).** RT1 90, RT1-structural +3
(so RT1 holds STRUCTURALLY at FAST_MIN), pulse 42, g1 42, forkA 87, forkG 87,
fork 90; RT1b 86, RT1b-structural −3, pulse2 42, g2 41, forkA2 87,
forkG2 86, fork2 87. -/
theorem arcs_fastMin :
    2 * fastMin.o6 + RF.sym.d6 = 90 ∧ fastMin.o6 - fastMin.o5q - RF.sym.d5q = 3 ∧
    fastMin.o5q = 42 ∧ fastMin.o6 + fastMin.o5q = 87 ∧
    fastMin.o5a + fastMin.o5q + RF.sym.d5a - RF.sym.d6 = 86 ∧
    fastMin.o5q - fastMin.o6 - RF.sym.d6 = -3 ∧ fastMin.o5q - RF.sym.d6 = 42 ∧
    fastMin.o5a + fastMin.o5q - fastMin.o6 + RF.sym.d5a - 2 * RF.sym.d6 = 41 ∧
    fastMin.o6 + fastMin.o5q - RF.sym.d6 = 87 ∧
    fastMin.o5a + fastMin.o5q + RF.sym.d5a - 2 * RF.sym.d6 = 86 := by decide

/-- Zero routing, server `smin`. -/
def x0 (smin : Int) (h : 0 ≤ smin) : Rt := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, smin, by omega⟩

/-- **Corrected `prj_pulse2_tight`**: at zero routing the mirror pulse condition
holds iff `smin ≥ d6 − o5q`; at every consistent corner (`d6 = 0`) that is
every `smin ≥ 0`, i.e. the "wfa2 + 16" tightest margin does not exist. -/
theorem pulse2_zero_routing (c : Corner) (r : RF) (smin : Int) (h : 0 ≤ smin) :
    0 ≤ mPulse2 (cDl c r (x0 smin h)) ↔ r.d6 - c.o5q ≤ smin := by
  rw [(decomp c r _).2.2.2.2.2.2.2.2.2.1]; simp only [wPulse2, x0]; omega

/-- Arc-only (every route 0) with the hw server `bd_delay #(SLEN=2)` taken as
two LUT1 arcs AT THE SAME CORNER (`smin = 2·o6`): 248 ps at SLOW_MAX,
90 ps at FAST_MIN (7h/7j used 112 = 2 × FAST_MAX). -/
def Dslow : Dl := cDl slowMax RF.sym (x0 248 (by decide))
def Dfast : Dl := cDl fastMin RF.sym (x0 90 (by decide))

/-- **Corrected `prj_arc_only` / `prj_arc_only2`, SLOW_MAX**, with exact margins:
RT1 496, pulse 398, g1 646, forkA 522, forkG 770, fork 248;
RT1b 550, pulse2 398, g2 674, forkA2 522, forkG2 798, fork2 274. -/
theorem slow_arc_only :
    mRT1 Dslow = 496 ∧ mPulse Dslow = 398 ∧ mG1 Dslow = 646 ∧ mForkA Dslow = 522 ∧
    mForkG Dslow = 770 ∧ mFork Dslow = 248 ∧
    mRT1b Dslow = 550 ∧ mPulse2 Dslow = 398 ∧ mG2 Dslow = 674 ∧ mForkA2 Dslow = 522 ∧
    mForkG2 Dslow = 798 ∧ mFork2 Dslow = 274 := by
  simp only [Dslow, mRT1, mPulse, mG1, mForkA, mForkG, mFork, mRT1b, mPulse2, mG2, mForkA2,
    mForkG2, mFork2, cDl, x0, slowMax, Corner.of, RF.sym, O6, O5_I0, O5_I2]
  omega

/-- **Corrected arc-only margins, FAST_MIN**: RT1 180, pulse 132, g1 222,
forkA 177, forkG 267, fork 90; RT1b 176, pulse2 132, g2 221, forkA2 177,
forkG2 266, fork2 87. -/
theorem fast_arc_only :
    mRT1 Dfast = 180 ∧ mPulse Dfast = 132 ∧ mG1 Dfast = 222 ∧ mForkA Dfast = 177 ∧
    mForkG Dfast = 267 ∧ mFork Dfast = 90 ∧
    mRT1b Dfast = 176 ∧ mPulse2 Dfast = 132 ∧ mG2 Dfast = 221 ∧ mForkA2 Dfast = 177 ∧
    mForkG2 Dfast = 266 ∧ mFork2 Dfast = 87 := by
  simp only [Dfast, mRT1, mPulse, mG1, mForkA, mForkG, mFork, mRT1b, mPulse2, mG2, mForkA2,
    mForkG2, mFork2, cDl, x0, fastMin, Corner.of, RF.sym, O6, O5_I0, O5_I2]
  omega

theorem slow_all : RT1 Dslow ∧ RT2 Dslow ∧ A0Fork Dslow ∧ RT1b Dslow ∧ RT2b Dslow ∧ A0Fork2 Dslow := by
  have h := slow_arc_only
  rw [RT1_iff, RT2_iff, A0Fork_iff, RT1b_iff, RT2b_iff, A0Fork2_iff]
  omega

theorem fast_all : RT1 Dfast ∧ RT2 Dfast ∧ A0Fork Dfast ∧ RT1b Dfast ∧ RT2b Dfast ∧ A0Fork2 Dfast := by
  have h := fast_arc_only
  rw [RT1_iff, RT2_iff, A0Fork_iff, RT1b_iff, RT2b_iff, A0Fork2_iff]
  omega

/-- **Consistent corner, any routing: the reduced conditions.** At any corner
with rise = fall the conditions of 7h and 7j are exactly
`0 ≤ arc part + wire part` with the arc parts of `decomp` (`RF.sym`). -/
theorem corner_conditions (c : Corner) (r : RF) (hr : r.d6 = 0 ∧ r.d5a = 0 ∧ r.d5q = 0) (x : Rt) :
    (RT1 (cDl c r x) ↔ (0 ≤ 2 * c.o6 + wRT1 x ∨ c.o5q ≤ c.o6)) ∧
    (RT2 (cDl c r x) ↔ (0 ≤ c.o5q + wPulse x ∧ 0 ≤ c.o5q + wG1 x ∧
       0 ≤ c.o6 + c.o5q + wForkA x ∧ 0 ≤ c.o6 + c.o5q + wForkG x)) ∧
    (A0Fork (cDl c r x) ↔ 0 ≤ 2 * c.o6 + wFork x) ∧
    (RT1b (cDl c r x) ↔ (0 ≤ c.o5a + c.o5q + wRT1b x ∨ c.o6 ≤ c.o5q)) ∧
    (RT2b (cDl c r x) ↔ (0 ≤ c.o5q + wPulse2 x ∧ 0 ≤ c.o5a + c.o5q - c.o6 + wG2 x ∧
       0 ≤ c.o6 + c.o5q + wForkA2 x ∧ 0 ≤ c.o5a + c.o5q + wForkG2 x)) ∧
    (A0Fork2 (cDl c r x) ↔ 0 ≤ c.o6 + c.o5q + wFork2 x) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14⟩ := decomp c r x
  simp only [RT1_iff, RT2_iff, A0Fork_iff, RT1b_iff, RT2b_iff, A0Fork2_iff, d1, d2, d3, d4, d5, d6,
    d7, d8, d9, d10, d11, d12, d13, d14]
  obtain ⟨e1, e2, e3⟩ := hr
  simp only [e1, e2, e3, Int.add_zero, Int.sub_zero, Int.mul_zero, Int.sub_nonneg, and_self]

/-! ### The box for 7h / 7j: every arc independently in [FAST_MIN, SLOW_MAX] -/

/-- H_DELAY_BOX for 7h/7j: rise = fall per arc (H_RF_ASYM excluded) and each
arc anywhere in its prjxray interval, independently of every other arc. (No
single condition contains both the rise and the fall of one arc, so the box
worst cases below are the same without the rise = fall coupling.) -/
def InBoxD (D : Dl) : Prop :=
  D.qr = D.qf ∧ D.Rr1 = D.Rf1 ∧ D.Rr2 = D.Rf2 ∧ D.Rrq = D.Rfq ∧ D.g1r1 = D.g1f1 ∧
  D.g1r2 = D.g1f2 ∧ D.g1rq = D.g1fq ∧ D.g2r = D.g2f ∧ D.c1r = D.c1f ∧ D.c2r = D.c2f ∧
  45 ≤ D.qr ∧ D.qr ≤ 124 ∧ 45 ≤ D.g2r ∧ D.g2r ≤ 124 ∧ 45 ≤ D.c1r ∧ D.c1r ≤ 124 ∧
  45 ≤ D.c2r ∧ D.c2r ≤ 124 ∧
  44 ≤ D.Rr1 ∧ D.Rr1 ≤ 152 ∧ 44 ≤ D.Rr2 ∧ D.Rr2 ≤ 152 ∧ 44 ≤ D.g1r1 ∧ D.g1r1 ≤ 152 ∧
  44 ≤ D.g1r2 ∧ D.g1r2 ≤ 152 ∧ 42 ≤ D.Rrq ∧ D.Rrq ≤ 150 ∧ 42 ≤ D.g1rq ∧ D.g1rq ≤ 150

/-- The box bounds are prjxray's FAST_MIN / SLOW_MAX columns. -/
theorem InBoxD_bounds : O6.fmin = 45 ∧ O6.smax = 124 ∧ O5_I0.fmin = 44 ∧ O5_I0.smax = 152 ∧
    O5_I2.fmin = 42 ∧ O5_I2.smax = 150 := by decide

/-- The box worst corner of 7h (client 1 releases). -/
def Dw7h (x : Rt) : Dl where
  wr1s := x.wr1s
  wr2s := x.wr2s
  wr1g := x.wr1g
  wr2g := x.wr2g
  wfb := x.wfb
  wa0s := x.wa0s
  wq := x.wq
  wg1 := x.wg1
  wa01 := x.wa01
  wfa1 := x.wfa1
  wg2 := x.wg2
  wa02 := x.wa02
  wfa2 := x.wfa2
  qr := 45
  qf := 45
  Rr1 := 44
  Rf1 := 44
  Rr2 := 44
  Rf2 := 44
  Rrq := 42
  Rfq := 42
  g1r1 := 152
  g1f1 := 152
  g1r2 := 44
  g1f2 := 44
  g1rq := 150
  g1fq := 150
  g2r := 45
  g2f := 45
  c1r := 124
  c1f := 124
  c2r := 45
  c2f := 45
  smin := x.smin
  H_NONNEG := by have := x.H_nonneg; omega
  H_RISE_LE_FALL := by omega
  H_LOOP_POS := by have := x.H_nonneg; omega

/-- The box worst corner of 7j (client 2 releases). -/
def Dw7j (x : Rt) : Dl where
  wr1s := x.wr1s
  wr2s := x.wr2s
  wr1g := x.wr1g
  wr2g := x.wr2g
  wfb := x.wfb
  wa0s := x.wa0s
  wq := x.wq
  wg1 := x.wg1
  wa01 := x.wa01
  wfa1 := x.wfa1
  wg2 := x.wg2
  wa02 := x.wa02
  wfa2 := x.wfa2
  qr := 45
  qf := 45
  Rr1 := 44
  Rf1 := 44
  Rr2 := 44
  Rf2 := 44
  Rrq := 42
  Rfq := 42
  g1r1 := 44
  g1f1 := 44
  g1r2 := 44
  g1f2 := 44
  g1rq := 42
  g1fq := 42
  g2r := 124
  g2f := 124
  c1r := 45
  c1f := 45
  c2r := 124
  c2f := 124
  smin := x.smin
  H_NONNEG := by have := x.H_nonneg; omega
  H_RISE_LE_FALL := by omega
  H_LOOP_POS := by have := x.H_nonneg; omega

theorem Dw7h_inBox (x : Rt) : InBoxD (Dw7h x) := by simp [InBoxD, Dw7h]
theorem Dw7j_inBox (x : Rt) : InBoxD (Dw7j x) := by simp [InBoxD, Dw7j]

/-- Routes of a `Dl`, as an `Rt` (to state the box over arbitrary `Dl`). -/
def rtOf (D : Dl) : Rt := ⟨D.wr1s, D.wr2s, D.wr1g, D.wr2g, D.wfb, D.wa0s, D.wq, D.wg1, D.wa01,
  D.wfa1, D.wg2, D.wa02, D.wfa2, D.smin, by have := D.H_NONNEG; omega⟩

/-- **Box, 7h direction: every margin is at least its worst-corner value**:
RT1 −18, pulse −37, g1 −145, forkA +8, forkG −100, fork +90 (plus the wire part).
So for any arcs in the box, RT1 ∧ RT2 ∧ A0Fork hold if the routing satisfies
these six inequalities. -/
theorem box_7h (D : Dl) (hb : InBoxD D) :
    -18 + wRT1 (rtOf D) ≤ mRT1 D ∧ -37 + wPulse (rtOf D) ≤ mPulse D ∧ -145 + wG1 (rtOf D) ≤ mG1 D ∧
    8 + wForkA (rtOf D) ≤ mForkA D ∧ -100 + wForkG (rtOf D) ≤ mForkG D ∧ 90 + wFork (rtOf D) ≤ mFork D := by
  unfold InBoxD at hb
  simp only [mRT1, mPulse, mG1, mForkA, mForkG, mFork, wRT1, wPulse, wG1, wForkA, wForkG, wFork,
    rtOf]
  omega

/-- ... and the bounds are attained at `Dw7h` (which is in the box), where the
conditions are EXACTLY these routing inequalities. -/
theorem box_7h_worst (x : Rt) :
    (RT1 (Dw7h x) ↔ 18 ≤ wRT1 x) ∧
    (RT2 (Dw7h x) ↔ (37 ≤ wPulse x ∧ 145 ≤ wG1 x ∧ -8 ≤ wForkA x ∧ 100 ≤ wForkG x)) ∧
    (A0Fork (Dw7h x) ↔ -90 ≤ wFork x) := by
  rw [RT1_iff, RT2_iff, A0Fork_iff]
  simp only [mRT1, mRT1s, mPulse, mG1, mForkA, mForkG, mFork, wRT1, wPulse, wG1, wForkA, wForkG,
    wFork, Dw7h]
  omega

/-- **Box, 7j direction**: RT1b +7, pulse2 −37, g2 −117, forkA2 +8, forkG2 −72,
fork2 +87 (plus the wire part). -/
theorem box_7j (D : Dl) (hb : InBoxD D) :
    7 + wRT1b (rtOf D) ≤ mRT1b D ∧ -37 + wPulse2 (rtOf D) ≤ mPulse2 D ∧ -117 + wG2 (rtOf D) ≤ mG2 D ∧
    8 + wForkA2 (rtOf D) ≤ mForkA2 D ∧ -72 + wForkG2 (rtOf D) ≤ mForkG2 D ∧
    87 + wFork2 (rtOf D) ≤ mFork2 D := by
  unfold InBoxD at hb
  simp only [mRT1b, mPulse2, mG2, mForkA2, mForkG2, mFork2, wRT1b, wPulse2, wG2, wForkA2,
    wForkG2, wFork2, rtOf]
  omega

theorem box_7j_worst (x : Rt) :
    (RT1b (Dw7j x) ↔ -7 ≤ wRT1b x) ∧
    (RT2b (Dw7j x) ↔ (37 ≤ wPulse2 x ∧ 117 ≤ wG2 x ∧ -8 ≤ wForkA2 x ∧ 72 ≤ wForkG2 x)) ∧
    (A0Fork2 (Dw7j x) ↔ -87 ≤ wFork2 x) := by
  rw [RT1b_iff, RT2b_iff, A0Fork2_iff]
  simp only [mRT1b, mRT1bs, mPulse2, mG2, mForkA2, mForkG2, mFork2, wRT1b, wPulse2, wG2,
    wForkA2, wForkG2, wFork2, Dw7j]
  omega

/-- Box at zero routing with the fastest box server (`smin = 90`): every
condition still holds (margins RT1 72, pulse 53, g1 35, forkA 98, forkG 80,
fork 90; RT1b 97, pulse2 53, g2 63, forkA2 98, forkG2 108, fork2 87). -/
theorem box_arc_only :
    wRT1 (x0 90 (by decide)) - 18 = 72 ∧ wPulse (x0 90 (by decide)) - 37 = 53 ∧
    wG1 (x0 90 (by decide)) - 145 = 35 ∧ wForkA (x0 90 (by decide)) + 8 = 98 ∧
    wForkG (x0 90 (by decide)) - 100 = 80 ∧ wFork (x0 90 (by decide)) + 90 = 90 ∧
    wRT1b (x0 90 (by decide)) + 7 = 97 ∧ wPulse2 (x0 90 (by decide)) - 37 = 53 ∧
    wG2 (x0 90 (by decide)) - 117 = 63 ∧ wForkA2 (x0 90 (by decide)) + 8 = 98 ∧
    wForkG2 (x0 90 (by decide)) - 72 = 108 ∧ wFork2 (x0 90 (by decide)) + 87 = 87 := by
  simp only [wRT1, wPulse, wG1, wForkA, wForkG, wFork, wRT1b, wPulse2, wG2, wForkA2, wForkG2,
    wFork2, x0]
  decide

/-! ### The runt band of 7j at a consistent corner -/

section Runt
variable {D : Dl} {s : Sigs} {t0 ta TA TA2 Hz : Int}

/-- **With rise = fall on ua1 (`c1r = c1f`), `A1_stuck`'s pulse disjunct is
vacuous**: A1 can stay stuck only through a late g1, never through a short A0
pulse. (7j's "68 < p" lower edge is `c1f − c1r` of the corner mix.) -/
theorem stuck_pulse_vacuous (S : Scn D s t0 ta TA TA2 Hz) (h : D.c1r = D.c1f) :
    ¬ (TA2 + D.wa01 ≤ TA + D.wa01 + D.c1f - D.c1r) := by
  have := S.H_ORDER; omega

/-- **The runt band at a consistent corner is `0 < p < c1f + wfa1`.** With
`c1r = c1f`, g1 early, and A0's low pulse `p = TA2 − TA` shorter than ua1's
fall loop, A1 makes a low runt and re-latches high. -/
theorem A1_band_corner (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz) (h : D.c1r = D.c1f)
    (H_g1early : G1 D t0 TA + D.wg1 ≤ TA + D.wa01)
    (H_hi : TA2 - TA < D.c1f + D.wfa1) (hz : TA2 + D.wa01 + D.c1r < Hz) :
    s.A1 (T1 D t0 TA - 1) = true ∧ s.A1 (T1 D t0 TA) = false ∧
      s.A1 (TA2 + D.wa01 + D.c1r) = true :=
  A1_band R S H_g1early (by have := S.H_ORDER; omega) H_hi hz

/-- Under H_RF_ASYM with `c1f − c1r = δ ≥ 0` the band is `δ < p < c1f + wfa1`. -/
theorem A1_band_asym (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz) (δ : Int)
    (hδ : D.c1f - D.c1r = δ)
    (H_g1early : G1 D t0 TA + D.wg1 ≤ TA + D.wa01)
    (H_lo : δ < TA2 - TA) (H_hi : TA2 - TA < D.c1f + D.wfa1) (hz : TA2 + D.wa01 + D.c1r < Hz) :
    s.A1 (T1 D t0 TA - 1) = true ∧ s.A1 (T1 D t0 TA) = false ∧
      s.A1 (TA2 + D.wa01 + D.c1r) = true :=
  A1_band R S H_g1early (by omega) H_hi hz

end Runt

end Held

/-! ## §3 Corner sign changes: cells and wires scale differently

Between SLOW_MAX and FAST_MIN a LUT arc scales by `Af / As` (O6 0.363,
O5 0.28–0.29), but routing scales by a different ratio `k` (f1_compare on gcd:
median 0.55, p10 0.37, p90 0.82). Every margin above is
`m = (arc part) + (wire part)`. Write `As`, `Af` for the arc part at SLOW_MAX
and FAST_MIN (from `decomp`) and `W` for the wire part at SLOW_MAX; the wire
part at FAST_MIN is `Wf` with

    H_WIRE_RATIO :  kd · Wf = kn · W        (k = kn / kd > 0),

a single common ratio for the signed wire sum of that margin. (Per-wire
scatter of the ratio is the box of §1/§2 applied to wires; not done here.)
The theorems below give the EXACT routing window where the sign changes. -/

section Flip
open ArbHeldTimed ArbHeldTimed2

theorem mul_pos_neg_iff {k y : Int} (hk : 0 < k) : k * y < 0 ↔ y < 0 := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hy
    have := Int.mul_nonneg (Int.le_of_lt hk) (Int.not_lt.mp hy)
    omega
  · intro h; exact Int.mul_neg_of_pos_of_neg hk h

/-- **The flip that the post-route rules cannot see** (they all read SLOW_MAX):
the margin is non-negative at SLOW_MAX and negative at FAST_MIN iff the
SLOW_MAX wire part lies in `[−As, −(kd·Af)/kn)`. -/
theorem flip_iff (As Af W Wf kn kd : Int) (hkd : 0 < kd) (H : kd * Wf = kn * W) :
    (0 ≤ As + W ∧ Af + Wf < 0) ↔ (-As ≤ W ∧ kn * W < -(kd * Af)) := by
  have e : kd * (Af + Wf) = kd * Af + kn * W := by rw [Int.mul_add, H]
  have := @mul_pos_neg_iff kd (Af + Wf) hkd
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩

/-- The opposite flip (safe at FAST_MIN, unsafe at SLOW_MAX): `W` in
`[−(kd·Af)/kn, −As)`. -/
theorem flip_iff' (As Af W Wf kn kd : Int) (hkd : 0 < kd) (H : kd * Wf = kn * W) :
    (As + W < 0 ∧ 0 ≤ Af + Wf) ↔ (W < -As ∧ -(kd * Af) ≤ kn * W) := by
  have e : kd * (Af + Wf) = kd * Af + kn * W := by rw [Int.mul_add, H]
  have := @mul_pos_neg_iff kd (Af + Wf) hkd
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, by omega⟩

/-- **The window is non-empty iff cells scale more than wires**: a routing with
SLOW_MAX safe / FAST_MIN unsafe exists iff `Af / As < k` (`kd·Af < kn·As`). -/
theorem flip_exists (As Af kn kd : Int) (hkn : 0 ≤ kn) :
    (∃ W : Int, -As ≤ W ∧ kn * W < -(kd * Af)) ↔ kd * Af < kn * As := by
  constructor
  · rintro ⟨W, h1, h2⟩
    have := Int.mul_le_mul_of_nonneg_left h1 hkn
    rw [Int.mul_neg] at this
    omega
  · intro h
    refine ⟨-As, Int.le_refl _, ?_⟩
    rw [Int.mul_neg]; omega

/-- **In slow-margin terms**: with `M = As + W` the SLOW_MAX margin, the
FAST_MIN margin is negative iff `kn·M < kn·As − kd·Af`, i.e. iff
`M < As − Af / k`. So `As − Af/k` is the guard a SLOW_MAX check must add. -/
theorem fast_neg_iff (As Af W Wf kn kd : Int) (hkd : 0 < kd) (H : kd * Wf = kn * W) :
    Af + Wf < 0 ↔ kn * (As + W) < kn * As - kd * Af := by
  have e : kd * (Af + Wf) = kd * Af + kn * W := by rw [Int.mul_add, H]
  have := @mul_pos_neg_iff kd (Af + Wf) hkd
  rw [Int.mul_add]; omega

/-- **A universal guard**: if wires never get slower at the fast corner
(`k ≤ 1`, H_WIRE_RATIO_LE1) and the fast arc part is non-negative, a SLOW_MAX
margin of at least `As − Af` guarantees a non-negative FAST_MIN margin. -/
theorem guard_universal (As Af W Wf kn kd : Int) (hkd : 0 < kd) (hkn : 0 ≤ kn) (hk : kn ≤ kd)
    (hAf : 0 ≤ Af) (H : kd * Wf = kn * W) (hM : As - Af ≤ As + W) : 0 ≤ Af + Wf := by
  have e : kd * (Af + Wf) = kd * Af + kn * W := by rw [Int.mul_add, H]
  have := @mul_pos_neg_iff kd (Af + Wf) hkd
  by_cases hW : 0 ≤ W
  · have := Int.mul_nonneg hkn hW
    have := Int.mul_nonneg (Int.le_of_lt hkd) hAf
    omega
  · have h1 : kd * W ≤ kn * W := Int.mul_le_mul_of_nonpos_right hk (by omega)
    have h2 : 0 ≤ kd * (Af + W) := Int.mul_nonneg (Int.le_of_lt hkd) (by omega)
    rw [Int.mul_add] at h2
    omega

/-- No flip when every term has a sign: arcs non-negative at both corners and
the wire part non-negative (7e's zero-skew overlap, `w ≥ 0`). -/
theorem no_flip_nonneg (As Af W Wf kn kd : Int) (hkd : 0 < kd) (hkn : 0 ≤ kn)
    (hAs : 0 ≤ As) (hAf : 0 ≤ Af) (hW : 0 ≤ W) (H : kd * Wf = kn * W) :
    0 ≤ As + W ∧ 0 ≤ Af + Wf := by
  have e : kd * (Af + Wf) = kd * Af + kn * W := by rw [Int.mul_add, H]
  have := @mul_pos_neg_iff kd (Af + Wf) hkd
  have := Int.mul_nonneg hkn hW
  have := Int.mul_nonneg (Int.le_of_lt hkd) hAf
  omega

/-! ### Applied to 7h / 7j: the window per condition

For each condition, `As`/`Af` are its arc parts at SLOW_MAX / FAST_MIN
(`arcs_slowMax`, `arcs_fastMin`). Every one has `Af/As ≤ 0.363 < 0.37`, so for
EVERY wire ratio in the measured p10..p90 range the window is non-empty:

| condition | As | Af | Af/As | flip window for the SLOW_MAX margin M, at k |
|---|---|---|---|---|
| RT1, fork (7h) | 248 | 90 | 0.363 | `M < 248 − 90/k`: 84 (k=.55), 5 (.37), 138 (.82) |
| pulse, g1 (7h), pulse2 (7j) | 150 | 42 | 0.280 | 74, 37, 99 |
| forkA, forkG (7h), forkA2, fork2 | 274 | 87 | 0.318 | 116, 39, 168 |
| RT1b, forkG2 (7j) | 302 | 86 | 0.285 | 146, 70, 197 |
| g2 (7j) | 178 | 41 | 0.230 | 103, 67, 128 |

(`M` is in ps at SLOW_MAX; the upper ends for `k ≤ 1` are `As − Af`:
158, 108, 187, 216, 137, `guard_universal`.) With the plausible routing of
7h/7j (smallest margins about 0.47–0.62 ns) all are far outside the window;
the window matters only for a margin already within about 0.2 ns of zero. -/

/-- The window exists for every condition of 7h/7j at the median wire ratio
`k = 55/100`: `kd·Af < kn·As` for each (As, Af) pair. -/
theorem windows_exist_median :
    100 * 90 < 55 * 248 ∧ 100 * 42 < 55 * 150 ∧ 100 * 87 < 55 * 274 ∧
    100 * 86 < 55 * 302 ∧ 100 * 41 < 55 * 178 := by decide

/-- ... and even at the p10 wire ratio `k = 37/100`. -/
theorem windows_exist_p10 :
    100 * 90 < 37 * 248 ∧ 100 * 42 < 37 * 150 ∧ 100 * 87 < 37 * 274 ∧
    100 * 86 < 37 * 302 ∧ 100 * 41 < 37 * 178 := by decide

/-- **Worked instance on the real conditions: the mirror pulse condition (7j),
the old "tightest margin".** For routes `xs` (SLOW_MAX) and `xf` (FAST_MIN)
with H_WIRE_RATIO on its wire part, the condition holds at SLOW_MAX and fails
at FAST_MIN iff `−150 ≤ W ∧ kn·W < −42·kd`. -/
theorem pulse2_flip (xs xf : Rt) (kn kd : Int) (hkd : 0 < kd)
    (H : kd * wPulse2 xf = kn * wPulse2 xs) :
    (0 ≤ mPulse2 (cDl slowMax RF.sym xs) ∧ mPulse2 (cDl fastMin RF.sym xf) < 0) ↔
      (-150 ≤ wPulse2 xs ∧ kn * wPulse2 xs < -(kd * 42)) := by
  rw [(decomp _ _ _).2.2.2.2.2.2.2.2.2.1, (decomp _ _ _).2.2.2.2.2.2.2.2.2.1]
  have := flip_iff 150 42 (wPulse2 xs) (wPulse2 xf) kn kd hkd H
  have e1 : slowMax.o5q - RF.sym.d6 = 150 := by decide
  have e2 : fastMin.o5q - RF.sym.d6 = 42 := by decide
  rw [e1, e2]; exact this

/-- The same for 7h's RT1 race disjunct (`As = 248`, `Af = 90`). At FAST_MIN
RT1 also has its structural disjunct (`g1fq ≤ g2r`, 42 ≤ 45), so RT1 ITSELF
cannot fail at FAST_MIN; the race margin can. -/
theorem rt1_flip (xs xf : Rt) (kn kd : Int) (hkd : 0 < kd)
    (H : kd * wRT1 xf = kn * wRT1 xs) :
    (0 ≤ mRT1 (cDl slowMax RF.sym xs) ∧ mRT1 (cDl fastMin RF.sym xf) < 0) ↔
      (-248 ≤ wRT1 xs ∧ kn * wRT1 xs < -(kd * 90)) := by
  rw [(decomp _ _ _).1, (decomp _ _ _).1]
  have := flip_iff 248 90 (wRT1 xs) (wRT1 xf) kn kd hkd H
  have e1 : 2 * slowMax.o6 + RF.sym.d6 = 248 := by decide
  have e2 : 2 * fastMin.o6 + RF.sym.d6 = 90 := by decide
  rw [e1, e2]; exact this

theorem rt1_fast_structural (x : Rt) : RT1 (cDl fastMin RF.sym x) := by
  rw [RT1_iff]; right
  rw [(decomp _ _ _).2.1]; decide

/-- RT1b is structural at SLOW_MAX (`g2f ≤ g1rq`, 124 ≤ 150), whatever the routing. -/
theorem rt1b_slow_structural (x : Rt) : RT1b (cDl slowMax RF.sym x) := by
  rw [RT1b_iff]; right
  rw [(decomp _ _ _).2.2.2.2.2.2.2.2.1]; decide

/-- ... but not at FAST_MIN (42 < 45): there RT1b is the race condition alone. -/
theorem rt1b_fast_race (x : Rt) :
    RT1b (cDl fastMin RF.sym x) ↔ 0 ≤ mRT1b (cDl fastMin RF.sym x) := by
  rw [RT1b_iff, (decomp _ _ _).2.2.2.2.2.2.2.2.1]
  have : ¬ (0 ≤ fastMin.o5q - fastMin.o6 - RF.sym.d6) := by decide
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h this
  · exact Or.inl

end Flip

/-! ### Applied to rule J (probe 7g), on its run semantics -/

section RuleJ
open ArbA0Fork

/-- The cell-like part of 7g's `early − late` (arcs and site pins). -/
def cellJ (p : ArbA0Fork.Dl) : Int :=
  (p.pSt + p.aSt + p.pQG + p.aG + p.pGC : Nat) - (p.pAC : Nat)
/-- The routed part of 7g's `early − late` (past the shared prefix). -/
def wireJ (p : ArbA0Fork.Dl) : Int := (p.wSt + p.wQG + p.wGC : Nat) - (p.wAC : Nat)

theorem early_late (p : ArbA0Fork.Dl) :
    ((p.early : Nat) : Int) - (p.late : Nat) = cellJ p + wireJ p := by
  unfold ArbA0Fork.Dl.early ArbA0Fork.Dl.late cellJ wireJ; omega

/-- **Rule J's corner flip, on 7g's exact run semantics (client 2).** `ps` is
the delay set at SLOW_MAX, `pf` at FAST_MIN, related by H_WIRE_RATIO on the
routed part. Every SLOW_MAX run is safe while every FAST_MIN run acknowledges
early (7g's `client2_iff`) iff the SLOW_MAX routed part lies in the window
`[−As, −(kd·Af)/kn)`, where `As`, `Af` are the cell parts at the two corners. -/
theorem client2_corner_flip (ps pf : ArbA0Fork.Dl) {T0 T0' : Nat}
    {a0 q g A a0' q' g' A' : Nat → Bool}
    (Rs : ArbA0Fork.Run F2 G2 true ps T0 a0 q g A) (Rf : ArbA0Fork.Run F2 G2 true pf T0' a0' q' g' A')
    (kn kd : Int) (hkd : 0 < kd) (H : kd * wireJ pf = kn * wireJ ps) :
    ((∀ t, A t = false) ∧ ∃ t, A' t = true) ↔
      (-cellJ ps ≤ wireJ ps ∧ kn * wireJ ps < -(kd * cellJ pf)) := by
  rw [client2_iff Rs]
  have hf := client2_iff Rf
  have e1 := early_late ps
  have e2 := early_late pf
  have hx : (∃ t, A' t = true) ↔ pf.early < pf.late := by
    constructor
    · rintro ⟨t, ht⟩
      apply Classical.byContradiction
      intro hc
      have := (hf.2 (by omega)) t
      rw [this] at ht; exact Bool.false_ne_true ht
    · intro hlt
      apply Classical.byContradiction
      intro hc
      have : ∀ t, A' t = false := fun t => by
        cases h : A' t
        · rfl
        · exact absurd ⟨t, h⟩ hc
      have := hf.1 this
      omega
  rw [hx, ← flip_iff (cellJ ps) (cellJ pf) (wireJ ps) (wireJ pf) kn kd hkd H]
  omega

/-- Client 1 (ustate rise + ugrant O5 rise): the same statement. -/
theorem client1_corner_flip (ps pf : ArbA0Fork.Dl) {T0 T0' : Nat}
    {a0 q g A a0' q' g' A' : Nat → Bool}
    (Rs : ArbA0Fork.Run F1 G1 false ps T0 a0 q g A) (Rf : ArbA0Fork.Run F1 G1 false pf T0' a0' q' g' A')
    (kn kd : Int) (hkd : 0 < kd) (H : kd * wireJ pf = kn * wireJ ps) :
    ((∀ t, A t = false) ∧ ∃ t, A' t = true) ↔
      (-cellJ ps ≤ wireJ ps ∧ kn * wireJ ps < -(kd * cellJ pf)) := by
  rw [client1_iff Rs]
  have hf := client1_iff Rf
  have e1 := early_late ps
  have e2 := early_late pf
  have hx : (∃ t, A' t = true) ↔ pf.early < pf.late := by
    constructor
    · rintro ⟨t, ht⟩
      apply Classical.byContradiction
      intro hc
      have := (hf.2 (by omega)) t
      rw [this] at ht; exact Bool.false_ne_true ht
    · intro hlt
      apply Classical.byContradiction
      intro hc
      have : ∀ t, A' t = false := fun t => by
        cases h : A' t
        · rfl
        · exact absurd ⟨t, h⟩ hc
      have := hf.1 this
      omega
  rw [hx, ← flip_iff (cellJ ps) (cellJ pf) (wireJ ps) (wireJ pf) kn kd hkd H]
  omega

/-- The two arcs on rule J's early side, per corner (7g's item 1 corrected):
client 2 = ustate O6 + ugrant O6 = 248 (SLOW_MAX) / 90 (FAST_MIN); client 1
= ustate O6 + ugrant O5 from I2 = 274 / 87. Box: [90, 248] and [87, 274]
(7g quoted 145–180 and 87–117 from the corner mix). Rule J's nextpnr SDF
counts 2 × 124 = 248: exact at SLOW_MAX for client 2, 26 ps conservative for
client 1. -/
theorem ruleJ_arcs :
    O6.smax + O6.smax = 248 ∧ O6.fmin + O6.fmin = 90 ∧
    O6.smax + O5_I2.smax = 274 ∧ O6.fmin + O5_I2.fmin = 87 := by decide

/-- **Guarded rule J also covers the FAST_MIN corner** (site pins excluded, as
in rule J itself). Rule J passes when `0.772·(E + 3·124) > 1.155·(L + 124)`
(`cells/verify/arb_fork.py`; E, L the routed early/late parts past the shared
prefix from the SLOW_MAX SDF, the arcs nextpnr's flat 124). If the early
chain carries at least 114 ps of routing (it always carries two routed hops;
the same-slice hop alone is 295 ps), wires do not slow down at the fast corner
(`k ≤ 1`), and the true fast cell part is at least 87 ps (`ruleJ_arcs`), the
FAST_MIN margin is non-negative. -/
theorem ruleJ_guard_covers_fast (E L Af Wf kn kd : Int) (hkd : 0 < kd) (hkn : 0 ≤ kn)
    (hk : kn ≤ kd) (hE : 114 ≤ E) (hAf : 80 ≤ Af) (H : kd * Wf = kn * (E - L))
    (H_RULEJ : 1155 * (L + 124) < 772 * (E + 372)) : 0 ≤ Af + Wf := by
  apply guard_universal (Af + 0) Af (E - L) Wf kn kd hkd hkn hk (by omega) H
  omega

/-- ... and the same guard implies the SLOW_MAX margin with the true arcs
(at least 248) is non-negative. -/
theorem ruleJ_guard_covers_slow (E L As : Int) (hE : 0 ≤ E) (hAs : 248 ≤ As)
    (H_RULEJ : 1155 * (L + 124) < 772 * (E + 372)) : 0 ≤ As + (E - L) := by omega

/-- The 114 ps premise is needed: with no early routing a guarded pass can
still fail at FAST_MIN with `k = 1` (E = 0, L = 124: guard passes, margin −37). -/
theorem ruleJ_guard_small_E :
    1155 * ((124 : Int) + 124) < 772 * (0 + 372) ∧ (87 : Int) + (0 - 124) < 0 := by decide

/-- **Unguarded (raw-sign) rule J does not cover FAST_MIN**: for client 2 the
window is `0 ≤ M < 248 − 90/k` (84 ps at k = 0.55). B-gls-compare's example:
M = +133 at SLOW_MAX stays +27 at FAST_MIN (k = 0.55, outside the window). -/
theorem ruleJ_raw_window :
    100 * 90 < 55 * 248 ∧
    (100 * (90 : Int) + 55 * (885 - 1000) > 0) ∧ (248 + (885 - 1000 : Int) = 133) := by decide

end RuleJ

/-! ## §4 Non-vacuity at consistent corners (replaces 7j's `nonvacuous`, whose
`D0` is the corner mix)

`Dslow` (SLOW_MAX, routes 0, `smin = 248`) and `Dfast` (FAST_MIN, routes 0,
`smin = 90`) satisfy every condition (`slow_all`, `fast_all`). For each corner
and each direction an explicit step-function run satisfies `Run` for ALL `t`
(server included, answering in exactly `smin`) and `Scn`/`Scn2` for every
horizon past the second server edge. Every edge time below was derived by
hand from 7h/7j's instant formulas (`TR`, `QB`, `RR`, `G1`, `G2`, `T1`, `T2`
and the mirror ones); a wrong value would not check.

SLOW_MAX, 7h direction (`t0 = 0`, `ta = −1000`): TR = 152, TA = 400,
QB = 524, RR = 674, TA2 = 922, G1 = 152, G2 = 648, T1 = 524, T2 = 1046.
SLOW_MAX, mirror: TRb = 152, TA = 400, QBb = 524, RRb = 674, TA2 = 922,
G1b = 674, G2b = 124, T1b = 524, T2b = 1046.
FAST_MIN, 7h direction: TR = 44, TA = 134, QB = 179, RR = 221, TA2 = 311,
G1 = 44, G2 = 224, T1 = 179, T2 = 356. FAST_MIN, mirror: TRb = 44, TA = 134,
QBb = 179, RRb = 221, TA2 = 311, G1b = 221, G2b = 45, T1b = 179, T2b = 356. -/

section Witness
open ArbHeldTimed ArbHeldTimed2

def W1s : Sigs where
  r1 := fun t => decide (t < 0)
  r2 := fun _ => true
  q := fun t => decide (t < 524)
  R0 := fun t => decide (t < 152) || decide (674 ≤ t)
  g1 := fun t => decide (t < 152)
  g2 := fun t => decide (648 ≤ t)
  A0 := fun t => (decide (-1000 ≤ t) && decide (t < 400)) || decide (922 ≤ t)
  A1 := fun t => decide (t < 524)
  A2 := fun t => decide (1046 ≤ t)

def W2s : Sigs where
  r1 := fun _ => true
  r2 := fun t => decide (t < 0)
  q := fun t => decide (524 ≤ t)
  R0 := fun t => decide (t < 152) || decide (674 ≤ t)
  g1 := fun t => decide (674 ≤ t)
  g2 := fun t => decide (t < 124)
  A0 := fun t => (decide (-1000 ≤ t) && decide (t < 400)) || decide (922 ≤ t)
  A1 := fun t => decide (1046 ≤ t)
  A2 := fun t => decide (t < 524)

def W1f : Sigs where
  r1 := fun t => decide (t < 0)
  r2 := fun _ => true
  q := fun t => decide (t < 179)
  R0 := fun t => decide (t < 44) || decide (221 ≤ t)
  g1 := fun t => decide (t < 44)
  g2 := fun t => decide (224 ≤ t)
  A0 := fun t => (decide (-1000 ≤ t) && decide (t < 134)) || decide (311 ≤ t)
  A1 := fun t => decide (t < 179)
  A2 := fun t => decide (356 ≤ t)

def W2f : Sigs where
  r1 := fun _ => true
  r2 := fun t => decide (t < 0)
  q := fun t => decide (179 ≤ t)
  R0 := fun t => decide (t < 44) || decide (221 ≤ t)
  g1 := fun t => decide (221 ≤ t)
  g2 := fun t => decide (t < 45)
  A0 := fun t => (decide (-1000 ≤ t) && decide (t < 134)) || decide (311 ≤ t)
  A1 := fun t => decide (356 ≤ t)
  A2 := fun t => decide (t < 179)

theorem W1s_run : Run Dslow W1s where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [W1s, Dslow, cDl, x0, slowMax, Corner.of, RF.sym, O6, O5_I0, O5_I2, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [W1s, Dslow, cDl, x0, slowMax, Corner.of, RF.sym, O6, O5_I0, O5_I2, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [W1s, Dslow, cDl, x0, slowMax, Corner.of, RF.sym, O6, O5_I0, O5_I2, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [W1s, Dslow, cDl, x0, slowMax, Corner.of, RF.sym, O6, O5_I0, O5_I2, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [W1s, Dslow, cDl, x0, slowMax, Corner.of, RF.sym, O6, O5_I0, O5_I2, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [W1s, Dslow, cDl, x0, slowMax, Corner.of, RF.sym, O6, O5_I0, O5_I2, CE_eq]; omega
  H_SRV := by
    intro t h
    have ht : t = -1000 ∨ t = 400 ∨ t = 922 := by
      exact Classical.byContradiction fun hc => h (by rw [Bool.eq_iff_iff]; simp [W1s]; omega)
    rcases ht with rfl | rfl | rfl
    · exact ⟨-1248, by simp [Dslow, cDl, x0], by simp [W1s], fun v _ _ => by simp [W1s]; omega⟩
    · exact ⟨152, by simp [Dslow, cDl, x0], by simp [W1s], fun v _ _ => by simp [W1s]; omega⟩
    · exact ⟨674, by simp [Dslow, cDl, x0], by simp [W1s], fun v _ _ => by simp [W1s]; omega⟩

theorem W2s_run : Run Dslow W2s where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [W2s, Dslow, cDl, x0, slowMax, Corner.of, RF.sym, O6, O5_I0, O5_I2, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [W2s, Dslow, cDl, x0, slowMax, Corner.of, RF.sym, O6, O5_I0, O5_I2, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [W2s, Dslow, cDl, x0, slowMax, Corner.of, RF.sym, O6, O5_I0, O5_I2, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [W2s, Dslow, cDl, x0, slowMax, Corner.of, RF.sym, O6, O5_I0, O5_I2, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [W2s, Dslow, cDl, x0, slowMax, Corner.of, RF.sym, O6, O5_I0, O5_I2, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [W2s, Dslow, cDl, x0, slowMax, Corner.of, RF.sym, O6, O5_I0, O5_I2, CE_eq]; omega
  H_SRV := by
    intro t h
    have ht : t = -1000 ∨ t = 400 ∨ t = 922 := by
      exact Classical.byContradiction fun hc => h (by rw [Bool.eq_iff_iff]; simp [W2s]; omega)
    rcases ht with rfl | rfl | rfl
    · exact ⟨-1248, by simp [Dslow, cDl, x0], by simp [W2s], fun v _ _ => by simp [W2s]; omega⟩
    · exact ⟨152, by simp [Dslow, cDl, x0], by simp [W2s], fun v _ _ => by simp [W2s]; omega⟩
    · exact ⟨674, by simp [Dslow, cDl, x0], by simp [W2s], fun v _ _ => by simp [W2s]; omega⟩

theorem W1f_run : Run Dfast W1f where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [W1f, Dfast, cDl, x0, fastMin, Corner.of, RF.sym, O6, O5_I0, O5_I2, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [W1f, Dfast, cDl, x0, fastMin, Corner.of, RF.sym, O6, O5_I0, O5_I2, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [W1f, Dfast, cDl, x0, fastMin, Corner.of, RF.sym, O6, O5_I0, O5_I2, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [W1f, Dfast, cDl, x0, fastMin, Corner.of, RF.sym, O6, O5_I0, O5_I2, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [W1f, Dfast, cDl, x0, fastMin, Corner.of, RF.sym, O6, O5_I0, O5_I2, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [W1f, Dfast, cDl, x0, fastMin, Corner.of, RF.sym, O6, O5_I0, O5_I2, CE_eq]; omega
  H_SRV := by
    intro t h
    have ht : t = -1000 ∨ t = 134 ∨ t = 311 := by
      exact Classical.byContradiction fun hc => h (by rw [Bool.eq_iff_iff]; simp [W1f]; omega)
    rcases ht with rfl | rfl | rfl
    · exact ⟨-1090, by simp [Dfast, cDl, x0], by simp [W1f], fun v _ _ => by simp [W1f]; omega⟩
    · exact ⟨44, by simp [Dfast, cDl, x0], by simp [W1f], fun v _ _ => by simp [W1f]; omega⟩
    · exact ⟨221, by simp [Dfast, cDl, x0], by simp [W1f], fun v _ _ => by simp [W1f]; omega⟩

theorem W2f_run : Run Dfast W2f where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [W2f, Dfast, cDl, x0, fastMin, Corner.of, RF.sym, O6, O5_I0, O5_I2, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [W2f, Dfast, cDl, x0, fastMin, Corner.of, RF.sym, O6, O5_I0, O5_I2, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [W2f, Dfast, cDl, x0, fastMin, Corner.of, RF.sym, O6, O5_I0, O5_I2, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [W2f, Dfast, cDl, x0, fastMin, Corner.of, RF.sym, O6, O5_I0, O5_I2, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [W2f, Dfast, cDl, x0, fastMin, Corner.of, RF.sym, O6, O5_I0, O5_I2, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [W2f, Dfast, cDl, x0, fastMin, Corner.of, RF.sym, O6, O5_I0, O5_I2, CE_eq]; omega
  H_SRV := by
    intro t h
    have ht : t = -1000 ∨ t = 134 ∨ t = 311 := by
      exact Classical.byContradiction fun hc => h (by rw [Bool.eq_iff_iff]; simp [W2f]; omega)
    rcases ht with rfl | rfl | rfl
    · exact ⟨-1090, by simp [Dfast, cDl, x0], by simp [W2f], fun v _ _ => by simp [W2f]; omega⟩
    · exact ⟨44, by simp [Dfast, cDl, x0], by simp [W2f], fun v _ _ => by simp [W2f]; omega⟩
    · exact ⟨221, by simp [Dfast, cDl, x0], by simp [W2f], fun v _ _ => by simp [W2f]; omega⟩

theorem W1s_scn (Hz : Int) (hz : 922 < Hz) : Scn Dslow W1s 0 (-1000) 400 922 Hz where
  H_ORDER := by omega
  H_r1 := fun _ _ => rfl
  H_r2 := fun _ _ => rfl
  H_A0 := by intro t h1 _; rw [Bool.eq_iff_iff]; simp [W1s]; omega
  H_A0_prev := by simp [W1s]
  H_q_init := by intro t h; simp [W1s]; omega
  H_A1_init := by intro t h; simp [W1s]; omega
  H_A2_init := by intro t h; simp [W1s]; omega
  H_SETTLED := by simp [Dslow, cDl, x0, slowMax, Corner.of, RF.sym, O6]

theorem W2s_scn (Hz : Int) (hz : 922 < Hz) : Scn2 Dslow W2s 0 (-1000) 400 922 Hz where
  H_ORDER := by omega
  H_r1 := fun _ _ => rfl
  H_r2 := fun _ _ => rfl
  H_A0 := by intro t h1 _; rw [Bool.eq_iff_iff]; simp [W2s]; omega
  H_A0_prev := by simp [W2s]
  H_q_init := by intro t h; simp [W2s]; omega
  H_A1_init := by intro t h; simp [W2s]; omega
  H_A2_init := by intro t h; simp [W2s]; omega
  H_SETTLED := by simp [Dslow, cDl, x0, slowMax, Corner.of, RF.sym, O6]

theorem W1f_scn (Hz : Int) (hz : 311 < Hz) : Scn Dfast W1f 0 (-1000) 134 311 Hz where
  H_ORDER := by omega
  H_r1 := fun _ _ => rfl
  H_r2 := fun _ _ => rfl
  H_A0 := by intro t h1 _; rw [Bool.eq_iff_iff]; simp [W1f]; omega
  H_A0_prev := by simp [W1f]
  H_q_init := by intro t h; simp [W1f]; omega
  H_A1_init := by intro t h; simp [W1f]; omega
  H_A2_init := by intro t h; simp [W1f]; omega
  H_SETTLED := by simp [Dfast, cDl, x0, fastMin, Corner.of, RF.sym, O6]

theorem W2f_scn (Hz : Int) (hz : 311 < Hz) : Scn2 Dfast W2f 0 (-1000) 134 311 Hz where
  H_ORDER := by omega
  H_r1 := fun _ _ => rfl
  H_r2 := fun _ _ => rfl
  H_A0 := by intro t h1 _; rw [Bool.eq_iff_iff]; simp [W2f]; omega
  H_A0_prev := by simp [W2f]
  H_q_init := by intro t h; simp [W2f]; omega
  H_A1_init := by intro t h; simp [W2f]; omega
  H_A2_init := by intro t h; simp [W2f]; omega
  H_SETTLED := by simp [Dfast, cDl, x0, fastMin, Corner.of, RF.sym, O6]

/-- The servers answer in exactly `smin` (the worst case of the arc forms). -/
theorem W_minserver_corners :
    (400 : Int) = TR Dslow 0 + Dslow.smin ∧ (922 : Int) = RR Dslow 400 + Dslow.smin ∧
    (400 : Int) = TRb Dslow 0 + Dslow.smin ∧ (922 : Int) = RRb Dslow 400 + Dslow.smin ∧
    (134 : Int) = TR Dfast 0 + Dfast.smin ∧ (311 : Int) = RR Dfast 134 + Dfast.smin ∧
    (134 : Int) = TRb Dfast 0 + Dfast.smin ∧ (311 : Int) = RRb Dfast 134 + Dfast.smin := by
  simp [TR, RR, QB, TRb, RRb, QBb, Dslow, Dfast, cDl, x0, slowMax, fastMin, Corner.of, RF.sym,
    O6, O5_I0, O5_I2]

/-- **Non-vacuity at a consistent corner** (both SLOW_MAX and FAST_MIN): a delay
set satisfying all conditions of 7h and 7j and, for each direction, a run of
the gate relations satisfying the scenario. -/
theorem nonvacuous_corners :
    (RT1 Dslow ∧ RT2 Dslow ∧ A0Fork Dslow ∧ RT1b Dslow ∧ RT2b Dslow ∧ A0Fork2 Dslow ∧
      Run Dslow W1s ∧ (∀ Hz, 922 < Hz → Scn Dslow W1s 0 (-1000) 400 922 Hz) ∧
      Run Dslow W2s ∧ (∀ Hz, 922 < Hz → Scn2 Dslow W2s 0 (-1000) 400 922 Hz)) ∧
    (RT1 Dfast ∧ RT2 Dfast ∧ A0Fork Dfast ∧ RT1b Dfast ∧ RT2b Dfast ∧ A0Fork2 Dfast ∧
      Run Dfast W1f ∧ (∀ Hz, 311 < Hz → Scn Dfast W1f 0 (-1000) 134 311 Hz) ∧
      Run Dfast W2f ∧ (∀ Hz, 311 < Hz → Scn2 Dfast W2f 0 (-1000) 134 311 Hz)) :=
  ⟨⟨slow_all.1, slow_all.2.1, slow_all.2.2.1, slow_all.2.2.2.1, slow_all.2.2.2.2.1,
     slow_all.2.2.2.2.2, W1s_run, W1s_scn, W2s_run, W2s_scn⟩,
   ⟨fast_all.1, fast_all.2.1, fast_all.2.2.1, fast_all.2.2.2.1, fast_all.2.2.2.2.1,
     fast_all.2.2.2.2.2, W1f_run, W1f_scn, W2f_run, W2f_scn⟩⟩

/-- The exclusion theorems therefore apply to these runs: e.g. at both corners
neither grants nor acks overlap before any horizon (7h's and 7j's theorems,
instantiated). -/
theorem corners_exclusion (Hz : Int) (hzs : 922 < Hz) (hzf : 311 < Hz) :
    (∀ t, t < Hz → (W1s.g1 t && W1s.g2 t) = false ∧ (W1s.A1 t && W1s.A2 t) = false) ∧
    (∀ t, t < Hz → (W2s.g1 t && W2s.g2 t) = false ∧ (W2s.A1 t && W2s.A2 t) = false) ∧
    (∀ t, t < Hz → (W1f.g1 t && W1f.g2 t) = false ∧ (W1f.A1 t && W1f.A2 t) = false) ∧
    (∀ t, t < Hz → (W2f.g1 t && W2f.g2 t) = false ∧ (W2f.A1 t && W2f.A2 t) = false) := by
  refine ⟨fun t ht => ⟨?_, ?_⟩, fun t ht => ⟨?_, ?_⟩, fun t ht => ⟨?_, ?_⟩, fun t ht => ⟨?_, ?_⟩⟩
  · exact rt1_exclusion W1s_run (W1s_scn Hz hzs) slow_all.1 t ht
  · exact rt2_exclusion_arcs W1s_run (W1s_scn Hz hzs) slow_all.2.1 slow_all.2.2.1 t ht
  · exact rt1_exclusion2 W2s_run (W2s_scn Hz hzs) slow_all.2.2.2.1 t ht
  · exact rt2_exclusion2_arcs W2s_run (W2s_scn Hz hzs) slow_all.2.2.2.2.1 slow_all.2.2.2.2.2 t ht
  · exact rt1_exclusion W1f_run (W1f_scn Hz hzf) fast_all.1 t ht
  · exact rt2_exclusion_arcs W1f_run (W1f_scn Hz hzf) fast_all.2.1 fast_all.2.2.1 t ht
  · exact rt1_exclusion2 W2f_run (W2f_scn Hz hzf) fast_all.2.2.2.1 t ht
  · exact rt2_exclusion2_arcs W2f_run (W2f_scn Hz hzf) fast_all.2.2.2.2.1 fast_all.2.2.2.2.2 t ht

end Witness

end Formal.Cells.ArbCorners
