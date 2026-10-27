import Formal.Cells.ArbBinary

/-!
# Probe Bov: does a digital race trace of `bd_arbcell` explain the 8% overlap?

ARBITER.md: on `hw/arb_mtbf.v` (192 copies of the bare `bd_arbcell`, two
free-running request rings, detector `raw = g1c & g2c`, width filter
`filt = raw & bd_delay(2)(raw)`), 15/192 copies fire the FILTERED sticky bit,
whose minimum threshold is about 203 ps. The flow's prediction caps the
structural overlap at 96 ps. Question: is there a DIGITAL trace (gates + per-pin
transport delays inside prjxray's bands) whose g1.g2 overlap outlives 203 ps?

Model (gate fidelity; real INITs through `lutB`/`o5B`/`o6B` via 7a's `stF`, `gr1`,
`gr2`; the detector's LUT2 INIT `4'h8` through `lutB`):

* every LUT input is read through ONE pure (transport) delay per (pin, output):
  route + site-pin input buffer + LUT arc of that pin (`Dl`). No rise/fall split
  (prjxray has none; `ArbCorners.RF.sym`).
* `Dec`: the grant LUT and the detector, with NO assumption on how `q` moves
  (any Boolean waveform: settled, runt, oscillating, metastable-as-digital).
* `Rig`: `Dec` plus the state LUT `q = stF(r1, r2, q)` with its own delays.

Results:
* §1 `run_cap`: if `x(t-a) ∧ ¬x(t-b)` holds on an interval, the interval is at
  most `|a - b|` long. Nothing about `x` is assumed.
* §2 `grant_cap`: every run of `g1 ∧ g2` at the grant LUT is at most
  `|b5 - b6|`, the q-pin-to-O5 minus q-pin-to-O6 delay, for EVERY trace of the
  requests and of `q`. Since O5 and O6 read q on ONE physical pin
  (H_SHARED_Q_PIN) the route and the site pin cancel (`b_cancel`): only the
  O5-vs-O6 arc of that pin is left. Request-fork skew between ustate and ugrant
  cannot widen it (`g1 = r1.q` is killed by q itself, `g2 = r2.~q` likewise).
  `raw_cap`: at the detector the cap is `|s + b|`, `s = e1 - e2` the
  grant-to-detector skew INCLUDING the detector's site-pin delays.
* §3 exact durations of the two handovers (`handover12`, `handover21`), with the
  request-fork term: `D12 = s + min(κ1, b)`, `D21 = -s + min(κ2, -b)`.
* §4 the transport width filter (`filter_iff`), and a pulse train that it
  passes (`train_passes`).
* §5 prjxray numbers: the cell alone is capped at 33 ps at every consistent
  corner and 112 ps in the independent box (`cell_cap_*`): it CANNOT pass a
  203 ps filter. The rig (detector included) is capped at 184 ps at FAST_MIN
  with zero interconnect skew (`rig_cap_fastMin`) but NOT at SLOW_MAX: an
  explicit SLOW_MAX trace with zero interconnect skew, q settled before and
  after, overlaps for 305 ps and passes every filter delay below 305 ps
  (`slow_trace_*`). The lever is the detector's site-pin delays (A1 516 ps vs
  A5 112 ps), which nextpnr's SDF does not contain.
-/

namespace Formal.Cells.ArbOverlapRace
open Formal.Cells Formal.Cells.ArbBinary

abbrev Sig := Int → Bool

/-- `|a - b|`. -/
def adist (a b : Int) : Int := if b ≤ a then a - b else b - a

/-- `x` is high on the whole interval `[T, T + ℓ)`. -/
def HighOn (x : Sig) (T ℓ : Int) : Prop := ∀ t, T ≤ t → t < T + ℓ → x t = true

/-! ## §1 The shared-signal run cap -/

/-- **Run cap.** If `x` delayed by `a` is high and `x` delayed by `b` is low at
every point of `[T, T+ℓ)`, then `ℓ ≤ |a - b|`. No hypothesis on `x`. -/
theorem run_cap (x : Sig) (a b T ℓ : Int)
    (h : ∀ t, T ≤ t → t < T + ℓ → x (t - a) = true ∧ x (t - b) = false) :
    ℓ ≤ adist a b := by
  unfold adist
  split
  · rename_i hab
    refine Int.not_lt.mp ?_
    intro hl
    have h1 := (h (T + (a - b)) (by omega) (by omega)).1
    have h0 := (h T (Int.le_refl _) (by omega)).2
    rw [show T + (a - b) - a = T - b by omega] at h1
    rw [h1] at h0
    exact absurd h0 (by decide)
  · rename_i hab
    refine Int.not_lt.mp ?_
    intro hl
    have h1 := (h (T + (b - a)) (by omega) (by omega)).2
    have h0 := (h T (Int.le_refl _) (by omega)).1
    rw [show T + (b - a) - b = T - a by omega] at h1
    rw [h1] at h0
    exact absurd h0 (by decide)

/-- The cap is attained: a single falling edge of `x` gives a run of exactly
`a - b` (non-vacuity of `run_cap`). -/
theorem run_cap_tight (a b : Int) (hab : b ≤ a) :
    HighOn (fun t => decide (t - a < 0) && !decide (t - b < 0)) b (a - b) ∧
    adist a b = a - b := by
  refine ⟨?_, by unfold adist; simp [hab]⟩
  intro t h1 h2
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
  omega

/-! ## §2 The model and the caps -/

/-- The detector LUT of `hw/arb_mtbf.v` (`assign anomaly_raw = g1c & g2c`): a
LUT2 with INIT `4'h8`, pins `[I0 = g1c, I1 = g2c]`. -/
def DET : Nat := 8
def det (a b : Bool) : Bool := lutB DET [a, b]

theorem det_eq (a b : Bool) : det a b = (a && b) := by
  cases a <;> cases b <;> decide

/-- Per-pin transport delays (ps). Each is route + site-pin input buffer + the
LUT arc from that pin to that output. -/
structure Dl where
  /-- r1 → q (ustate O6). -/
  s1 : Int
  /-- r2 → q. -/
  s2 : Int
  /-- q → q (feedback route + site pin + O6 arc). -/
  L : Int
  /-- r1 → g1 (ugrant O5). -/
  a1 : Int
  /-- r2 → O5 (the O5 function ignores it). -/
  x2 : Int
  /-- q → g1 (O5). -/
  b5 : Int
  /-- r1 → O6 (the O6 function ignores it). -/
  x1 : Int
  /-- r2 → g2 (ugrant O6). -/
  a2 : Int
  /-- q → g2 (O6). -/
  b6 : Int
  /-- g1 → raw (route + detector site pin + detector arc). -/
  e1 : Int
  /-- g2 → raw. -/
  e2 : Int

/-- The grant LUT and the detector. Nothing is assumed about `r1`, `r2`, `q`. -/
structure Dec (D : Dl) (r1 r2 q g1 g2 raw : Sig) : Prop where
  /-- H_G5: O5 of `ugrant` is the real INIT on its pins, each read through its
  own transport delay (mux tree behind input buffers, no rise/fall split).
  Test: GLS with transport LUT outputs and per-pin site delays. -/
  H_G5 : ∀ t, g1 t = gr1 (r1 (t - D.a1)) (r2 (t - D.x2)) (q (t - D.b5))
  /-- H_G6: the same for O6. -/
  H_G6 : ∀ t, g2 t = gr2 (r1 (t - D.x1)) (r2 (t - D.a2)) (q (t - D.b6))
  /-- H_DET: the detector LUT2 (INIT 8) with per-pin transport delays. -/
  H_DET : ∀ t, raw t = det (g1 (t - D.e1)) (g2 (t - D.e2))

/-- The full rig: `Dec` plus the state LUT (`bd_c2n_set`, real INIT, rst = 0). -/
structure Rig (D : Dl) (r1 r2 q g1 g2 raw : Sig) : Prop extends Dec D r1 r2 q g1 g2 raw where
  /-- H_ST: `ustate` with per-pin transport delays and its feedback loop. -/
  H_ST : ∀ t, q t = stF (r1 (t - D.s1)) (r2 (t - D.s2)) (q (t - D.L))

/-- **Grant cap (candidates a, b, c at the cell).** For EVERY waveform of the
requests and of `q` (request-fork skew, near ties, runts, endless oscillation),
every interval on which both grants are high is at most `|b5 - b6|` long. -/
theorem grant_cap {D : Dl} {r1 r2 q g1 g2 raw : Sig} (hD : Dec D r1 r2 q g1 g2 raw)
    (T ℓ : Int) (h : HighOn (fun t => g1 t && g2 t) T ℓ) : ℓ ≤ adist D.b5 D.b6 := by
  apply run_cap q D.b5 D.b6 T ℓ
  intro t h1 h2
  have := h t h1 h2
  simp only [hD.H_G5, hD.H_G6, gr1_eq, gr2_eq, Bool.and_eq_true, Bool.not_eq_true'] at this
  exact ⟨this.1.2, this.2.2⟩

/-- **Detector cap.** Every run of `raw` is at most `|(e1 + b5) - (e2 + b6)|`. -/
theorem raw_cap {D : Dl} {r1 r2 q g1 g2 raw : Sig} (hD : Dec D r1 r2 q g1 g2 raw)
    (T ℓ : Int) (h : HighOn raw T ℓ) : ℓ ≤ adist (D.e1 + D.b5) (D.e2 + D.b6) := by
  apply run_cap q (D.e1 + D.b5) (D.e2 + D.b6) T ℓ
  intro t h1 h2
  have := h t h1 h2
  simp only [hD.H_DET, det_eq, hD.H_G5, hD.H_G6, gr1_eq, gr2_eq, Bool.and_eq_true,
    Bool.not_eq_true'] at this
  rw [show t - (D.e1 + D.b5) = t - D.e1 - D.b5 by omega,
      show t - (D.e2 + D.b6) = t - D.e2 - D.b6 by omega]
  exact ⟨this.1.2, this.2.2⟩

/-- How the delays decompose physically (all named, all from prjxray / SDF). -/
structure Decomp (D : Dl) where
  /-- q route to ugrant, q's site pin at ugrant, its O5 and O6 arcs. -/
  wq : Int
  pq : Int
  o5q : Int
  o6q : Int
  /-- grant routes to the detector, detector site pins, detector arc, and any
  extra O5-side output delay (AMUX output path; prjxray lists none: 0). -/
  w1 : Int
  w2 : Int
  p1 : Int
  p2 : Int
  od : Int
  xo5 : Int
  /-- H_SHARED_Q_PIN: O5 and O6 of a LUT6_2 read q on ONE physical pin, so they
  share its route and its site-pin buffer; only the arc into each LUT5 half
  differs. Fact of the CLB (A1..A5 feed both halves). Test: FASM pin map
  (`PinAssign`): ugrant has one q pin. -/
  H_SHARED_Q_PIN : D.b5 = wq + pq + o5q ∧ D.b6 = wq + pq + o6q
  /-- H_DET_PATHS: each detector input is route + its OWN site pin + arc. -/
  H_DET_PATHS : D.e1 = w1 + xo5 + p1 + od ∧ D.e2 = w2 + p2 + od

/-- The q route and q's site-pin delay cancel: `b = o5q - o6q`. -/
theorem b_cancel {D : Dl} (P : Decomp D) : D.b5 - D.b6 = P.o5q - P.o6q := by
  have := P.H_SHARED_Q_PIN; omega

/-- At the detector: `s + b = (w1 - w2) + xo5 + (p1 - p2) + (o5q - o6q)`; the
interconnect skew `w1 - w2` is the only part nextpnr's SDF reports. -/
theorem sb_eq {D : Dl} (P : Decomp D) :
    (D.e1 + D.b5) - (D.e2 + D.b6) = (P.w1 - P.w2) + P.xo5 + (P.p1 - P.p2) + (P.o5q - P.o6q) := by
  have := P.H_SHARED_Q_PIN; have := P.H_DET_PATHS; omega

/-! ## §3 The two handovers, exactly -/

/-- **Handover r1 → r2** (`r2` steady high, `r1` falls at `f`, q = 1 settled
before). `q` falls exactly at `f + s1`, and `raw` is high exactly on
`[f + s1 + e2 + b6, min (f + e1 + a1) (f + s1 + e1 + b5))`, i.e. for
`s + min (κ1, b)` with `s = e1 - e2`, `b = b5 - b6`, `κ1 = a1 - s1 - b6`. -/
theorem handover12 {D : Dl} {r1 r2 q g1 g2 raw : Sig} (hR : Rig D r1 r2 q g1 g2 raw) (f : Int)
    (hr1 : ∀ t, r1 t = decide (t < f)) (hr2 : ∀ t, r2 t = true)
    (hq0 : ∀ t, t < f + D.s1 → q t = true) :
    (∀ t, q t = decide (t < f + D.s1)) ∧
    ∀ t, raw t = true ↔
      (f + D.s1 + D.e2 + D.b6 ≤ t ∧ t < f + D.e1 + D.a1 ∧ t < f + D.s1 + D.e1 + D.b5) := by
  have hq : ∀ t, q t = decide (t < f + D.s1) := by
    intro t
    by_cases ht : t < f + D.s1
    · rw [hq0 t ht]; simp [ht]
    · rw [hR.H_ST t, hr1, hr2, stF_eq]
      have : ¬ (t - D.s1 < f) := by omega
      simp [this, ht]
  refine ⟨hq, ?_⟩
  intro t
  rw [hR.H_DET, det_eq, hR.H_G5, hR.H_G6, gr1_eq, gr2_eq, hr1, hr2, hq, hq]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
    Bool.true_and]
  constructor
  · intro h; omega
  · intro h; omega

/-- **Handover r2 → r1** (`r1` steady high, `r2` falls at `f`, q = 0 settled
before). `raw` is high exactly on
`[f + s2 + e1 + b5, min (f + e2 + a2) (f + s2 + e2 + b6))`, i.e. for
`-s + min (κ2, -b)` with `κ2 = a2 - s2 - b5`. -/
theorem handover21 {D : Dl} {r1 r2 q g1 g2 raw : Sig} (hR : Rig D r1 r2 q g1 g2 raw) (f : Int)
    (hr1 : ∀ t, r1 t = true) (hr2 : ∀ t, r2 t = decide (t < f))
    (hq0 : ∀ t, t < f + D.s2 → q t = false) :
    (∀ t, q t = decide (f + D.s2 ≤ t)) ∧
    ∀ t, raw t = true ↔
      (f + D.s2 + D.e1 + D.b5 ≤ t ∧ t < f + D.e2 + D.a2 ∧ t < f + D.s2 + D.e2 + D.b6) := by
  have hq : ∀ t, q t = decide (f + D.s2 ≤ t) := by
    intro t
    by_cases ht : t < f + D.s2
    · rw [hq0 t ht]; have : ¬ (f + D.s2 ≤ t) := by omega
      simp [this]
    · rw [hR.H_ST t, hr1, hr2, stF_eq]
      have : ¬ (t - D.s2 < f) := by omega
      have h2 : f + D.s2 ≤ t := by omega
      simp [this, h2]
  refine ⟨hq, ?_⟩
  intro t
  rw [hR.H_DET, det_eq, hR.H_G5, hR.H_G6, gr1_eq, gr2_eq, hr1, hr2, hq, hq]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
    Bool.true_and]
  constructor
  · intro h; omega
  · intro h; omega

/-! ## §4 The width filter (transport) -/

/-- `filt = raw & bd_delay(W)(raw)` with transport delays: `c0` the direct pin,
`c0 + Dw` the delayed pin. On an isolated run `[lo, hi)` it fires iff the run is
longer than `Dw` (the filter threshold, ≥ ~203 ps on the board, H_FILTER). -/
theorem filter_iff (raw : Sig) (lo hi c0 Dw : Int)
    (hraw : ∀ t, raw t = true ↔ lo ≤ t ∧ t < hi) (hD : 0 ≤ Dw) :
    (∃ t, (raw (t - c0) && raw (t - c0 - Dw)) = true) ↔ Dw < hi - lo := by
  constructor
  · rintro ⟨t, ht⟩
    simp only [Bool.and_eq_true, hraw] at ht
    omega
  · intro h
    refine ⟨lo + Dw + c0, ?_⟩
    simp only [Bool.and_eq_true, hraw]
    omega

/-- **Candidate (b), the caveat.** For a pulse TRAIN the transport filter is not
a width filter: 6 ps pulses every 140 ps pass a 280 ps filter (aliasing). Every
single run is still capped by `raw_cap`. -/
theorem train_passes :
    let raw : Sig := fun t => decide (t % 140 < 6)
    (raw (0 - 0) && raw (0 - 0 - 280)) = true ∧ ¬ HighOn raw 0 7 := by
  refine ⟨by decide, ?_⟩
  intro h
  have := h 6 (by decide) (by decide)
  exact absurd this (by decide)

/-! ## §5 prjxray numbers (CLBLL_L/R, CLBLM_L/R `.sdf` and `tile_type_*.json`)

Columns are `(FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX)`; ranges over every
A..D LUT and every pin of the four CLB tile types:
* O6 arc: flat 45 / 56 / 100 / 124 (every pin).
* O5 arc: [42,51] / [52,63] / [93,127] / [116,157] (A5 is the fast O5 pin:
  116..120 slow max; A1..A4 149..157).
* site pin (input buffer), SLICEL A1..A6 slow max 516 507 344 284 112 5,
  fast min 172 170 107 86 33 2; SLICEM up to 531 / 180, down to 16 / 7.
  Bands: [2,180] / [2,225] / [4,428] / [5,531].
nextpnr's SDF has a flat 124 ps per LUT arc and no per-pin site delay
(B-arb-a0fork.md, C-10b). -/

/-- **The cell alone, consistent corner**: `|o5q - o6q| ≤ 33` at each of the four
corners (O6 flat, O5 in its column's band). -/
theorem cell_cap_consistent (o5q : Int) :
    ((42 ≤ o5q ∧ o5q ≤ 51) → adist o5q 45 ≤ 6) ∧
    ((52 ≤ o5q ∧ o5q ≤ 63) → adist o5q 56 ≤ 7) ∧
    ((93 ≤ o5q ∧ o5q ≤ 127) → adist o5q 100 ≤ 27) ∧
    ((116 ≤ o5q ∧ o5q ≤ 157) → adist o5q 124 ≤ 33) := by
  unfold adist
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> split <;> omega

/-- **The cell alone, independent box** (every arc anywhere in [FAST_MIN, SLOW_MAX]). -/
theorem cell_cap_box (o5q o6q : Int) (h5 : 42 ≤ o5q ∧ o5q ≤ 157) (h6 : 45 ≤ o6q ∧ o6q ≤ 124) :
    adist o5q o6q ≤ 112 := by
  unfold adist; split <;> omega

/-- **Verdict for the cell.** For every digital trace of `bd_arbcell` (any
request waveforms and fork skews, any `q` waveform), with prjxray arcs in the
independent box, no interval of `g1 ∧ g2` at the grant LUT reaches 113 ps;
hence none outlives a 203 ps filter. -/
theorem cell_never_203 {D : Dl} {r1 r2 q g1 g2 raw : Sig} (hD : Dec D r1 r2 q g1 g2 raw)
    (P : Decomp D) (h5 : 42 ≤ P.o5q ∧ P.o5q ≤ 157) (h6 : 45 ≤ P.o6q ∧ P.o6q ≤ 124)
    (T ℓ : Int) (h : HighOn (fun t => g1 t && g2 t) T ℓ) : ℓ ≤ 112 ∧ ℓ < 203 := by
  have h1 := grant_cap hD T ℓ h
  have h2 := cell_cap_box P.o5q P.o6q h5 h6
  have hb := P.H_SHARED_Q_PIN
  have : adist D.b5 D.b6 = adist P.o5q P.o6q := by
    unfold adist; rw [hb.1, hb.2]; split <;> split <;> omega
  omega

/-- **The rig at FAST_MIN with zero interconnect skew** (`w1 = w2`, no extra O5
output delay): no run of `raw` reaches 185 ps, so nothing passes 203 ps. -/
theorem rig_cap_fastMin {D : Dl} {r1 r2 q g1 g2 raw : Sig} (hD : Dec D r1 r2 q g1 g2 raw)
    (P : Decomp D) (hw : P.w1 = P.w2) (hx : P.xo5 = 0)
    (hp1 : 2 ≤ P.p1 ∧ P.p1 ≤ 180) (hp2 : 2 ≤ P.p2 ∧ P.p2 ≤ 180)
    (h5 : 42 ≤ P.o5q ∧ P.o5q ≤ 51) (h6 : P.o6q = 45)
    (T ℓ : Int) (h : HighOn raw T ℓ) : ℓ ≤ 184 := by
  have h1 := raw_cap hD T ℓ h
  have h2 := sb_eq P
  unfold adist at h1; split at h1 <;> omega

/-- The SLOW_MAX analogue of the cap is 559 ps: the bound alone does not
exclude a 203 ps run there. -/
theorem rig_cap_slowMax_value {D : Dl} {r1 r2 q g1 g2 raw : Sig} (hD : Dec D r1 r2 q g1 g2 raw)
    (P : Decomp D) (hw : P.w1 = P.w2) (hx : P.xo5 = 0)
    (hp1 : 5 ≤ P.p1 ∧ P.p1 ≤ 531) (hp2 : 5 ≤ P.p2 ∧ P.p2 ≤ 531)
    (h5 : 116 ≤ P.o5q ∧ P.o5q ≤ 157) (h6 : P.o6q = 124)
    (T ℓ : Int) (h : HighOn raw T ℓ) : ℓ ≤ 559 := by
  have h1 := raw_cap hD T ℓ h
  have h2 := sb_eq P
  unfold adist at h1; split at h1 <;> omega

/-! ### An explicit SLOW_MAX trace that passes the filter

Every number is SLOW_MAX (one consistent corner), SLICEL:
* ustate: r1 on A5 (site 112) via a 400 ps route, O6 124: `s1 = 636`; r2 likewise
  `s2 = 636` (unused); q feedback on A1 (site 516), 0 ps intra-site route, O6:
  `L = 640`.
* ugrant: r1 on A1 (516) via the same 400 ps route, O5(A1) 152: `a1 = 1068`;
  q on A5 (site 112) over the same-slice 295 ps hop, O5(A5) 118 / O6 124:
  `b5 = 525`, `b6 = 531`; r2 on A2: `a2 = 400 + 507 + 124 = 1031`.
* detector: g1c on A1 (516), g2c on A5 (112), EQUAL 300 ps routes (SDF skew 0),
  O6 124: `e1 = 940`, `e2 = 536`. So `s = 404`, `b = -6`, `κ1 = -99`.
`D12 = 404 + min(-99, -6) = 305 ps`. -/

def slowD : Dl where
  s1 := 636
  s2 := 636
  L := 640
  a1 := 1068
  x2 := 1031
  b5 := 525
  x1 := 1068
  a2 := 1031
  b6 := 531
  e1 := 940
  e2 := 536

/-- The decomposition of `slowD` into prjxray SLOW_MAX pieces (non-vacuous). -/
def slowP : Decomp slowD where
  wq := 295
  pq := 112
  o5q := 118
  o6q := 124
  w1 := 300
  w2 := 300
  p1 := 516
  p2 := 112
  od := 124
  xo5 := 0
  H_SHARED_Q_PIN := by decide
  H_DET_PATHS := by decide

def sR1 : Sig := fun t => decide (t < 0)
def sR2 : Sig := fun _ => true
def sQ : Sig := fun t => decide (t < 636)
def sG1 : Sig := fun t => gr1 (sR1 (t - 1068)) (sR2 (t - 1031)) (sQ (t - 525))
def sG2 : Sig := fun t => gr2 (sR1 (t - 1068)) (sR2 (t - 1031)) (sQ (t - 531))
def sRaw : Sig := fun t => det (sG1 (t - 940)) (sG2 (t - 536))

/-- The explicit trace satisfies every gate relation of the rig. -/
theorem slow_trace_rig : Rig slowD sR1 sR2 sQ sG1 sG2 sRaw where
  H_G5 := fun _ => rfl
  H_G6 := fun _ => rfl
  H_DET := fun _ => rfl
  H_ST := by
    intro t
    simp only [sQ, sR1, sR2, slowD, stF_eq]
    by_cases h : t < 636
    · have h1 : t - 636 < 0 := by omega
      have h2 : t - 640 < 636 := by omega
      simp [h, h1, h2]
    · have h1 : ¬ (t - 636 < 0) := by omega
      simp [h, h1]

/-- **The explicit overlap**: `raw` is high exactly on `[1703, 2008)`, 305 ps,
with zero grant-to-detector interconnect skew. -/
theorem slow_trace_raw (t : Int) : sRaw t = true ↔ 1703 ≤ t ∧ t < 2008 := by
  have := (handover12 slow_trace_rig 0 (fun _ => rfl) (fun _ => rfl)
    (fun t ht => by simp [sQ, slowD] at ht ⊢; omega)).2 t
  rw [this]; simp only [slowD]; omega

/-- **It passes every filter threshold below 305 ps** (in particular 203). -/
theorem slow_trace_passes (c0 Dw : Int) (h0 : 0 ≤ Dw) :
    (∃ t, (sRaw (t - c0) && sRaw (t - c0 - Dw)) = true) ↔ Dw < 305 := by
  have := filter_iff sRaw 1703 2008 c0 Dw slow_trace_raw h0
  rw [this]; omega

theorem slow_trace_passes_203 : ∃ t, (sRaw t && sRaw (t - 203)) = true := by
  obtain ⟨t, ht⟩ := (slow_trace_passes 0 203 (by decide)).2 (by decide)
  exact ⟨t, by simpa using ht⟩

/-- Negative control (the check can fail): the same trace with g1c moved to the
detector's A5 pin as well (`e1 = e2 = 536`, so `s = 0`) has NO overlap at all. -/
def ctrlD : Dl := { slowD with e1 := 536 }

theorem ctrl_trace_clean (r1 r2 q g1 g2 raw : Sig) (hR : Rig ctrlD r1 r2 q g1 g2 raw)
    (hr1 : ∀ t, r1 t = decide (t < 0)) (hr2 : ∀ t, r2 t = true)
    (hq0 : ∀ t, t < 0 + ctrlD.s1 → q t = true) (t : Int) : raw t = false := by
  have := (handover12 hR 0 hr1 hr2 hq0).2 t
  simp only [ctrlD, slowD] at this
  cases h : raw t
  · rfl
  · exact absurd (this.1 h) (by omega)

/-- Negative control: the SAME pins at FAST_MIN (site 172/33, O5(A5) 48, O6 45,
routes scaled to 0.4x) give `s + b = 139 + 3 = 142`, below 203 by `rig_cap`. -/
theorem slow_pins_at_fastMin : (160 + 172 + 45) + (118 + 33 + 48) - ((160 + 33 + 45) + (118 + 33 + 45)) = 142 := by
  decide

end Formal.Cells.ArbOverlapRace
