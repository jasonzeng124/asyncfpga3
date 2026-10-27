import Formal.Cells.ArbCorners
import Formal.Cells.PinAssign

/-!
# Probe Bc2: ArbCorners' numeric results redone with the ROUTED pin of every seed

Audit P3 rows 1-2 (`audit/findings/P3.md`, `audit/lean/P3/ArbPinA5.lean`):
`ArbCorners` took every O5 arc from ONE prjxray line, `CLBLL_L.sdf SLICEL/A5LUT`,
with q on A3 ("I2 under the identity pin map", 42/150 ps). The repo's own routed
arbiters (`Formal.Net.FasmLink.S1..S4`, read back from the four `link_arb`
bitstreams, nextpnr sha256 9c732bc6303458df) place `ustate` and `ugrant` in
`CLBLM_R` tiles, `SLICEM_X0` (SLICE_X42..), A LUT, and nextpnr chose the pins.
`PinAssign` proved those pins from the bits. This file

* §0  takes the arcs of the RIGHT SDF cell (`CLBLM_R.sdf`, `SLICEM/A5LUT`,
       per physical pin A1..A5) and the bit-proved pin maps of every seed, and
       ties each seed's pin list to `PinAssign`'s `Realizes`/`_src` theorems;
* §1  re-derives 7h/7j's margins with SEVEN arc classes (ustate O5 from its
       r1, r2 and q pins; ugrant O5 from its r1, r2 and q pins; O6) instead of
       ArbCorners' three, and proves ArbCorners' `cDl` is the special case;
* §2  RT1 / RT1b structural: exact iff in the arcs (`gQ ≤ o6` / `o6 ≤ gQ`),
       per seed at SLOW_MAX and FAST_MIN;
* §3  per-seed arc parts (SLOW_MAX, FAST_MIN) and flip-window existence;
* §4  7e skew caps per seed;
* §5  rule J per seed, on 7g's run semantics: optimistic by 8 ps (S1, S3, S4),
       conservative by 24 ps (S2), with explicit runs;
* §6  guarded rule J under PER-WIRE corner ratios in a band `[a/d, b/d]`:
       the exact pointwise condition, a uniform sufficient condition, the
       uniform necessary condition `772·b ≤ 1155·a`, and the audit's −118.5 ps
       counterexample as an instance.

Fidelity: the LUT functions are the real INITs (inherited, and the pin maps are
`PinAssign`'s bit-proved `Realizes`). LUT timing: one transport arc per
(LUT, physical input pin, output) at one prjxray column, rise = fall (prjxray
has no edge split); 7h/7j's rise-fast OR channel at rise = fall is a plain
transport delay. Routes and site pins: one delay per pin, as in 7h/7g.
-/

namespace Formal.Cells.ArbCornersPin
open Formal.Cells Formal.Cells.ArbCorners Formal.Cells.PinAssign

/-! ## §0 Data: the SDF cell of the routed sites, and the pins from the bits -/

/-- prjxray-db zynq7 `timings/CLBLM_R.sdf`, cell `LUT_OR_MEM5LRAM`, instance
`SLICEM/A5LUT`, `(IOPATH A<k+1> O5 (FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX))`, ps:

    A1 (0.044::0.055)(0.121::0.150)    A2 (0.044::0.055)(0.118::0.146)
    A3 (0.043::0.053)(0.120::0.148)    A4 (0.046::0.057)(0.121::0.150)
    A5 (0.048::0.060)(0.093::0.116)

Physical pin index `k` is 0-based (0 = A1), as in `PinAssign`. A6 is not an O5
input; out-of-range indices give an all-zero column, which every use below
rules out (`PA.Ok` needs `0 < o6` only, but every seed's arcs are decided). -/
def pinCol : Nat → Col
  | 0 => ⟨44, 55, 121, 150⟩
  | 1 => ⟨44, 55, 118, 146⟩
  | 2 => ⟨43, 53, 120, 148⟩
  | 3 => ⟨46, 57, 121, 150⟩
  | 4 => ⟨48, 60, 93, 116⟩
  | _ => ⟨0, 0, 0, 0⟩

/-- `CLBLM_R.sdf SLICEM/A6LUT`: `(IOPATH A1..A6 O6 (0.045::0.056)(0.100::0.124))`,
the same flat column as ArbCorners' `O6` (SLICEL). -/
theorem O6_same : O6 = ⟨45, 56, 100, 124⟩ := rfl

/-- The SLICEM A3 arc is NOT ArbCorners' SLICEL A3 (`O5_I2`, 42/150): it is 43/148. -/
theorem slicem_A3_ne : pinCol 2 ≠ O5_I2 ∧ (pinCol 2).fmin = 43 ∧ (pinCol 2).smax = 148 := by
  refine ⟨?_, rfl, rfl⟩
  intro h; have := congrArg Col.smax h; simp [pinCol, O5_I2] at this

/-- The A5 arc is the only one whose SLOW_MAX is below O6's (116 < 124) and whose
FAST_MIN is above O6's (48 > 45): the sign of `o6 − o5` flips against every other pin. -/
theorem A5_vs_O6 :
    (pinCol 4).smax < O6.smax ∧ O6.fmin < (pinCol 4).fmin ∧
    (∀ k, k < 4 → O6.smax < (pinCol k).smax ∧ (pinCol k).fmin ≤ O6.fmin + 1) := by
  refine ⟨by decide, by decide, ?_⟩
  intro k hk
  match k, hk with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide

/-- A seed's physical pins (0-based) for the two LUT6_2 cells of `bd_arbiter`.
`ust`: ustate's (r1, r2, q feedback, rst, A0); `ug`: ugrant's (r1, r2, q). -/
structure Seed where
  ust : List Nat
  ug : List Nat

def s1 : Seed := ⟨[2, 3, 4, 0, 1], [0, 3, 4]⟩
def s2 : Seed := ⟨[2, 1, 4, 0, 3], [0, 4, 2]⟩
def s3 : Seed := ⟨[4, 1, 0, 2, 3], [2, 1, 4]⟩
def s4 : Seed := ⟨[0, 3, 4, 2, 1], [2, 1, 4]⟩

/-- **The pins are the bits'.** Seed 1: ustate is `S1.lut3` (SLICE_X42Y94,
CLBLM_R_X29Y94.SLICEM_X0.ALUT), ugrant `S1.lut5` (SLICE_X42Y95, ...SLICEM_X0.ALUT).
With `s1`'s pin lists, the physical O5 realizes the real cell O5 (R0 / g1) and
the pins are wired to r1 (port 5), r2 (port 6) and q (ustate's O6). -/
theorem s1_bits :
    Realizes Formal.Net.FasmLink.S1.lut3 .o5 (o5B initUstate) vecUstate s1.ust 5 = true ∧
    s1.ust.map (fun k => Formal.Net.FasmLink.S1.lut3.pins[k]?) =
      [some (.port 5), some (.port 6), some (.lut 3 .o6), some (.port 8), some (.port 0)] ∧
    Realizes Formal.Net.FasmLink.S1.lut5 .o5 (o5B initUgrant) vecUgrant s1.ug 3 = true ∧
    s1.ug.map (fun k => Formal.Net.FasmLink.S1.lut5.pins[k]?) =
      [some (.port 5), some (.port 6), some (.lut 3 .o6)] ∧
    Formal.Net.FasmLink.S1.lut3.site = "SLICE_X42Y94" ∧ Formal.Net.FasmLink.S1.lut5.site = "SLICE_X42Y95" :=
  ⟨la1_ustate_o5, la1_ustate_src, la1_ugrant_o5, la1_ugrant_src, rfl, rfl⟩

/-- Seed 2: ustate `S2.lut4` (SLICE_X42Y89), ugrant `S2.lut3` (SLICE_X42Y87); q on ugrant's A3. -/
theorem s2_bits :
    Realizes Formal.Net.FasmLink.S2.lut4 .o5 (o5B initUstate) vecUstate s2.ust 5 = true ∧
    s2.ust.map (fun k => Formal.Net.FasmLink.S2.lut4.pins[k]?) =
      [some (.port 5), some (.port 6), some (.lut 4 .o6), some (.port 8), some (.port 0)] ∧
    Realizes Formal.Net.FasmLink.S2.lut3 .o5 (o5B initUgrant) vecUgrant s2.ug 3 = true ∧
    s2.ug.map (fun k => Formal.Net.FasmLink.S2.lut3.pins[k]?) =
      [some (.port 5), some (.port 6), some (.lut 4 .o6)] ∧
    Formal.Net.FasmLink.S2.lut4.site = "SLICE_X42Y89" ∧ Formal.Net.FasmLink.S2.lut3.site = "SLICE_X42Y87" :=
  ⟨la2_ustate_o5, la2_ustate_src, la2_ugrant_o5, la2_ugrant_src, rfl, rfl⟩

/-- Seed 3: ustate `S3.lut4` (SLICE_X42Y93), ugrant `S3.lut6` (SLICE_X42Y97); q on ugrant's A5. -/
theorem s3_bits :
    Realizes Formal.Net.FasmLink.S3.lut4 .o5 (o5B initUstate) vecUstate s3.ust 5 = true ∧
    s3.ust.map (fun k => Formal.Net.FasmLink.S3.lut4.pins[k]?) =
      [some (.port 5), some (.port 6), some (.lut 4 .o6), some (.port 8), some (.port 0)] ∧
    Realizes Formal.Net.FasmLink.S3.lut6 .o5 (o5B initUgrant) vecUgrant s3.ug 3 = true ∧
    s3.ug.map (fun k => Formal.Net.FasmLink.S3.lut6.pins[k]?) =
      [some (.port 5), some (.port 6), some (.lut 4 .o6)] ∧
    Formal.Net.FasmLink.S3.lut4.site = "SLICE_X42Y93" ∧ Formal.Net.FasmLink.S3.lut6.site = "SLICE_X42Y97" :=
  ⟨la3_ustate_o5, la3_ustate_src, la3_ugrant_o5, la3_ugrant_src, rfl, rfl⟩

/-- Seed 4: ustate `S4.lut3` (SLICE_X42Y88), ugrant `S4.lut5` (SLICE_X42Y91); q on ugrant's A5. -/
theorem s4_bits :
    Realizes Formal.Net.FasmLink.S4.lut3 .o5 (o5B initUstate) vecUstate s4.ust 5 = true ∧
    s4.ust.map (fun k => Formal.Net.FasmLink.S4.lut3.pins[k]?) =
      [some (.port 5), some (.port 6), some (.lut 3 .o6), some (.port 8), some (.port 0)] ∧
    Realizes Formal.Net.FasmLink.S4.lut5 .o5 (o5B initUgrant) vecUgrant s4.ug 3 = true ∧
    s4.ug.map (fun k => Formal.Net.FasmLink.S4.lut5.pins[k]?) =
      [some (.port 5), some (.port 6), some (.lut 3 .o6)] ∧
    Formal.Net.FasmLink.S4.lut3.site = "SLICE_X42Y88" ∧ Formal.Net.FasmLink.S4.lut5.site = "SLICE_X42Y91" :=
  ⟨la4_ustate_o5, la4_ustate_src, la4_ugrant_o5, la4_ugrant_src, rfl, rfl⟩

/-- q enters ugrant on A5 (index 4) in S1, S3, S4 and on A3 (index 2) in S2;
ustate reads its own q on A5 in S1, S2, S4 and on A1 in S3. -/
theorem q_pins :
    s1.ug[2]? = some 4 ∧ s2.ug[2]? = some 2 ∧ s3.ug[2]? = some 4 ∧ s4.ug[2]? = some 4 ∧
    s1.ust[2]? = some 4 ∧ s2.ust[2]? = some 4 ∧ s3.ust[2]? = some 0 ∧ s4.ust[2]? = some 4 := by
  decide

/-! ## §1 Seven arc classes instead of three -/

/-- Pinned arcs at one corner (ps, rise = fall). `o6`: any pin to O6 (ustate's q,
ugrant's g2, ua_k: flat over pins, letters and tiles). `uR1 uR2 uQ`: ustate O5
(R0) from its r1, r2, q pins. `gR1 gR2 gQ`: ugrant O5 (g1) from its r1, r2, q pins. -/
structure PA where
  o6 : Int
  uR1 : Int
  uR2 : Int
  uQ : Int
  gR1 : Int
  gR2 : Int
  gQ : Int
  deriving DecidableEq

abbrev PA.Ok (a : PA) : Prop :=
  0 < a.o6 ∧ 0 ≤ a.uR1 ∧ 0 ≤ a.uR2 ∧ 0 ≤ a.uQ ∧ 0 ≤ a.gR1 ∧ 0 ≤ a.gR2 ∧ 0 ≤ a.gQ

/-- A seed's arcs at the prjxray column `sel`, each O5 arc from its routed pin's line. -/
def Seed.at (s : Seed) (sel : Col → Int) : PA :=
  ⟨sel O6, sel (pinCol (s.ust.getD 0 9)), sel (pinCol (s.ust.getD 1 9)),
   sel (pinCol (s.ust.getD 2 9)), sel (pinCol (s.ug.getD 0 9)),
   sel (pinCol (s.ug.getD 1 9)), sel (pinCol (s.ug.getD 2 9))⟩

/-- ArbCorners' three-class corner as pinned arcs: ustate and ugrant share the
identity pin map (r1, r2 on the "I0/I1" line, q on the "I2" line). -/
def PA.ofCorner (c : Corner) : PA := ⟨c.o6, c.o5a, c.o5a, c.o5q, c.o5a, c.o5a, c.o5q⟩

section Held
open ArbHeldTimed ArbHeldTimed2

/-- 7h's `Dl` with pinned arcs (rise = fall) and routes `x`. -/
def cDlP (a : PA) (ha : a.Ok) (x : Rt) : Dl where
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
  qr := a.o6
  qf := a.o6
  Rr1 := a.uR1
  Rf1 := a.uR1
  Rr2 := a.uR2
  Rf2 := a.uR2
  Rrq := a.uQ
  Rfq := a.uQ
  g1r1 := a.gR1
  g1f1 := a.gR1
  g1r2 := a.gR2
  g1f2 := a.gR2
  g1rq := a.gQ
  g1fq := a.gQ
  g2r := a.o6
  g2f := a.o6
  c1r := a.o6
  c1f := a.o6
  c2r := a.o6
  c2f := a.o6
  smin := x.smin
  H_NONNEG := by have := x.H_nonneg; have := ha; omega
  H_RISE_LE_FALL := by omega
  H_LOOP_POS := by have := x.H_nonneg; have := ha; omega

/-- **Every margin = pinned arc part + the same wire part as ArbCorners.** Note
what no longer cancels: RT1's race keeps `uR1 − gR1` (ustate's and ugrant's r1
pins differ), the pulse conditions read ustate's q pin `uQ`, the structural
disjuncts and fork2 read ugrant's q pin `gQ`. -/
theorem decompP (a : PA) (ha : a.Ok) (x : Rt) :
    mRT1 (cDlP a ha x) = (2 * a.o6 + a.uR1 - a.gR1) + wRT1 x ∧
    mRT1s (cDlP a ha x) = a.o6 - a.gQ ∧
    mPulse (cDlP a ha x) = a.uQ + wPulse x ∧
    mG1 (cDlP a ha x) = (a.uR1 + a.uQ - a.gR1) + wG1 x ∧
    mForkA (cDlP a ha x) = (a.o6 + a.uQ) + wForkA x ∧
    mForkG (cDlP a ha x) = (a.o6 + a.uR1 + a.uQ - a.gR1) + wForkG x ∧
    mFork (cDlP a ha x) = 2 * a.o6 + wFork x ∧
    mRT1b (cDlP a ha x) = (a.uR2 + a.gQ) + wRT1b x ∧
    mRT1bs (cDlP a ha x) = a.gQ - a.o6 ∧
    mPulse2 (cDlP a ha x) = a.uQ + wPulse2 x ∧
    mG2 (cDlP a ha x) = (a.uR2 + a.uQ - a.o6) + wG2 x ∧
    mForkA2 (cDlP a ha x) = (a.o6 + a.uQ) + wForkA2 x ∧
    mForkG2 (cDlP a ha x) = (a.uR2 + a.uQ) + wForkG2 x ∧
    mFork2 (cDlP a ha x) = (a.o6 + a.gQ) + wFork2 x := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [mRT1, mRT1s, mPulse, mG1, mForkA, mForkG, mFork, mRT1b, mRT1bs, mPulse2, mG2,
    mForkA2, mForkG2, mFork2, wRT1, wPulse, wG1, wForkA, wForkG, wFork, wRT1b, wPulse2, wG2,
    wForkA2, wForkG2, wFork2, cDlP] <;>
  omega

/-- **ArbCorners is the identity-pin special case**: with `PA.ofCorner c` every
one of the 14 margins equals ArbCorners' `cDl c RF.sym` margin. -/
theorem margins_ofCorner (c : Corner) (h : (PA.ofCorner c).Ok) (x : Rt) :
    mRT1 (cDlP _ h x) = mRT1 (cDl c RF.sym x) ∧ mRT1s (cDlP _ h x) = mRT1s (cDl c RF.sym x) ∧
    mPulse (cDlP _ h x) = mPulse (cDl c RF.sym x) ∧ mG1 (cDlP _ h x) = mG1 (cDl c RF.sym x) ∧
    mForkA (cDlP _ h x) = mForkA (cDl c RF.sym x) ∧ mForkG (cDlP _ h x) = mForkG (cDl c RF.sym x) ∧
    mFork (cDlP _ h x) = mFork (cDl c RF.sym x) ∧ mRT1b (cDlP _ h x) = mRT1b (cDl c RF.sym x) ∧
    mRT1bs (cDlP _ h x) = mRT1bs (cDl c RF.sym x) ∧
    mPulse2 (cDlP _ h x) = mPulse2 (cDl c RF.sym x) ∧ mG2 (cDlP _ h x) = mG2 (cDl c RF.sym x) ∧
    mForkA2 (cDlP _ h x) = mForkA2 (cDl c RF.sym x) ∧
    mForkG2 (cDlP _ h x) = mForkG2 (cDl c RF.sym x) ∧
    mFork2 (cDlP _ h x) = mFork2 (cDl c RF.sym x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [mRT1, mRT1s, mPulse, mG1, mForkA, mForkG, mFork, mRT1b, mRT1bs, mPulse2, mG2,
    mForkA2, mForkG2, mFork2, cDlP, cDl, PA.ofCorner, RF.sym] <;>
  omega

/-! ## §2 RT1 / RT1b structural: exact conditions -/

/-- **RT1 holds for every routing iff `gQ ≤ o6`** (ugrant's q-pin O5 arc no
slower than O6). If `gQ > o6` a routing with a long r1 → ugrant route breaks it. -/
theorem rt1_structural_iff (a : PA) (ha : a.Ok) :
    (∀ x : Rt, RT1 (cDlP a ha x)) ↔ a.gQ ≤ a.o6 := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hc
    let K : Int := max 0 (2 * a.o6 + a.uR1 - a.gR1) + 1
    have hK : 0 ≤ K := by omega
    let x : Rt := ⟨0, 0, K, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, by omega⟩
    have := h x
    rw [RT1_iff, (decompP a ha x).1, (decompP a ha x).2.1] at this
    simp only [wRT1, x] at this
    omega
  · intro h x
    rw [RT1_iff, (decompP a ha x).2.1]; right; omega

/-- **RT1b holds for every routing iff `o6 ≤ gQ`.** -/
theorem rt1b_structural_iff (a : PA) (ha : a.Ok) :
    (∀ x : Rt, RT1b (cDlP a ha x)) ↔ a.o6 ≤ a.gQ := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hc
    let K : Int := max 0 (a.uR2 + a.gQ) + 1
    have hK : 0 ≤ K := by omega
    let x : Rt := ⟨0, 0, 0, K, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, by omega⟩
    have := h x
    rw [RT1b_iff, (decompP a ha x).2.2.2.2.2.2.2.1, (decompP a ha x).2.2.2.2.2.2.2.2.1] at this
    simp only [wRT1b, x] at this
    omega
  · intro h x
    rw [RT1b_iff, (decompP a ha x).2.2.2.2.2.2.2.2.1]; right; omega

/-- Per-seed corners. -/
def s1S : PA := s1.at Col.smax
def s1F : PA := s1.at Col.fmin
def s2S : PA := s2.at Col.smax
def s2F : PA := s2.at Col.fmin
def s3S : PA := s3.at Col.smax
def s3F : PA := s3.at Col.fmin
def s4S : PA := s4.at Col.smax
def s4F : PA := s4.at Col.fmin

theorem s1S_ok : s1S.Ok := by decide
theorem s1F_ok : s1F.Ok := by decide
theorem s2S_ok : s2S.Ok := by decide
theorem s2F_ok : s2F.Ok := by decide
theorem s3S_ok : s3S.Ok := by decide
theorem s3F_ok : s3F.Ok := by decide
theorem s4S_ok : s4S.Ok := by decide
theorem s4F_ok : s4F.Ok := by decide

/-- The numbers (ps): (o6, uR1, uR2, uQ, gR1, gR2, gQ). -/
theorem seed_arcs :
    s1S = ⟨124, 148, 150, 116, 150, 150, 116⟩ ∧ s1F = ⟨45, 43, 46, 48, 44, 46, 48⟩ ∧
    s2S = ⟨124, 148, 146, 116, 150, 116, 148⟩ ∧ s2F = ⟨45, 43, 44, 48, 44, 48, 43⟩ ∧
    s3S = ⟨124, 116, 146, 150, 148, 146, 116⟩ ∧ s3F = ⟨45, 48, 44, 44, 43, 44, 48⟩ ∧
    s4S = ⟨124, 150, 150, 116, 148, 146, 116⟩ ∧ s4F = ⟨45, 44, 46, 48, 43, 44, 48⟩ := by
  decide

/-- **Which of RT1 / RT1b is structural, per seed and corner.** With q on A5
(S1, S3, S4): RT1 at SLOW_MAX, RT1b at FAST_MIN; with q on A3 (S2): RT1b at
SLOW_MAX, RT1 at FAST_MIN (ArbCorners' identity-pin pattern). In every case the
other one is NOT structural: some routing breaks it. -/
theorem structural_s1 :
    (∀ x, RT1 (cDlP s1S s1S_ok x)) ∧ ¬ (∀ x, RT1b (cDlP s1S s1S_ok x)) ∧
    ¬ (∀ x, RT1 (cDlP s1F s1F_ok x)) ∧ (∀ x, RT1b (cDlP s1F s1F_ok x)) := by
  rw [rt1_structural_iff, rt1b_structural_iff, rt1_structural_iff, rt1b_structural_iff]
  decide

theorem structural_s2 :
    ¬ (∀ x, RT1 (cDlP s2S s2S_ok x)) ∧ (∀ x, RT1b (cDlP s2S s2S_ok x)) ∧
    (∀ x, RT1 (cDlP s2F s2F_ok x)) ∧ ¬ (∀ x, RT1b (cDlP s2F s2F_ok x)) := by
  rw [rt1_structural_iff, rt1b_structural_iff, rt1_structural_iff, rt1b_structural_iff]
  decide

theorem structural_s3 :
    (∀ x, RT1 (cDlP s3S s3S_ok x)) ∧ ¬ (∀ x, RT1b (cDlP s3S s3S_ok x)) ∧
    ¬ (∀ x, RT1 (cDlP s3F s3F_ok x)) ∧ (∀ x, RT1b (cDlP s3F s3F_ok x)) := by
  rw [rt1_structural_iff, rt1b_structural_iff, rt1_structural_iff, rt1b_structural_iff]
  decide

theorem structural_s4 :
    (∀ x, RT1 (cDlP s4S s4S_ok x)) ∧ ¬ (∀ x, RT1b (cDlP s4S s4S_ok x)) ∧
    ¬ (∀ x, RT1 (cDlP s4F s4F_ok x)) ∧ (∀ x, RT1b (cDlP s4F s4F_ok x)) := by
  rw [rt1_structural_iff, rt1b_structural_iff, rt1_structural_iff, rt1b_structural_iff]
  decide

/-- The structural margins themselves (`o6 − gQ`, the RT1 one; RT1b's is its negative):
S1/S3/S4: +8 at SLOW_MAX, −3 at FAST_MIN; S2: −24, +2 (ArbCorners: −26, +3). -/
theorem structural_margins :
    s1S.o6 - s1S.gQ = 8 ∧ s1F.o6 - s1F.gQ = -3 ∧ s2S.o6 - s2S.gQ = -24 ∧ s2F.o6 - s2F.gQ = 2 ∧
    s3S.o6 - s3S.gQ = 8 ∧ s3F.o6 - s3F.gQ = -3 ∧ s4S.o6 - s4S.gQ = 8 ∧ s4F.o6 - s4F.gQ = -3 := by
  decide

/-! ## §3 Per-seed arc parts and flip windows -/

/-- The 14 arc parts of `decompP`, in the order RT1, RT1s, pulse, g1, forkA,
forkG, fork, RT1b, RT1bs, pulse2, g2, forkA2, forkG2, fork2. -/
def PA.parts (a : PA) : List Int :=
  [2 * a.o6 + a.uR1 - a.gR1, a.o6 - a.gQ, a.uQ, a.uR1 + a.uQ - a.gR1, a.o6 + a.uQ,
   a.o6 + a.uR1 + a.uQ - a.gR1, 2 * a.o6, a.uR2 + a.gQ, a.gQ - a.o6, a.uQ,
   a.uR2 + a.uQ - a.o6, a.o6 + a.uQ, a.uR2 + a.uQ, a.o6 + a.gQ]

/-- ArbCorners' (identity pin, SLICEL) values, for comparison (`arcs_slowMax/fastMin`). -/
theorem parts_identity :
    (PA.ofCorner slowMax).parts = [248, -26, 150, 150, 274, 274, 248, 302, 26, 150, 178, 274, 302, 274] ∧
    (PA.ofCorner fastMin).parts = [90, 3, 42, 42, 87, 87, 90, 86, -3, 42, 41, 87, 86, 87] := by
  decide

/-- **Per-seed arc parts at SLOW_MAX** (ps). -/
theorem parts_slowMax :
    s1S.parts = [246, 8, 116, 114, 240, 238, 248, 266, -8, 116, 142, 240, 266, 240] ∧
    s2S.parts = [246, -24, 116, 114, 240, 238, 248, 294, 24, 116, 138, 240, 262, 272] ∧
    s3S.parts = [216, 8, 150, 118, 274, 242, 248, 262, -8, 150, 172, 274, 296, 240] ∧
    s4S.parts = [250, 8, 116, 118, 240, 242, 248, 266, -8, 116, 142, 240, 266, 240] := by
  decide

/-- **Per-seed arc parts at FAST_MIN** (ps). -/
theorem parts_fastMin :
    s1F.parts = [89, -3, 48, 47, 93, 92, 90, 94, 3, 48, 49, 93, 94, 93] ∧
    s2F.parts = [89, 2, 48, 47, 93, 92, 90, 87, -2, 48, 47, 93, 92, 88] ∧
    s3F.parts = [95, -3, 44, 49, 89, 94, 90, 92, 3, 44, 43, 89, 88, 93] ∧
    s4F.parts = [91, -3, 48, 49, 93, 94, 90, 94, 3, 48, 49, 93, 94, 93] := by
  decide

/-- **Flip windows per seed.** ArbCorners' `windows_exist_p10` (every condition can
flip at the p10 wire ratio 0.37) is identity-pin specific. With ustate's q on A5
the pulse conditions have `Af/As = 48/116 = 0.414 > 0.37`: no flip window at
k = 0.37 (S1, S2, S4). At the median k = 0.55 every condition of every seed
still has a window (largest ratio: S3's RT1 race, 95/216 = 0.440). -/
theorem windows_seed :
    ¬ (100 * 48 < 37 * 116) ∧
    (∀ p ∈ (s1S.parts.zip s1F.parts ++ s2S.parts.zip s2F.parts ++
            s3S.parts.zip s3F.parts ++ s4S.parts.zip s4F.parts),
       0 < p.1 → 100 * p.2 < 55 * p.1) ∧
    100 * 95 < 55 * 216 ∧ ¬ (100 * 95 < 37 * 216) := by
  decide

end Held

/-! ## §4 7e (bare cell): skew caps per seed -/

/-- The 7e corner of a seed: g1's r-pin arc from ugrant's r1 pin, g1's q-pin arc
`gQ`. (7e's `Arcs` has one O5 arc for both r pins; g1 = r1 ∧ q does not depend
on r2, so the r2 value is never read by a transport LUT.) -/
def cornerOf (a : PA) (h : a.Ok) : Corner := ⟨a.o6, a.gR1, a.gQ, by omega⟩

/-- **Skew caps per seed** (`ArbCorners.overlap` thresholds `max 0 (o6 − o5q)` for
r2 → r1, `max 0 (o5q − o6)` for r1 → r2). SLOW_MAX: S1/S3/S4 8 / 0, S2 0 / 24
(ArbCorners: 0 / 26). FAST_MIN: S1/S3/S4 0 / 3, S2 2 / 0 (ArbCorners: 3 / 0). -/
theorem caps_seed :
    (max 0 (s1S.o6 - s1S.gQ), max 0 (s1S.gQ - s1S.o6)) = ((8 : Int), (0 : Int)) ∧
    (max 0 (s2S.o6 - s2S.gQ), max 0 (s2S.gQ - s2S.o6)) = ((0 : Int), (24 : Int)) ∧
    (max 0 (s3S.o6 - s3S.gQ), max 0 (s3S.gQ - s3S.o6)) = ((8 : Int), (0 : Int)) ∧
    (max 0 (s4S.o6 - s4S.gQ), max 0 (s4S.gQ - s4S.o6)) = ((8 : Int), (0 : Int)) ∧
    (max 0 (s1F.o6 - s1F.gQ), max 0 (s1F.gQ - s1F.o6)) = ((0 : Int), (3 : Int)) ∧
    (max 0 (s2F.o6 - s2F.gQ), max 0 (s2F.gQ - s2F.o6)) = ((2 : Int), (0 : Int)) ∧
    (max 0 (s3F.o6 - s3F.gQ), max 0 (s3F.gQ - s3F.o6)) = ((0 : Int), (3 : Int)) ∧
    (max 0 (s4F.o6 - s4F.gQ), max 0 (s4F.gQ - s4F.o6)) = ((0 : Int), (3 : Int)) := by
  decide

section Handover
open ArbHandover

/-- **S1 at SLOW_MAX, r2 → r1 with request-fork skew σ**: an overlap exists iff
`σ > 116 + w`. ArbCorners' `skew_r2_to_r1_C` at its identity-pin SLOW_MAX
says "never". (S3, S4 have the same arcs here.) -/
theorem skew_r2_to_r1_s1_slow (w wfb : Int) (hw : 0 ≤ w) (hfb : 0 ≤ wfb)
    (t0 σ : Int) (r1 r2s r2g q g1 g2 : Sig)
    (Hs : LutOut3 stateF r1 r2s (fun s => q (s - wfb)) 124 124 124 124 124 124 q)
    (H_g1 : LutOut3 g1F r1 r2g (fun s => q (s - w)) 150 150 116 150 150 116 g1)
    (H_g2 : LutOut3 g2F r1 r2g (fun s => q (s - w)) 124 124 124 124 124 124 g2)
    (H_r1 : ∀ t, r1 t = true) (H_r2s : ∀ t, r2s t = decide (t < t0))
    (H_r2g : ∀ t, r2g t = decide (t < t0 + σ))
    (H_init : ∀ t, t < t0 → q t = false) :
    (∃ t, (g1 t && g2 t) = true) ↔ 116 + w < σ := by
  have h := skew_r2_to_r1_C (cornerOf s1S s1S_ok) w wfb hw hfb t0 σ r1 r2s r2g q g1 g2
    Hs H_g1 H_g2 H_r1 H_r2s H_r2g H_init
  rw [h]
  have e1 : (cornerOf s1S s1S_ok).o5q = 116 := by decide
  have e2 : (cornerOf s1S s1S_ok).o6 = 124 := by decide
  rw [e1, e2]; omega

/-- ... and r1 → r2 with skew: never at S1 SLOW_MAX (ArbCorners: iff σ > 96 + w). -/
theorem skew_r1_to_r2_s1_slow (w wfb : Int) (hw : 0 ≤ w) (hfb : 0 ≤ wfb)
    (t0 σ : Int) (r1s r1g r2 q g1 g2 : Sig)
    (Hs : LutOut3 stateF r1s r2 (fun s => q (s - wfb)) 124 124 124 124 124 124 q)
    (H_g1 : LutOut3 g1F r1g r2 (fun s => q (s - w)) 150 150 116 150 150 116 g1)
    (H_g2 : LutOut3 g2F r1g r2 (fun s => q (s - w)) 124 124 124 124 124 124 g2)
    (H_r2 : ∀ t, r2 t = true) (H_r1s : ∀ t, r1s t = decide (t < t0))
    (H_r1g : ∀ t, r1g t = decide (t < t0 + σ))
    (H_init : ∀ t, t < t0 → q t = true) :
    ∀ t, (g1 t && g2 t) = false := by
  have h := skew_r1_to_r2_C (cornerOf s1S s1S_ok) w wfb hw hfb t0 σ r1s r1g r2 q g1 g2
    Hs H_g1 H_g2 H_r2 H_r1s H_r1g H_init
  have e1 : (cornerOf s1S s1S_ok).o5q = 116 := by decide
  have e2 : (cornerOf s1S s1S_ok).o6 = 124 := by decide
  rw [e1, e2] at h
  intro t
  cases hb : (g1 t && g2 t)
  · rfl
  · exact absurd (h.1 ⟨t, hb⟩).1 (by decide)

end Handover

/-! ## §5 Rule J per seed, on 7g's run semantics -/

section RuleJ
open ArbA0Fork

/-- Rule J's early-minus-late with nextpnr's FLAT arcs (2 × 124 for ustate and
ugrant), everything else (routes, site pins) as in the delay set. -/
def flatJ (p : ArbA0Fork.Dl) : Int :=
  ((p.wSt + p.pSt + p.wQG + p.pQG + p.wGC + p.pGC : Nat) : Int) + 248 - (p.late : Nat)

theorem early_late_flat (p : ArbA0Fork.Dl) :
    ((p.early : Nat) : Int) - (p.late : Nat) = flatJ p + ((p.aSt + p.aG : Nat) : Int) - 248 := by
  unfold flatJ ArbA0Fork.Dl.early ArbA0Fork.Dl.late; omega

/-- **Client 1 against rule J's flat count, exactly**: every run is safe iff
`flatJ p ≥ 248 − (aSt + aG)`. The bias `248 − (aSt + aG)` is what rule J's flat
arcs get wrong: positive = optimistic (rule J passes routes that fail). -/
theorem client1_vs_flat {p : ArbA0Fork.Dl} {T0 : Nat} {a0 q g A : Nat → Bool}
    (R : ArbA0Fork.Run F1 G1 false p T0 a0 q g A) :
    (∀ t, A t = false) ↔ 248 - ((p.aSt + p.aG : Nat) : Int) ≤ flatJ p := by
  rw [client1_iff R]; have := early_late_flat p; omega

theorem client2_vs_flat {p : ArbA0Fork.Dl} {T0 : Nat} {a0 q g A : Nat → Bool}
    (R : ArbA0Fork.Run F2 G2 true p T0 a0 q g A) :
    (∀ t, A t = false) ↔ 248 - ((p.aSt + p.aG : Nat) : Int) ≤ flatJ p := by
  rw [client2_iff R]; have := early_late_flat p; omega

/-- The true SLOW_MAX early-side arcs (ustate O6 + ugrant O5 from q's pin) and
the bias of rule J's flat 248, per seed, client 1: S1/S3/S4 240 (optimistic by
8), S2 272 (conservative by 24). Client 2 (ugrant O6) is 248 in every seed:
exact. At FAST_MIN the true arcs are 93 / 88 / 93 / 93 (client 2: 90). -/
theorem ruleJ_seed :
    s1S.o6 + s1S.gQ = 240 ∧ s2S.o6 + s2S.gQ = 272 ∧ s3S.o6 + s3S.gQ = 240 ∧ s4S.o6 + s4S.gQ = 240 ∧
    248 - (s1S.o6 + s1S.gQ) = 8 ∧ 248 - (s2S.o6 + s2S.gQ) = -24 ∧
    248 - (s3S.o6 + s3S.gQ) = 8 ∧ 248 - (s4S.o6 + s4S.gQ) = 8 ∧
    2 * s1S.o6 = 248 ∧
    s1F.o6 + s1F.gQ = 93 ∧ s2F.o6 + s2F.gQ = 88 ∧ s3F.o6 + s3F.gQ = 93 ∧ s4F.o6 + s4F.gQ = 93 ∧
    2 * s1F.o6 = 90 := by
  decide

/-- **S1/S3/S4: rule J is 8 ps optimistic, exactly.** With the seed's true
SLOW_MAX arcs (`aSt = 124`, `aG = 116`), client 1 is safe iff `flatJ p ≥ 8`. -/
theorem ruleJ_A5_iff {p : ArbA0Fork.Dl} {T0 : Nat} {a0 q g A : Nat → Bool}
    (R : ArbA0Fork.Run F1 G1 false p T0 a0 q g A) (hS : p.aSt = 124) (hG : p.aG = 116) :
    (∀ t, A t = false) ↔ 8 ≤ flatJ p := by
  rw [client1_vs_flat R, hS, hG]; constructor <;> intro h <;> omega

/-- **S2: rule J is 24 ps conservative, exactly** (`aG = 148`, SLICEM A3). -/
theorem ruleJ_A3_iff {p : ArbA0Fork.Dl} {T0 : Nat} {a0 q g A : Nat → Bool}
    (R : ArbA0Fork.Run F1 G1 false p T0 a0 q g A) (hS : p.aSt = 124) (hG : p.aG = 148) :
    (∀ t, A t = false) ↔ -24 ≤ flatJ p := by
  rw [client1_vs_flat R, hS, hG]; constructor <;> intro h <;> omega

/-- A delay set with the S1/S3/S4 SLOW_MAX arcs that RAW rule J passes (flat
margin +7) and on which client 1 acknowledges early. -/
def pOpt : ArbA0Fork.Dl :=
  { c := 0, wSt := 0, pSt := 0, aSt := 124, wQf := 0, pQf := 0, wQG := 0, pQG := 0, aG := 116,
    wGC := 0, pGC := 0, wAC := 241, pAC := 0, aC := 124, wCf := 0, pCf := 0 }

/-- **The optimism is realised**: a run on `pOpt` exists (7g's `run_exists`), and
on every such run client 1's ack rises, although `flatJ pOpt = 7 ≥ 0`. -/
theorem ruleJ_optimistic_run :
    flatJ pOpt = 7 ∧ (∃ a0 q g A, ArbA0Fork.Run F1 G1 false pOpt 1 a0 q g A) ∧
    (∀ a0 q g A, ArbA0Fork.Run F1 G1 false pOpt 1 a0 q g A → ∃ t, A t = true) := by
  refine ⟨by decide, run_exists F1 G1 true pOpt 1 F1_hold F1_go G1_vals.1 (by decide)
    (by decide) (by decide), ?_⟩
  intro a0 q g A R
  apply Classical.byContradiction
  intro hc
  have hall : ∀ t, A t = false := fun t => by
    cases h : A t
    · rfl
    · exact absurd ⟨t, h⟩ hc
  have := (ruleJ_A5_iff R rfl rfl).1 hall
  have h7 : flatJ pOpt = 7 := by decide
  omega

/-- A delay set with the S2 SLOW_MAX arcs that raw rule J rejects (flat margin
−1) and on which every run is safe. -/
def pCons : ArbA0Fork.Dl :=
  { c := 0, wSt := 0, pSt := 0, aSt := 124, wQf := 0, pQf := 0, wQG := 0, pQG := 0, aG := 148,
    wGC := 0, pGC := 0, wAC := 249, pAC := 0, aC := 124, wCf := 0, pCf := 0 }

theorem ruleJ_conservative_run :
    flatJ pCons = -1 ∧ (∃ a0 q g A, ArbA0Fork.Run F1 G1 false pCons 1 a0 q g A) ∧
    (∀ a0 q g A, ArbA0Fork.Run F1 G1 false pCons 1 a0 q g A → ∀ t, A t = false) := by
  refine ⟨by decide, run_exists F1 G1 true pCons 1 F1_hold F1_go G1_vals.1 (by decide)
    (by decide) (by decide), ?_⟩
  intro a0 q g A R
  exact (ruleJ_A3_iff R rfl rfl).2 (by decide)

/-- **The GUARDED rule J still covers SLOW_MAX on every seed.** ArbCorners'
`ruleJ_guard_covers_slow` assumed true arcs ≥ 248, false for S1/S3/S4 (240).
The guard `1155·(L+124) < 772·(E+372)` already implies `L ≤ E + 124`, so any
true arc part `As ≥ 125` suffices. -/
theorem ruleJ_guard_covers_slow' (E L As : Int) (hE : 0 ≤ E) (hAs : 125 ≤ As)
    (H_RULEJ : 1155 * (L + 124) < 772 * (E + 372)) : 0 ≤ As + (E - L) := by omega

/-- ArbCorners' single-ratio `ruleJ_guard_covers_fast` needs `Af ≥ 87`; per seed
client 1 has 93 / 88 / 93 / 93 and client 2 has 90, so it applies to every seed
(still under its single wire ratio, which §6 removes). -/
theorem guard_fast_premise_seed :
    87 ≤ s1F.o6 + s1F.gQ ∧ 87 ≤ s2F.o6 + s2F.gQ ∧ 87 ≤ s3F.o6 + s3F.gQ ∧
    87 ≤ s4F.o6 + s4F.gQ ∧ 87 ≤ 2 * s1F.o6 := by decide

end RuleJ

/-! ## §6 Guarded rule J under PER-WIRE corner ratios

Each routed wire `w = (s, F)` has its SLOW_MAX delay `s` (ps) and its FAST_MIN
delay `F / d` (so `F` is in units of `1/d` ps), with its own ratio in the band

    H_WIRE_BAND :  a·s ≤ F ≤ b·s       (k_w = F/(d·s) ∈ [a/d, b/d]).

This replaces ArbCorners' H_WIRE_RATIO (one ratio for a margin's signed wire
sum). Physical fact: every routed pip/wire's fast/slow ratio lies in a measured
band (f1_compare on gcd: p10 0.37, p90 0.82); test by comparing per-net delays
of one route in the FAST_MIN and SLOW_MAX prjxray SDF GLS. The early wires sum
to `E` (slow), the late wires to `L`. The FAST_MIN margin (in 1/d ps) is
`Afd + ΣF_early − ΣF_late` with `Afd = d · (fast arc part)`. -/

section Band

abbrev Band (a b : Int) (w : Int × Int) : Prop := a * w.1 ≤ w.2 ∧ w.2 ≤ b * w.1

def sS : List (Int × Int) → Int
  | [] => 0
  | w :: ws => w.1 + sS ws

def sF : List (Int × Int) → Int
  | [] => 0
  | w :: ws => w.2 + sF ws

theorem band_sum (a b : Int) : ∀ ws : List (Int × Int), (∀ w ∈ ws, Band a b w) →
    a * sS ws ≤ sF ws ∧ sF ws ≤ b * sS ws
  | [], _ => by simp [sS, sF]
  | w :: ws, h => by
    have ih := band_sum a b ws (fun v hv => h v (List.mem_cons_of_mem _ hv))
    have hw := h w (by simp)
    unfold Band at hw
    simp only [sS, sF, Int.mul_add]
    omega

/-- **The exact per-route condition.** For a route whose early wires total `E`
and late wires `L` (SLOW_MAX), the FAST_MIN margin is non-negative for EVERY
per-wire ratio assignment in the band iff `Afd + a·E − b·L ≥ 0`: the worst case
is all early wires at the band's bottom and all late wires at its top
(attained already with one wire per side). -/
theorem perwire_exact (a b Afd E L : Int) (hab : a ≤ b) (hE : 0 ≤ E) (hL : 0 ≤ L) :
    (∀ es ls : List (Int × Int), sS es = E → sS ls = L →
        (∀ w ∈ es, Band a b w) → (∀ w ∈ ls, Band a b w) → 0 ≤ Afd + sF es - sF ls) ↔
      0 ≤ Afd + a * E - b * L := by
  constructor
  · intro h
    have h1 : a * E ≤ b * E := Int.mul_le_mul_of_nonneg_right hab hE
    have h2 : a * L ≤ b * L := Int.mul_le_mul_of_nonneg_right hab hL
    have := h [(E, a * E)] [(L, b * L)] (by simp [sS]) (by simp [sS])
      (by intro w hw; simp at hw; subst hw; exact ⟨Int.le_refl _, h1⟩)
      (by intro w hw; simp at hw; subst hw; exact ⟨h2, Int.le_refl _⟩)
    simpa [sF] using this
  · intro h es ls hes hls he hl
    have e1 := band_sum a b es he
    have e2 := band_sum a b ls hl
    subst hes hls
    omega

/-- **Uniform sufficient condition.** If the band is narrow enough,
`772·b ≤ 1155·a` (k_max/k_min ≤ 1155/772 ≈ 1.496), every guarded route with
`E ≥ E0` keeps a non-negative FAST_MIN margin under every per-wire assignment,
provided `1155·Afd + (1155·a − 772·b)·E0 ≥ 143963·b`. -/
theorem guard_band_covers (a b Afd E0 E L : Int) (hb : 0 ≤ b) (hnarrow : 772 * b ≤ 1155 * a)
    (hE0 : E0 ≤ E) (H_RULEJ : 1155 * (L + 124) < 772 * (E + 372))
    (hfloor : 143963 * b ≤ 1155 * Afd + (1155 * a - 772 * b) * E0) :
    0 ≤ Afd + a * E - b * L := by
  have g : 1155 * L ≤ 772 * E + 143963 := by omega
  have m1 : b * (1155 * L) ≤ b * (772 * E + 143963) := Int.mul_le_mul_of_nonneg_left g hb
  have m2 : (1155 * a - 772 * b) * E0 ≤ (1155 * a - 772 * b) * E :=
    Int.mul_le_mul_of_nonneg_left hE0 (by omega)
  rw [Int.mul_add, Int.mul_left_comm b 1155 L, Int.mul_left_comm b 772 E,
    Int.mul_comm b 143963] at m1
  rw [Int.sub_mul, Int.sub_mul, Int.mul_assoc, Int.mul_assoc, Int.mul_assoc,
    Int.mul_assoc] at m2
  rw [Int.sub_mul, Int.mul_assoc, Int.mul_assoc] at hfloor
  omega

/-- **Uniform necessary condition.** If the band is wider, `1155·a < 772·b`,
then for EVERY early-routing floor `E0` and every fast arc part there is a
route with `E ≥ E0` that passes the guard and whose worst per-wire FAST_MIN
margin is negative. -/
theorem guard_band_fails (a b Afd E0 : Int) (hb : 0 ≤ b) (hwide : 1155 * a < 772 * b) :
    ∃ E L, E0 ≤ E ∧ 0 ≤ E ∧ 0 ≤ L ∧ 1155 * (L + 124) < 772 * (E + 372) ∧
      Afd + a * E - b * L < 0 := by
  obtain ⟨E, hE⟩ : ∃ E : Int, E = max E0 0 + 1155 * max Afd 0 + 1 := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : Int, L = (772 * E + 143963) / 1155 := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by omega
  have g1 : 772 * E + 142809 ≤ 1155 * L := by omega
  have m1 : b * (772 * E + 142809) ≤ b * (1155 * L) := Int.mul_le_mul_of_nonneg_left g1 hb
  rw [Int.mul_add, Int.mul_left_comm b 1155 L, Int.mul_left_comm b 772 E,
    Int.mul_comm b 142809] at m1
  have m2 : 0 ≤ (772 * b - 1155 * a - 1) * E := Int.mul_nonneg (by omega) hE0
  rw [Int.sub_mul, Int.sub_mul, Int.mul_assoc, Int.mul_assoc, Int.one_mul] at m2
  have hb0 : 0 ≤ 142809 * b := by omega
  refine ⟨E, L, by omega, hE0, by omega, by omega, ?_⟩
  omega

/-- **So, per wire: guarded rule J covers FAST_MIN for all routes above a floor
`E0` only if the band is narrow** (`772·b ≤ 1155·a`). -/
theorem band_cover_needs_narrow (a b Afd E0 : Int) (ha : 0 ≤ a) (hab : a ≤ b)
    (H : ∀ E L, E0 ≤ E → 0 ≤ L → 1155 * (L + 124) < 772 * (E + 372) →
      ∀ es ls : List (Int × Int), sS es = E → sS ls = L →
        (∀ w ∈ es, Band a b w) → (∀ w ∈ ls, Band a b w) → 0 ≤ Afd + sF es - sF ls) :
    772 * b ≤ 1155 * a := by
  apply Classical.byContradiction
  intro hc
  obtain ⟨E, L, h1, hEpos, h2, h3, h4⟩ := guard_band_fails a b Afd E0 (by omega) (by omega)
  have := (perwire_exact a b Afd E L hab hEpos h2).1 (H E L h1 h2 h3)
  omega

/-- **The audit's counterexample (P3 row 2), as an instance.** Band [0.37, 0.82]
(`d = 100`), client 2's FAST_MIN arcs 90 ps (`Afd = 9000`), E = 600, L = 525:
the guard passes, E ≥ 114, the early wire at 0.37 (222 ps) and the late wire at
0.82 (430.5 ps) are in the band, and the FAST_MIN margin is −118.5 ps
(−11850 centi-ps). The single-ratio reading (k = 0.55) of the same route: +131.25. -/
theorem audit_cex :
    1155 * ((525 : Int) + 124) < 772 * (600 + 372) ∧ (114 : Int) ≤ 600 ∧
    Band 37 82 (600, 22200) ∧ Band 37 82 (525, 43050) ∧
    (9000 : Int) + sF [(600, 22200)] - sF [(525, 43050)] = -11850 ∧
    (9000 : Int) + 55 * (600 - 525) = 13125 := by
  decide

/-- The same route with S1/S3/S4's client-1 fast arcs (93 ps): −115.5 ps;
with S2's (88 ps): −120.5 ps. -/
theorem audit_cex_seeds :
    (9300 : Int) + 37 * 600 - 82 * 525 = -11550 ∧ (8800 : Int) + 37 * 600 - 82 * 525 = -12050 := by
  decide

/-- **The measured p10-p90 band is too wide for ANY floor**: 1155·37 < 772·82,
so `guard_band_fails` gives a failing guarded route above every `E0` (here 114). -/
theorem p10p90_fails (Afd : Int) :
    ∃ E L, 114 ≤ E ∧ 0 ≤ E ∧ 0 ≤ L ∧ 1155 * (L + 124) < 772 * (E + 372) ∧
      Afd + 37 * E - 82 * L < 0 :=
  guard_band_fails 37 82 Afd 114 (by decide) (by decide)

/-- Sanity: a single ratio `k = 1` (`a = b = d = 100`) with ArbCorners' premises
`E ≥ 114`, `Af ≥ 87` meets the sufficient condition, so `guard_band_covers`
contains ArbCorners' `ruleJ_guard_covers_fast` at k = 1; and the narrow band
[0.55, 0.82] needs a floor of E0 = 7948 ps for Af = 87 by this bound. -/
theorem band_examples :
    (772 * 100 ≤ 1155 * (100 : Int) ∧ 143963 * 100 ≤ 1155 * (8700 : Int) + (1155 * 100 - 772 * 100) * 114) ∧
    (772 * 82 ≤ 1155 * (55 : Int) ∧ 143963 * 82 ≤ 1155 * (8700 : Int) + (1155 * 55 - 772 * 82) * 7948 ∧
      ¬ (143963 * 82 ≤ 1155 * (8700 : Int) + (1155 * 55 - 772 * 82) * 7947)) := by
  decide

end Band

end Formal.Cells.ArbCornersPin
