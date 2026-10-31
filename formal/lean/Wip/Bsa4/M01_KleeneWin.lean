-- Bsa4 mutant M01 of Formal/Cells/KleeneWin.lean: one change, '0 1 421 1) false 419 1 421 ≠' -> '0 1 422 1) false 419 1 422 ≠'. Expected: FAIL.
import Formal.Cells.KleeneBox
import Formal.Cells.CElemStrict

/-!
# KleeneWin: per-edge X windows with their own split (no H_X_UNIFORM)

Probe Bxw (shard B), follow-up of `KleeneBox` (probe Bkx) and
`CElemStrict` (probe Bs). KleeneBox's edge forms assume **H_X_UNIFORM**:
every binary edge `T` is X on `[T - a, T + c)` with ONE split `(a, c)` for
every edge of every signal. Under it each setup and hold gains `w = a + c`,
strict at `w = 1`. The audit (P8 section 2) notes that this rests on the
uniform split and on `w = 1` tick being the grid minimum, not a measurement.
This file drops H_X_UNIFORM.

## Model (named hypotheses, all K3, time in ticks = ps)

* **H_X_EDGE** (per edge, replaces H_X_UNIFORM): each binary edge `T` of each
  signal has its OWN window `[T - a_T, T + c_T)`, with only `0 ≤ a_T + c_T`
  (a width is not negative; a single `a_T` or `c_T` may even be negative, a
  window that does not contain the binary reference edge). Outside its windows
  the signal is definite. Rise and fall, request and select, each edge of each
  pin: all independent. `ReqW R F aR cR aF cF` is the request (ctl_req,
  data enable) form; a select / index bit / data bit is `StabK v (S0 + cS0)
  (S1 - aS1)` (definite `v` between the end of its entry window and the
  start of its exit window, anything outside).
* All other hypotheses exactly as in KleeneBox / LibGapLatch / CElemStrict
  (H_PIN_READ with arbitrary read maps in the box, H_KLEENE_LUT on the real
  INITs, H_RESET; for the C-element H_TREE, H_MUX_KLEENE, H_IN_PHASES).
* **H_FB_WIN** (section 6, generalises CElemStrict's H_FB_PURE): the
  C-element's feedback pin at `t` reads the Kleene join of the root over
  `[t - D - wq, t - D]`: the cell's own output edge is seen at I2 with its
  own X window of width `wq` (the output crossing mid-rail at the pin). A
  leading part of the window is a smaller `D`. `wq = 0` is H_FB_PURE
  (`loopW_of_loop`).

## Results (headlines)

Each race condition gains `c(earlier edge) + a(later edge)` and nothing else:
the trailing half of the window of the edge that must come first, plus the
leading half of the window of the edge that must come after.

* `steer_win_exact` (bd_steer, iff): setup `S0 + Shi + (cS0 + aR) ≤ R + Rlo`,
  hold `F + Rhi + (cF + aS1) ≤ S1 + Slo`. `aS0`, `cS1`, `cR`, `aF` drop out.
* `join_win_exact` (bd_mux join, iff): the same against ctl_req.
* `muxn_win_exact` (bdc_muxn selected join, iff): per index bit `i`,
  `Ai0 + Ahi + (cAi0 + aCr) ≤ Cr + Clo`, `Cf + Chi + (cCf + aAi1) ≤ Ai1 + Alo`.
* `latch_win_exact` (bd_latch, iff): setup_pulse `+ (cOn + aOff)`,
  setup_data `+ (cD + aOff)`, hold `+ (cOff + aN)`.
* `cel_edges_iff`, `cel_env_iff` (every C-element cycle with `Facts`, iff):
  the own-feedback race `Tf + cf + D + ar ≤ Tr`; in B's terms
  `cf + dlmax + dwmax + ar ≤ dlmin + E`.
* `clean_iffW`, `box_iffW`, `cel_env_win_iff` (feedback pin with its own
  window `wq`, iff): `Tf + cf + D + wq + ar ≤ Tr`; in B's terms
  `cf + dlmax + dwmax + wq + ar ≤ dlmin + E`.
* Consequences: `steer_split_matters`: with EVERY edge's window of width 1,
  binary-edge equality is safe for one split and a 1-tick-strict margin is
  unsafe for another, so "+w, strict at w = 1" holds only under
  H_X_UNIFORM; `steer_win_uniform` recovers KleeneBox's form.

Counter-traces: inside every iff (the necessity halves reuse the binary
counter-traces of LibGapSteer / LibGapMux / LibGapMuxN / LibGapLatch through
the embedding, and CElemStrict's `hazard`; `hazardW` for the feedback
window); explicit: `steer_ct_split_x` (X on the unselected branch at a
margin that is strict by one tick in binary-edge times), `c2_fbwin_hazard`
(bd_c2 real INIT, `wq = 1`: CElemStrict's `strict_clean` point now reads X).
Non-vacuity: `steer_witness_W`, `join_witness_W`, `latch_witness_W`,
`loopW_exists`/`sim_loopW`, `c2_fbwin_clean`.

NOT covered: the values of the `a_T`, `c_T`, `wq` (no data; see
notes/B-kleene-win.md for a board test); windows that vary from one token to
the next on the same edge (each theorem is per token, so a per-token window
is covered, but the box quantifies only over read maps, not over windows);
bdc_muxn's unselected joins (`Cover`, binary only, as in KleeneBox); a
mid-rail select inside the mux tree beyond H_KLEENE_LUT; correlated corners.
-/

namespace Formal.Cells.KleeneWin
open Formal.Cells
open Formal.Cells.LibGapSteer (Rd Rd.const pulse Stable outK outK_def)
open Formal.Cells.KleeneBox (kb kb_inj kgate kgate_kb Supp StabK SpecK SteerSafeB steer_ok_K stabK_of
  LutEqK RestK JSpecK join_ok_K join_K_to_B unsel_definite MuxSafeK muxn_ok_K muxn_K_to_B)

/-! ## 1. Per-edge windows (H_X_EDGE) -/

/-- A request-like trace with binary edges `R` (rise) and `F` (fall), each
with its own X window: `[R - aR, R + cR)` and `[F - aF, F + cF)`. Definite 0
before the rise window and from the end of the fall window, definite 1
between the two windows, anything (X included) inside them. -/
def ReqW (R F aR cR aF cF : Int) (r : Int → K3) : Prop :=
  (∀ x, (x < R - aR ∨ F + cF ≤ x) → r x = .f) ∧ (∀ x, R + cR ≤ x → x < F - aF → r x = .t)

theorem reqW_supp {R F aR cR aF cF : Int} {r : Int → K3} (h : ReqW R F aR cR aF cF r) :
    Supp (R - aR) (F + cF) r := by
  intro x hx
  apply Classical.byContradiction; intro hn
  exact hx (h.1 x (by omega))

/-- The binary pulse over the outer window edges meets `ReqW` (only the
widths need to be non-negative). -/
theorem reqW_pulse (R F aR cR aF cF : Int) (hwR : 0 ≤ aR + cR) (hwF : 0 ≤ aF + cF) :
    ReqW R F aR cR aF cF (fun x => kb (pulse (R - aR) (F + cF) x)) := by
  refine ⟨fun x hx => ?_, fun x h1 h2 => ?_⟩
  · have : ¬ (R - aR ≤ x ∧ x < F + cF) := by omega
    simp [pulse, this]
  · have : R - aR ≤ x ∧ x < F + cF := by omega
    simp [pulse, this]

/-- A concrete trace with X on every window (used by the witnesses and the
counter-trace): 0, X on the rise window, 1, X on the fall window, 0. -/
def rE (R F aR cR aF cF : Int) (x : Int) : K3 :=
  if x < R - aR then .f else if x < R + cR then .x else if x < F - aF then .t
  else if x < F + cF then .x else .f

theorem rE_reqW (R F aR cR aF cF : Int) (h1 : 0 ≤ aR + cR) (h2 : R + cR ≤ F - aF) (h3 : 0 ≤ aF + cF) :
    ReqW R F aR cR aF cF (rE R F aR cR aF cF) := by
  refine ⟨fun x hx => ?_, fun x hx1 hx2 => ?_⟩
  · unfold rE
    repeat' split
    all_goals first | rfl | (exfalso; omega)
  · unfold rE
    repeat' split
    all_goals first | rfl | (exfalso; omega)

/-- The same shape as a select carrying `v = 1`: definite 1 between its
windows. -/
theorem rE_stab (S0 S1 aS0 cS0 aS1 cS1 : Int) (h1 : 0 ≤ aS0 + cS0) :
    StabK true (S0 + cS0) (S1 - aS1) (rE S0 S1 aS0 cS0 aS1 cS1) := by
  intro x hx1 hx2
  unfold rE
  repeat' split
  all_goals first | rfl | (exfalso; omega)

/-! ## 2. `bd_steer`, per-edge windows -/

/-- Box safety of a steer branch with per-edge windows on the request and on
the select. -/
def SteerW (b v : Bool) (Rlo Rhi Slo Shi R F aR cR aF cF S0 cS0 S1 aS1 : Int) : Prop :=
  ∀ pr ps : Rd, Rlo ≤ pr.lo → pr.hi ≤ Rhi → Slo ≤ ps.lo → ps.hi ≤ Shi →
    ∀ r s, ReqW R F aR cR aF cF r → StabK v (S0 + cS0) (S1 - aS1) s → SpecK b v pr ps r s

/-- **Headline (steer), per-edge windows, exact.** The setup gains
`cS0 + aR` (the select's entry window's trailing half, the request rise's
leading half); the hold gains `cF + aS1`. -/
theorem steer_win_exact (b v : Bool) (Rlo Rhi Slo Shi R F aR cR aF cF S0 cS0 S1 aS1 : Int)
    (hR : Rlo ≤ Rhi) (hS : Slo ≤ Shi) (hRF : R - aR < F + cF) (hwR : 0 ≤ aR + cR) (hwF : 0 ≤ aF + cF) :
    SteerW b v Rlo Rhi Slo Shi R F aR cR aF cF S0 cS0 S1 aS1 ↔
      (S0 + Shi + (cS0 + aR) ≤ R + Rlo ∧ F + Rhi + (cF + aS1) ≤ S1 + Slo) := by
  constructor
  · intro h
    have hB : SteerSafeB b v Rlo Rhi Slo Shi (R - aR) (F + cF) (S0 + cS0) (S1 - aS1) := by
      intro pr ps a1 a2 a3 a4 s hs t
      have := h pr ps a1 a2 a3 a4 _ _ (reqW_pulse R F aR cR aF cF hwR hwF) (stabK_of v _ _ s hs) t
      rw [outK_def, kgate_kb] at this
      exact kb_inj _ _ this
    have := (LibGapSteer.steer_box_exact b v Rlo Rhi Slo Shi (R - aR) (F + cF) (S0 + cS0) (S1 - aS1)
      hR hS hRF).mp hB
    omega
  · rintro ⟨h1, h2⟩ pr ps a1 a2 a3 a4 r s hr hs
    exact steer_ok_K b v pr ps (R - aR) (F + cF) (S0 + cS0) (S1 - aS1) r s (reqW_supp hr) hs
      (by omega) (by omega)

/-- H_X_UNIFORM is the special case: one split `(a, c)` everywhere gives
KleeneBox's `+ (a + c)` (`KleeneBox.steer_edges_K`). -/
theorem steer_win_uniform (b v : Bool) (Rlo Rhi Slo Shi R F S0 S1 a c : Int)
    (hR : Rlo ≤ Rhi) (hS : Slo ≤ Shi) (hRF : R < F) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    SteerW b v Rlo Rhi Slo Shi R F a c a c S0 c S1 a ↔
      (S0 + Shi + (a + c) ≤ R + Rlo ∧ F + Rhi + (a + c) ≤ S1 + Slo) := by
  rw [steer_win_exact b v _ _ _ _ R F a c a c S0 c S1 a hR hS (by omega) (by omega) (by omega)]
  omega

/-- **The split matters.** Every edge has a window of width exactly 1 in both
cases (select read in 500 ps, request in 300 ps). (i) The request's windows
inside its pulse (rise `(0, 1)`, fall `(1, 0)`) and the select's outside its
binary window (entry `cS0 = 0`, exit `aS1 = 0`): binary-edge EQUALITY on both
sides (`800 + 500 = 1000 + 300`, `3000 + 300 = 2800 + 500`) is safe. (ii) The
opposite split on the setup pair (`cS0 = aR = 1`): a setup margin that is
strict by one tick in binary-edge times (`800 + 500 < 1001 + 300`) is unsafe.
So KleeneBox's "+w, strict at w = 1" is neither necessary nor sufficient
without H_X_UNIFORM. -/
theorem steer_split_matters (b v : Bool) :
    SteerW b v 300 300 500 500 1000 3000 0 1 1 0 800 0 2800 0 ∧
    ((800 : Int) + 500 = 1000 + 300 ∧ (3000 : Int) + 300 = 2800 + 500) ∧
    ¬ SteerW b v 300 300 500 500 1001 3000 1 0 1 0 800 1 4500 1 ∧
    ((800 : Int) + 500 < 1001 + 300 ∧ (3000 : Int) + 300 < 4500 + 500) := by
  refine ⟨?_, by decide, ?_, by decide⟩
  · exact (steer_win_exact b v 300 300 500 500 1000 3000 0 1 1 0 800 0 2800 0 (by decide) (by decide)
      (by decide) (by decide) (by decide)).mpr (by decide)
  · rw [steer_win_exact b v 300 300 500 500 1001 3000 1 0 1 0 800 1 4500 1 (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    decide

/-- **Explicit counter-trace for (ii)**: request rises at 1001 with X on
`[1000, 1001)`, select (token `v = 1`) rises at 800 with X on `[800, 801)`;
read through 300 / 500 ps. Both traces meet H_X_EDGE. At 1300 the unselected
O5 (real INIT) reads X where the spec is definite 0. -/
theorem steer_ct_split_x :
    ReqW 1001 3000 1 0 1 0 (rE 1001 3000 1 0 1 0) ∧
    StabK true (800 + 1) (4500 - 1) (rE 800 4500 0 1 1 0) ∧
    outK false (rE 1001 3000 1 0 1 0 ((Rd.const 300).σ 1300)) (rE 800 4500 0 1 1 0 ((Rd.const 500).σ 1300))
      = .x ∧
    kgate (rE 1001 3000 1 0 1 0 ((Rd.const 300).σ 1300)) (true == false) = .f := by
  refine ⟨rE_reqW _ _ _ _ _ _ (by decide) (by decide) (by decide),
    rE_stab _ _ _ _ _ _ (by decide), by decide, by decide⟩

/-- **Non-vacuity (steer)**: a different split on every edge (request rise
`(2, 0)`, fall `(0, 3)`; select rise `(1, 1)`, fall `(0, 2)`), strict margins,
X on every window: the spec holds on both branches at every instant, and
O6 is definite 1 at 1400. -/
theorem steer_witness_W :
    ((500 : Int) + 600 + (1 + 2) ≤ 1000 + 200 ∧ (3000 : Int) + 400 + (3 + 0) ≤ 4000 + 300) ∧
    ReqW 1000 3000 2 0 0 3 (rE 1000 3000 2 0 0 3) ∧ StabK true (500 + 1) (4000 - 0) (rE 500 4000 1 1 0 2) ∧
    SpecK true true (Rd.const 300) (Rd.const 450) (rE 1000 3000 2 0 0 3) (rE 500 4000 1 1 0 2) ∧
    SpecK false true (Rd.const 300) (Rd.const 450) (rE 1000 3000 2 0 0 3) (rE 500 4000 1 1 0 2) ∧
    outK true (rE 1000 3000 2 0 0 3 ((Rd.const 300).σ 1400)) (rE 500 4000 1 1 0 2 ((Rd.const 450).σ 1400))
      = .t := by
  have hr := rE_reqW 1000 3000 2 0 0 3 (by decide) (by decide) (by decide)
  have hs := rE_stab 500 4000 1 1 0 2 (by decide)
  have hW : ∀ b, SteerW b true 200 400 300 600 1000 3000 2 0 0 3 500 1 4000 0 := fun b =>
    (steer_win_exact b true 200 400 300 600 1000 3000 2 0 0 3 500 1 4000 0 (by decide) (by decide)
      (by decide) (by decide) (by decide)).mpr (by decide)
  refine ⟨by decide, hr, hs, ?_, ?_, by decide⟩
  · exact hW true _ _ (by simp [Rd.const]) (by simp [Rd.const]) (by simp [Rd.const]) (by simp [Rd.const])
      _ _ hr hs
  · exact hW false _ _ (by simp [Rd.const]) (by simp [Rd.const]) (by simp [Rd.const]) (by simp [Rd.const])
      _ _ hr hs

/-! ## 3. `bd_mux` joins, per-edge windows -/

def JoinW (b v : Bool) (Rlo Rhi Clo Chi Slo Shi Qlo Qhi Cr Cf aCr cCr aCf cCf S0 cS0 S1 aS1 : Int) : Prop :=
  ∀ pr pc ps pq : Rd, Rlo ≤ pr.lo → pr.hi ≤ Rhi → Clo ≤ pc.lo → pc.hi ≤ Chi →
    Slo ≤ ps.lo → ps.hi ≤ Shi → Qlo ≤ pq.lo → pq.hi ≤ Qhi →
    ∀ r c s j : Int → K3, ReqW Cr Cf aCr cCr aCf cCf c → StabK v (S0 + cS0) (S1 - aS1) s →
      LutEqK b pr pc ps pq r c s j → RestK j → JSpecK b v pr pc pq r c j

/-- **Headline (mux join), per-edge windows, exact.** Setup `+ (cS0 + aCr)`,
hold `+ (cCf + aS1)`. The request (x_req / y_req) and FEEDBACK pins drop out,
whatever their windows. -/
theorem join_win_exact (b v : Bool) (Rlo Rhi Clo Chi Slo Shi Qlo Qhi Cr Cf aCr cCr aCf cCf S0 cS0 S1 aS1 : Int)
    (hR : Rlo ≤ Rhi) (hC : Clo ≤ Chi) (hS : Slo ≤ Shi) (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi)
    (hCF : Cr - aCr < Cf + cCf) (hwR : 0 ≤ aCr + cCr) (hwF : 0 ≤ aCf + cCf) (hRst : 0 ≤ Cr - aCr + Clo) :
    JoinW b v Rlo Rhi Clo Chi Slo Shi Qlo Qhi Cr Cf aCr cCr aCf cCf S0 cS0 S1 aS1 ↔
      (S0 + Shi + (cS0 + aCr) ≤ Cr + Clo ∧ Cf + Chi + (cCf + aS1) ≤ S1 + Slo) := by
  constructor
  · intro h
    have := (LibGapMux.join_box_exact b v Rlo Rhi Clo Chi Slo Shi Qlo Qhi (Cr - aCr) (Cf + cCf)
      (S0 + cS0) (S1 - aS1) hR hC hS hQ1 hQ hCF hRst).mp
      (join_K_to_B b v _ _ _ _ _ _ _ _ _ _ _ _ _ (reqW_pulse Cr Cf aCr cCr aCf cCf hwR hwF) h)
    omega
  · rintro ⟨h1, h2⟩ pr pc ps pq _ _ a3 a4 a5 a6 _ _ r c s j hc' hs hL _
    exact join_ok_K b v pr pc ps pq (Cr - aCr) (Cf + cCf) (S0 + cS0) (S1 - aS1) r c s j
      (reqW_supp hc') hs hL (by omega) (by omega)

/-- Non-vacuity (join): ctl_req rise `(0, 2)`, fall `(1, 1)`; select rise
`(2, 1)`, fall `(1, 0)`; strict margins; the run `LibGapLatch.run` with the
REAL uj0 INIT (unselected, x_req waiting) is definite 0 at every instant,
and the selected uj1 is definite 1 at 1400. -/
def jfW (b : Bool) (t : Int) (q : K3) : K3 :=
  LibGapMux.jK b .t (rE 1000 3000 0 2 1 1 (t - 300)) (rE 500 4000 2 1 1 0 (t - 450)) q

def wjW (b : Bool) : Int → K3 := LibGapLatch.run (jfW b) .f 100 (by decide)

theorem wjW_luteq (b : Bool) :
    LutEqK b (Rd.const 0) (Rd.const 300) (Rd.const 450) (Rd.const 100) (fun _ => .t)
      (rE 1000 3000 0 2 1 1) (rE 500 4000 2 1 1 0) (wjW b) := by
  intro t ht
  exact LibGapLatch.run_eq _ _ 100 (by decide) t ht

theorem join_witness_W :
    ((500 : Int) + 450 + (1 + 0) ≤ 1000 + 300 ∧ (3000 : Int) + 300 + (1 + 1) ≤ 4000 + 450) ∧
    ReqW 1000 3000 0 2 1 1 (rE 1000 3000 0 2 1 1) ∧ StabK true (500 + 1) (4000 - 1) (rE 500 4000 2 1 1 0) ∧
    (∀ t, wjW false t = .f) ∧ wjW true 1400 = .t := by
  have hc := rE_reqW 1000 3000 0 2 1 1 (by decide) (by decide) (by decide)
  have hs := rE_stab 500 4000 2 1 1 0 (by decide)
  have hW : ∀ b, JoinW b true 0 0 300 300 450 450 100 100 1000 3000 0 2 1 1 500 1 4000 1 := fun b =>
    (join_win_exact b true 0 0 300 300 450 450 100 100 1000 3000 0 2 1 1 500 1 4000 1 (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mpr
      (by decide)
  have hRst : ∀ b, RestK (wjW b) := fun b t ht => LibGapLatch.run_neg _ _ 100 (by decide) t ht
  have S0 := hW false _ _ _ _ (by simp [Rd.const]) (by simp [Rd.const]) (by simp [Rd.const])
    (by simp [Rd.const]) (by simp [Rd.const]) (by simp [Rd.const]) (by simp [Rd.const]) (by simp [Rd.const])
    _ _ _ _ hc hs (wjW_luteq false) (hRst false)
  have S1 := hW true _ _ _ _ (by simp [Rd.const]) (by simp [Rd.const]) (by simp [Rd.const])
    (by simp [Rd.const]) (by simp [Rd.const]) (by simp [Rd.const]) (by simp [Rd.const]) (by simp [Rd.const])
    _ _ _ _ hc hs (wjW_luteq true) (hRst true)
  refine ⟨by decide, hc, hs, unsel_definite false true (by decide) _ _ _ (by simp [Rd.const]) _ _ _ S0
    (hRst false), ?_⟩
  rw [S1 1400 (by decide)]
  decide

/-! ## 4. `bdc_muxn` selected join, per-edge windows on ctl_req and both index bits -/

open Formal.Cells.LibGapMuxN (SelCond)

/-- **Headline (bdc_muxn selected join), per-edge windows, exact.** Index bit
`A`'s entry window `cA0`, exit `aA1`; bit `B`'s `cB0`, `aB1`; ctl_req's rise
`aCr`, fall `cCf`. -/
theorem muxn_win_exact (k : Nat) (hk : k < 3)
    (Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi Cr Cf aCr cCr aCf cCf A0 cA0 A1 aA1 B0 cB0 B1 aB1 : Int)
    (hRb : Rlo ≤ Rhi) (hDb : Dlo ≤ Dhi) (hCb : Clo ≤ Chi) (hAb : Alo ≤ Ahi) (hBb : Blo ≤ Bhi)
    (hQ1 : 1 ≤ Qlo) (hQb : Qlo ≤ Qhi) (hCF : Cr - aCr < Cf + cCf) (hwR : 0 ≤ aCr + cCr) (hwF : 0 ≤ aCf + cCf)
    (hRst : 0 ≤ Cr - aCr + Clo + Dlo) :
    MuxSafeK k Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi
      (A0 + cA0) (A1 - aA1) (B0 + cB0) (B1 - aB1) (ReqW Cr Cf aCr cCr aCf cCf) ↔
    (A0 + Ahi + (cA0 + aCr) ≤ Cr + Clo ∧ Cf + Chi + (cCf + aA1) ≤ A1 + Alo ∧
      B0 + Bhi + (cB0 + aCr) ≤ Cr + Clo ∧ Cf + Chi + (cCf + aB1) ≤ B1 + Blo) := by
  constructor
  · intro h
    have := (LibGapMuxN.sel_box_exact (k := k) (hk := hk) (Rlo := Rlo) (Rhi := Rhi) (Dlo := Dlo) (Dhi := Dhi)
      (Clo := Clo) (Chi := Chi) (Alo := Alo) (Ahi := Ahi) (Blo := Blo) (Bhi := Bhi) (Qlo := Qlo) (Qhi := Qhi)
      (Cr := Cr - aCr) (Cf := Cf + cCf) (hRb := hRb) (hDb := hDb) (hCb := hCb) (hAb := hAb) (hBb := hBb)
      (hQ1 := hQ1) (hQb := hQb) (hCF := hCF) (hRst := hRst)
      (A0 := A0 + cA0) (A1 := A1 - aA1) (B0 := B0 + cB0) (B1 := B1 - aB1)).mp
      (muxn_K_to_B k hk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (reqW_pulse Cr Cf aCr cCr aCf cCf hwR hwF) h)
    unfold SelCond at this
    omega
  · intro hcond pr pd pc p0 p1 pq i1 i2 i3 i4 i5 i6 r cc s0 s1 D j hce
    exact muxn_ok_K k hk Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi (Cr - aCr) (Cf + cCf)
      (A0 + cA0) (A1 - aA1) (B0 + cB0) (B1 - aB1) (by unfold SelCond; omega)
      pr pd pc p0 p1 pq i1 i2 i3 i4 i5 i6 r cc s0 s1 D j (reqW_supp hce)

/-! ## 5. `bd_latch`, per-edge windows -/

/-- **Headline (bd_latch), per-edge windows, exact.** Enable binary edges
`Ton` (window end `cOn`; its leading half is irrelevant: the enable may be
anything before it is definite 1) and `Toff` (window `[Toff - aOff, Toff + cOff)`);
data edge `Td` (window end `cD`), next data `Tnew` (window start `aN`).
setup_pulse gains `cOn + aOff`, setup_data `cD + aOff`, hold `cOff + aN`. -/
theorem latch_win_exact (v : Bool) (Ton cOn Toff aOff cOff Td cD Tnew aN Dlo Dhi Elo Ehi Qlo Qhi : Int)
    (hD : Dlo ≤ Dhi) (hE : Elo ≤ Ehi) (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi)
    (hAB : Ton + cOn ≤ Toff - aOff) (hwOff : 0 ≤ aOff + cOff) (H_T0 : 0 ≤ Ton + cOn + Elo) :
    LibGapLatch.SafeBox v (Ton + cOn) (Toff - aOff) (Toff + cOff) (Td + cD) (Tnew - aN)
        Dlo Dhi Elo Ehi Qlo Qhi ↔
      (Ton + Ehi + Qhi + (cOn + aOff) ≤ Toff + Elo ∧ Td + Dhi + Qhi + (cD + aOff) ≤ Toff + Elo ∧
        Toff + Ehi + (cOff + aN) ≤ Tnew + Dlo) := by
  rw [LibGapLatch.box_exact v _ _ _ _ _ _ _ _ _ _ _ hD hE hQ1 hQ hAB (by omega) H_T0]; omega

/-- Non-vacuity (latch): non-uniform split `Ton = 1999, cOn = 1`;
`Toff = 3301, aOff = 1, cOff = 0`; `Td = 998, cD = 2`; `Tnew = 3803, aN = 2`.
These are exactly LibGapLatch's witness windows `A = 2000, B = 3300,
C = 3301, Td = 1000, Tn = 3801`, all three conditions hold (setup_pulse
with equality), the box safety holds, and LibGapLatch's run meets every
trace hypothesis (`witness_hyps`) and writes (`witness_run`). -/
theorem latch_witness_W :
    ((1999 : Int) + 1 = 2000 ∧ (3301 : Int) - 1 = 3300 ∧ (3301 : Int) + 0 = 3301 ∧
      (998 : Int) + 2 = 1000 ∧ (3803 : Int) - 2 = 3801) ∧
    ((1999 : Int) + 800 + 900 + (1 + 1) ≤ 3301 + 400 ∧ (998 : Int) + 700 + 900 + (2 + 1) ≤ 3301 + 400 ∧
      (3301 : Int) + 800 + (0 + 2) ≤ 3803 + 300) ∧
    LibGapLatch.SafeBox true (1999 + 1) (3301 - 1) (3301 + 0) (998 + 2) (3803 - 2) 300 700 400 800 300 900 ∧
    LibGapLatch.DStab true 1000 3801 (LibGapLatch.dAdv true 1000 3801) ∧
    LibGapLatch.EnTok 2000 3300 3301 (LibGapLatch.eAdv 2000 3300 3301) := by
  refine ⟨by decide, by decide, ?_, LibGapLatch.witness_hyps.1, LibGapLatch.witness_hyps.2.1⟩
  exact (latch_win_exact true 1999 1 3301 1 0 998 2 3803 2 300 700 400 800 300 900 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).mpr (by decide)

/-! ## 6. The C-element own-feedback race, per-edge windows (`CElemStrict`'s model)

Nat time. The follow pin's binary edge `Tf` has window `[Tf - af, Tf + cf)`,
so CElemStrict's `tb = Tf - af`, `wb = af + cf`; the release pin's binary
edge `Tr` has window `[Tr - ar, Tr + cr)`, `s = Tr - ar`, `wa = ar + cr`. -/

open Formal.Cells.CElemStrict (phase edge Facts Spec Loop SafeBox clean_iff box_iff ofBool_ne_x ofBool_inj
  c2Cycle c2F c2_all latF latch_facts)

/-- **Headline (C-element race), per-edge windows, exact.** For every loop
behaviour: one clean edge iff `Tf + cf + D + ar ≤ Tr`. `af` and `cr` drop
out. -/
theorem cel_edges_iff {ι : Type} {F : ι → K3 → K3} {I0 IX I1 RX R1 : ι} {v n : Bool}
    {Tf af cf Tr ar cr D : Nat} {i : Nat → ι} {qp G : Nat → K3}
    (L : Loop F I0 IX I1 RX R1 v (Tf - af) (af + cf) (Tr - ar) (ar + cr) D i qp G)
    (H : Facts F I0 IX I1 RX R1 v n) (hD : 1 ≤ D) (haf : af ≤ Tf) (har : ar ≤ Tr)
    (hord : Tf + cf ≤ Tr - ar) :
    Spec v n (Tf - af) (af + cf) G ↔ Tf + cf + D + ar ≤ Tr := by
  rw [clean_iff L H hD (by omega)]; omega

/-- **B's race with per-edge windows.** Loop delay `D ∈ [Dlo, dlmax + dwmax]`,
the release pin's binary edge as early as `Tf + dlmin + E` (B's H_ACK from the
follow pin's binary edge). Universally safe iff
`cf + dlmax + dwmax + ar ≤ dlmin + E`. -/
theorem cel_env_iff {ι : Type} {F : ι → K3 → K3} {I0 IX I1 RX R1 : ι} {v n : Bool}
    (H : Facts F I0 IX I1 RX R1 v n) {Tf af cf ar cr Dlo dlmin dlmax dwmax E : Nat}
    (hlo : 1 ≤ Dlo) (hbox : Dlo ≤ dlmax + dwmax) (haf : af ≤ Tf) (hord : cf + ar ≤ dlmin + E) :
    SafeBox F I0 IX I1 RX R1 v n (Tf - af) (af + cf) (ar + cr) Dlo (dlmax + dwmax) (Tf + dlmin + E - ar) ↔
      cf + dlmax + dwmax + ar ≤ dlmin + E := by
  rw [box_iff H hlo hbox (by omega)]; omega

/-! ## 7. The feedback pin with its own X window (H_FB_WIN) -/

/-- The feedback pin's read at loop delay `d`: the root `d` ticks ago (the
held value `v` before time 0). -/
def rdG (v : Bool) (G : Nat → K3) (t d : Nat) : K3 := if t < d then K3.ofBool v else G (t - d)

/-- The feedback pin with a window of width `wq`: Kleene join of the root's
values over `[t - D - wq, t - D]` (definite only if they all agree). -/
def winRd (v : Bool) (G : Nat → K3) (t D : Nat) : Nat → K3
  | 0 => rdG v G t D
  | k + 1 => K3.join (winRd v G t D k) (rdG v G t (D + (k + 1)))

theorem winRd_all (P : K3 → Prop) (hP : ∀ a b, P a → P b → P (K3.join a b)) (v : Bool) (G : Nat → K3)
    (t D : Nat) : ∀ wq, (∀ k, k ≤ wq → P (rdG v G t (D + k))) → P (winRd v G t D wq)
  | 0, h => h 0 (Nat.le_refl _)
  | k + 1, h => hP _ _ (winRd_all P hP v G t D k (fun j hj => h j (by omega))) (h (k + 1) (Nat.le_refl _))

theorem join_vx (a b c : K3) (hb : b = c ∨ b = K3.x) : K3.join a b = c ∨ K3.join a b = K3.x := by
  unfold K3.join
  split
  · next h => rw [h]; exact hb
  · exact Or.inr rfl

theorem winRd_last (v : Bool) (G : Nat → K3) (t D : Nat) (c : K3) : ∀ wq,
    (rdG v G t (D + wq) = c ∨ rdG v G t (D + wq) = K3.x) → (winRd v G t D wq = c ∨ winRd v G t D wq = K3.x)
  | 0, h => h
  | _ + 1, h => join_vx _ _ _ h

theorem closed_eq (c : K3) : ∀ a b : K3, a = c → b = c → K3.join a b = c := by
  intro a b ha hb; subst ha; subst hb; simp [K3.join]

theorem closed_vx (c : K3) : ∀ a b : K3, (a = c ∨ a = K3.x) → (b = c ∨ b = K3.x) →
    (K3.join a b = c ∨ K3.join a b = K3.x) := fun a b _ hb => join_vx a b c hb

/-- The loop's gate relations with H_FB_WIN in place of H_FB_PURE. -/
structure LoopW {ι : Type} (F : ι → K3 → K3) (I0 IX I1 RX R1 : ι) (v : Bool)
    (tb wb s wa D wq : Nat) (i : Nat → ι) (qp G : Nat → K3) : Prop where
  H_TREE : ∀ t, G t = F (i t) (qp t)
  H_FB_WIN : ∀ t, qp t = winRd v G t D wq
  H_IN_PHASES : ∀ t, i t = phase I0 IX I1 RX R1 tb wb s wa t

/-- `wq = 0` is CElemStrict's loop. -/
theorem loopW_of_loop {ι : Type} {F : ι → K3 → K3} {I0 IX I1 RX R1 : ι} {v : Bool}
    {tb wb s wa D : Nat} {i : Nat → ι} {qp G : Nat → K3}
    (L : Loop F I0 IX I1 RX R1 v tb wb s wa D i qp G) : LoopW F I0 IX I1 RX R1 v tb wb s wa D 0 i qp G :=
  { H_TREE := L.H_TREE, H_FB_WIN := fun t => by rw [L.H_FB_PURE]; rfl, H_IN_PHASES := L.H_IN_PHASES }

section genericW
variable {ι : Type} {F : ι → K3 → K3} {I0 IX I1 RX R1 : ι} {v n : Bool}
  {tb wb s wa D wq : Nat} {i : Nat → ι} {qp G : Nat → K3}

theorem prefix_okW (L : LoopW F I0 IX I1 RX R1 v tb wb s wa D wq i qp G)
    (H : Facts F I0 IX I1 RX R1 v n) (hD : 1 ≤ D) :
    ∀ t, t < s → G t = edge v n tb wb t := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro hts
    have hread : ∀ k, rdG v G t (D + k) =
        (if t < D + k then K3.ofBool v else edge v n tb wb (t - (D + k))) := by
      intro k
      unfold rdG
      by_cases h : t < D + k
      · simp only [h, ↓reduceIte]
      · simp only [h, ↓reduceIte]; exact ih _ (by omega) (by omega)
    rw [L.H_TREE, L.H_IN_PHASES, L.H_FB_WIN]
    unfold phase
    by_cases h1 : t < tb
    · have hq : winRd v G t D wq = K3.ofBool v := by
        apply winRd_all (· = K3.ofBool v) (closed_eq _)
        intro k _
        rw [hread]
        by_cases h : t < D + k
        · simp only [h, ↓reduceIte]
        · simp only [h, ↓reduceIte, edge, show t - (D + k) < tb by omega]
      simp only [h1, ↓reduceIte, edge, hq]; exact H.init
    · by_cases h2 : t < tb + wb
      · have hq : winRd v G t D wq = K3.ofBool v ∨ winRd v G t D wq = K3.x := by
          apply winRd_all (fun a => a = K3.ofBool v ∨ a = K3.x) (closed_vx _)
          intro k _
          rw [hread]
          by_cases h : t < D + k
          · simp only [h, ↓reduceIte]; simp
          · simp only [h, ↓reduceIte]
            unfold edge
            by_cases h4 : t - (D + k) < tb
            · simp only [h4, ↓reduceIte]; simp
            · simp only [h4, ↓reduceIte, show t - (D + k) < tb + wb by omega]; simp
        simp only [h1, h2, ↓reduceIte, edge]
        rcases hq with h | h <;> rw [h]
        · exact H.win_v
        · exact H.win_x
      · simp only [h1, h2, hts, ↓reduceIte, edge]; exact H.follow _

/-- **Clean** if the release pin starts moving no earlier than the tick the
feedback pin's own window has closed: `tb + D + wq + wb ≤ s`. -/
theorem cleanW (L : LoopW F I0 IX I1 RX R1 v tb wb s wa D wq i qp G)
    (H : Facts F I0 IX I1 RX R1 v n) (hD : 1 ≤ D) (hrace : tb + D + wq + wb ≤ s) :
    Spec v n tb wb G := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    by_cases hts : t < s
    · exact prefix_okW L H hD t hts
    · rw [L.H_TREE, L.H_IN_PHASES, L.H_FB_WIN]
      have hq : winRd v G t D wq = K3.ofBool n := by
        apply winRd_all (· = K3.ofBool n) (closed_eq _)
        intro k hk
        unfold rdG
        simp only [show ¬ t < D + k by omega, ↓reduceIte]
        rw [ih _ (by omega)]
        simp only [edge, show ¬ t - (D + k) < tb by omega, show ¬ t - (D + k) < tb + wb by omega,
          ↓reduceIte]
      simp only [phase, edge, show ¬ t < tb by omega, show ¬ t < tb + wb by omega, hts, ↓reduceIte, hq]
      by_cases h5 : t < s + wa
      · simp only [h5, ↓reduceIte]; exact H.holdX
      · simp only [h5, ↓reduceIte]; exact H.hold1

/-- **Hazard** if the release pin starts moving while the feedback pin's
window is still open (`s < tb + D + wq + wb`): the root at `s` is not `n`. -/
theorem hazardW (L : LoopW F I0 IX I1 RX R1 v tb wb s wa D wq i qp G)
    (H : Facts F I0 IX I1 RX R1 v n) (hD : 1 ≤ D) (hord : tb + wb ≤ s)
    (hrace : s < tb + D + wq + wb) :
    G s ≠ K3.ofBool n ∧ edge v n tb wb s = K3.ofBool n := by
  have hspec : edge v n tb wb s = K3.ofBool n := by
    simp only [edge, show ¬ s < tb by omega, show ¬ s < tb + wb by omega, ↓reduceIte]
  refine ⟨?_, hspec⟩
  rw [L.H_TREE, L.H_IN_PHASES, L.H_FB_WIN]
  simp only [phase, show ¬ s < tb by omega, show ¬ s < tb + wb by omega, Nat.lt_irrefl, ↓reduceIte]
  have hq : winRd v G s D wq = K3.ofBool v ∨ winRd v G s D wq = K3.x := by
    apply winRd_last
    unfold rdG
    by_cases h : s < D + wq
    · simp only [h, ↓reduceIte]; simp
    · simp only [h, ↓reduceIte]
      rw [prefix_okW L H hD (s - (D + wq)) (by omega)]
      unfold edge
      by_cases h4 : s - (D + wq) < tb
      · simp only [h4, ↓reduceIte]; simp
      · simp only [h4, ↓reduceIte, show s - (D + wq) < tb + wb by omega]; simp
  have hn : K3.ofBool v ≠ K3.ofBool n := fun h => H.ne (ofBool_inj h)
  by_cases h5 : s < s + wa
  · simp only [h5, ↓reduceIte]
    rcases hq with h | h <;> rw [h]
    · rw [H.hzXv]; exact (ofBool_ne_x n).symm
    · rw [H.hzXX]; exact (ofBool_ne_x n).symm
  · simp only [h5, ↓reduceIte]
    rcases hq with h | h <;> rw [h]
    · rw [H.hz1v]; exact hn
    · rw [H.hz1X]; exact (ofBool_ne_x n).symm

/-- **Exact, feedback window included.** -/
theorem clean_iffW (L : LoopW F I0 IX I1 RX R1 v tb wb s wa D wq i qp G)
    (H : Facts F I0 IX I1 RX R1 v n) (hD : 1 ≤ D) (hord : tb + wb ≤ s) :
    Spec v n tb wb G ↔ tb + D + wq + wb ≤ s := by
  constructor
  · intro hs
    apply Classical.byContradiction; intro hlt
    have ⟨h1, h2⟩ := hazardW L H hD hord (by omega)
    exact h1 (by rw [hs s]; exact h2)
  · exact cleanW L H hD

end genericW

/-! ### Non-vacuity: a simulator for H_FB_WIN -/

def rdP (v : Bool) (t e : Nat) (g : (u : Nat) → u < t → K3) : K3 :=
  if h : t < e + 1 then K3.ofBool v else g (t - (e + 1)) (by omega)

def winP (v : Bool) (t d : Nat) (g : (u : Nat) → u < t → K3) : Nat → K3
  | 0 => rdP v t d g
  | k + 1 => K3.join (winP v t d g k) (rdP v t (d + (k + 1)) g)

/-- The root of the loop with loop delay `d + 1` and feedback window `wq`. -/
def simGW {ι : Type} (F : ι → K3 → K3) (inp : Nat → ι) (v : Bool) (d wq : Nat) (t : Nat) : K3 :=
  F (inp t) (winP v t d (fun u (_ : u < t) => simGW F inp v d wq u) wq)
termination_by t
decreasing_by assumption

theorem simGW_eq {ι : Type} (F : ι → K3 → K3) (inp : Nat → ι) (v : Bool) (d wq t : Nat) :
    simGW F inp v d wq t = F (inp t) (winP v t d (fun u _ => simGW F inp v d wq u) wq) := by
  rw [simGW]

theorem rdP_eq (v : Bool) (G : Nat → K3) (t e : Nat) :
    rdP v t e (fun u _ => G u) = rdG v G t (e + 1) := by
  unfold rdP rdG
  by_cases h : t < e + 1 <;> simp [h]

theorem winP_eq (v : Bool) (G : Nat → K3) (t d : Nat) :
    ∀ k, winP v t d (fun u _ => G u) k = winRd v G t (d + 1) k
  | 0 => rdP_eq v G t d
  | k + 1 => by
    simp only [winP, winRd]
    rw [winP_eq v G t d k, rdP_eq, show d + (k + 1) + 1 = d + 1 + (k + 1) by omega]

theorem sim_loopW {ι : Type} (F : ι → K3 → K3) (inp : Nat → ι) (v : Bool) (d wq : Nat)
    {I0 IX I1 RX R1 : ι} {tb wb s wa : Nat} (hi : ∀ t, inp t = phase I0 IX I1 RX R1 tb wb s wa t) :
    LoopW F I0 IX I1 RX R1 v tb wb s wa (d + 1) wq inp (fun t => winRd v (simGW F inp v d wq) t (d + 1) wq)
      (simGW F inp v d wq) where
  H_TREE := by intro t; rw [simGW_eq, winP_eq]
  H_FB_WIN := fun _ => rfl
  H_IN_PHASES := hi

theorem loopW_exists {ι : Type} (F : ι → K3 → K3) (I0 IX I1 RX R1 : ι) (v : Bool)
    (tb wb s wa D wq : Nat) (hD : 1 ≤ D) :
    ∃ i qp G, LoopW F I0 IX I1 RX R1 v tb wb s wa D wq i qp G := by
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
  exact ⟨_, _, _, sim_loopW F (phase I0 IX I1 RX R1 tb wb s wa) v d wq (fun _ => rfl)⟩

/-- Universally safe over a box: every loop delay `D ∈ [Dlo, Dhi]`, every
feedback window `wq ≤ Wq`, every release start `s ≥ slo`, every behaviour. -/
def SafeBoxW {ι : Type} (F : ι → K3 → K3) (I0 IX I1 RX R1 : ι) (v n : Bool)
    (tb wb wa Dlo Dhi Wq slo : Nat) : Prop :=
  ∀ D wq s, Dlo ≤ D → D ≤ Dhi → wq ≤ Wq → slo ≤ s →
    ∀ i qp G, LoopW F I0 IX I1 RX R1 v tb wb s wa D wq i qp G → Spec v n tb wb G

theorem box_iffW {ι : Type} {F : ι → K3 → K3} {I0 IX I1 RX R1 : ι} {v n : Bool}
    (H : Facts F I0 IX I1 RX R1 v n) {tb wb wa Dlo Dhi Wq slo : Nat}
    (hlo : 1 ≤ Dlo) (hbox : Dlo ≤ Dhi) (hord : tb + wb ≤ slo) :
    SafeBoxW F I0 IX I1 RX R1 v n tb wb wa Dlo Dhi Wq slo ↔ tb + Dhi + Wq + wb ≤ slo := by
  constructor
  · intro hs
    obtain ⟨i, qp, G, L⟩ := loopW_exists F I0 IX I1 RX R1 v tb wb slo wa Dhi Wq (by omega)
    exact (clean_iffW L H (by omega) hord).1
      (hs Dhi Wq slo hbox (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) i qp G L)
  · intro hr D wq s h1 h2 h3 h4 i qp G L
    exact cleanW L H (by omega) (by omega)

/-- **Headline (C-element race, every window individual).** Follow pin edge
`Tf` with window end `cf`, release pin edge as early as `Tf + dlmin + E` with
window start `ar`, loop delay up to `dlmax + dwmax`, feedback pin window up to
`Wq`: universally safe iff `cf + dlmax + dwmax + Wq + ar ≤ dlmin + E`. -/
theorem cel_env_win_iff {ι : Type} {F : ι → K3 → K3} {I0 IX I1 RX R1 : ι} {v n : Bool}
    (H : Facts F I0 IX I1 RX R1 v n) {Tf af cf ar cr Dlo dlmin dlmax dwmax E Wq : Nat}
    (hlo : 1 ≤ Dlo) (hbox : Dlo ≤ dlmax + dwmax) (haf : af ≤ Tf) (hord : cf + ar ≤ dlmin + E) :
    SafeBoxW F I0 IX I1 RX R1 v n (Tf - af) (af + cf) (ar + cr) Dlo (dlmax + dwmax) Wq
        (Tf + dlmin + E - ar) ↔
      cf + dlmax + dwmax + Wq + ar ≤ dlmin + E := by
  rw [box_iffW H hlo hbox (by omega)]; omega

/-! ### The real bd_c2 INIT: CElemStrict's strict point is a hazard once the
feedback pin has a 1-tick window -/

/-- bd_c2, rising, follow b, release a, `tb = 0`, `wb = wa = 1`, `D = 420`,
feedback window `wq = 1`: at `s = 421` (CElemStrict's `strict_clean` point,
clean with `wq = 0`) the root is not 1 at the release tick, although the spec
says 1. -/
theorem c2_fbwin_hazard :
    let c := c2Cycle false false true
    simGW c2F (phase c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 0 1 422 1) false 419 1 422 ≠ kb true := by
  intro c
  exact (hazardW (sim_loopW c2F _ false 419 1 (fun _ => rfl)) (c2_all false false true) (by omega)
    (by omega) (by omega)).1

/-- One tick later it is clean (non-vacuity of the safe side). -/
theorem c2_fbwin_clean :
    let c := c2Cycle false false true
    Spec false true 0 1 (simGW c2F (phase c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 0 1 422 1) false 419 1) :=
  cleanW (sim_loopW _ _ _ _ _ (fun _ => rfl)) (c2_all false false true) (by omega) (by omega)

/-- The same for the bd_latch odd bit (data edge, then enable fall): the
latch's own loop with a feedback-pin window of `wq` needs
`tb + D + wq + wb ≤ s`. -/
theorem latch_fbwin_iff (vv : Bool) {tb wb s wa D wq : Nat} {i : Nat → K3 × K3} {qp G : Nat → K3}
    (L : LoopW latF (kb vv, K3.t) (K3.x, K3.t) (kb (!vv), K3.t) (kb (!vv), K3.x) (kb (!vv), K3.f) vv
      tb wb s wa D wq i qp G) (hD : 1 ≤ D) (hord : tb + wb ≤ s) :
    Spec vv (!vv) tb wb G ↔ tb + D + wq + wb ≤ s :=
  clean_iffW L (latch_facts vv) hD hord

end Formal.Cells.KleeneWin
