import Formal.Cells.KleenePess
import Formal.Cells.ArbOverlapRace
open Formal.Core.LutList

/-!
# Probe Bov2: can a PESSIMISTIC LUT model explain the arbcell 8% filtered overlap?

Follow-up of Bov (`ArbOverlapRace`: no binary transport trace of `bd_arbcell`
makes a >= 203 ps grant overlap; Bmt: with site pins the filter threshold `Dw`
is ~1.35 ns median, 0/192 copies predicted) under KleenePess's per-pin LUT
models (`kle`, `weak1`, `weak0`, `strict`, any per-pin mix).

## Model (`PRig`): one population copy of `hw/arb_mtbf.v`

`ustate` (`bd_c2n_set`, INIT FFB2.., rst = 0), `ugrant` O5/O6 (0C0C0C0C_A0A0A0A0),
detector `raw = g1c & g2c` (LUT2 8), filter `upwand = raw & bd_delay(2)(raw)`
(LUT2 8; the chain lumped into one pin delay `c0 + Dw` with window `wd`). Each pin
reads its source through Bov's transport delay; an edge makes the pin `x` for
`w` ticks (`pinW`: the mux select is mid-rail while the edge passes). Each LUT
output at each tick is ANY binary value its model output admits (`lutM`): a
model `x` is resolved adversarially, per tick, per reader. The filtered sticky
bit can be set iff the filter output is 1 at some tick (`Fires`).

## Results

* §2 `w0_rig`: with zero-width edges (`w = wd = 0`) EVERY policy family is
  Bov's binary model, so `w0_raw_cap`, `w0_cell_never_203`, `w0_filter_iff`
  (Bov's caps, Bmt's 0/192) hold under all four models. Pessimism needs an `x`
  select. `prig_of_kle`: a pessimistic model only adds traces (soundness of the
  Kleene/GMW reading transfers); §4 shows the added traces have no Kleene
  witness (exactness does not transfer).
* §3 detector path passing 0 (Kleene or weak 1 on its pins):
  `filter_two_point`, `det_two_point`, `filter_isolated` (the filter is still
  a width filter, slack `w`: an isolated raw run fires only if `Dw < len + w`).
* §4 weak 0 at upwand: `pess_trace` (all gate relations, real INITs, Bov's
  SLOW_MAX delays, `Dw = 1348`, `w = 1`), `pess_fires`: the filtered bit fires
  although `raw` is ONE 305 ps run (`pess_raw_short`), from the raw edge alone.
  Control `ctrl_kle_clean` / `ctrl_witness`: the same trace with both upwand pins
  passing 0 cannot fire. **`fires_iff`**: on this trace family a filtered event
  is possible iff an upwand pin fails to pass 0.
* §5 `ustate` per-pin exact conditions (`st_hold1_r2`, `st_hold1_r1`,
  `st_hold0_r1`, `st_hold0_r2`, `st_xhold`, `st_restore0/1`), `grants_both_x`,
  `weak1_chain`, `weak0_chain`, `restore_weak`: under weak 1 at r2's pin, ONE
  request edge into a both-high hold puts `x` on q and on both grants (no race);
  Kleene keeps q = 1.
* §6 any `ustate` model, grants and detector passing 0: `raw_needs_both` (raw = 1
  needs q = 1 and q = 0 |s+b| apart, slack 2w: a long raw run needs q toggling
  throughout), `toggle_echo` (with quiet requests every q toggle is an echo of
  one a loop delay earlier). Witnesses `raw_needs_both_witness`, `echo_witness`.

Assumed: KleenePess's models (one 2:1 mux per level; per-pin policy), the edge
window `w` (H_EDGE_X: a pin is `x` while its edge passes; width unmeasured), Bov's
per-pin transport delays (`Dl`, `slowD`), adversarial per-tick resolution of `x`
(H_PESS_ANY: a model `x` may be read as any value by each reader, each tick).
NOT covered: which model silicon follows; the sticky latch's own width
filtering (Fires = filter output 1 for one tick); the chain's two LUT1s as
separate gates; whether the weak-1 cell runt yields a filter-sized raw run
in the timed model (only §6's necessary conditions are proved); the 8% rate
(the models say "may", so they allow every copy, not 15 of 192).

Core Lean only.
-/

namespace Formal.Cells.ArbOverlapPess
open Formal.Cells Formal.Cells.KleenePess Formal.Cells.ArbBinary Formal.Cells.ArbOverlapRace

abbrev Sig := Int → Bool

/-! ## §1 The pin reading with an edge window -/

/-- A LUT pin reading source `x` through transport delay `d`, with an edge
window of `w` ticks: the pin is `x` (mid-rail select) while the delayed source
is not constant over the last `w + 1` ticks, else the delayed value.
`w = 0`: no window (Bov's transport model). -/
def pinW (x : Sig) (d : Int) (w : Nat) (t : Int) : K3 :=
  if (List.range (w + 1)).all (fun k => x (t - d - (k : Int)) == x (t - d)) then
    K3.ofBool (x (t - d)) else .x

theorem pinW_zero (x : Sig) (d t : Int) : pinW x d 0 t = K3.ofBool (x (t - d)) := by
  simp [pinW]

theorem pinW_one_def (x : Sig) (d t : Int) (h : x (t - d - 1) = x (t - d)) :
    pinW x d 1 t = K3.ofBool (x (t - d)) := by
  simp [pinW, List.range_succ, h]

theorem pinW_one_x (x : Sig) (d t : Int) (h : x (t - d - 1) ≠ x (t - d)) :
    pinW x d 1 t = .x := by
  simp [pinW, List.range_succ, h]

/-- A pin that does not read `0` saw a `1` somewhere in its window. -/
theorem pinW_ne_f (x : Sig) (d : Int) (w : Nat) (t : Int) (h : pinW x d w t ≠ .f) :
    ∃ k : Nat, k ≤ w ∧ x (t - d - (k : Int)) = true := by
  unfold pinW at h
  split at h
  · cases hx : x (t - d)
    · rw [hx] at h; exact absurd rfl h
    · exact ⟨0, Nat.zero_le _, by simpa using hx⟩
  · rename_i hc
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at hc
    have : ∃ k : Nat, k < w + 1 ∧ x (t - d - (k : Int)) ≠ x (t - d) := by
      apply Classical.byContradiction; intro hn; apply hc; intro k hk
      apply Classical.byContradiction; intro hne; exact hn ⟨k, hk, hne⟩
    obtain ⟨k, hk, hne⟩ := this
    cases hx : x (t - d)
    · refine ⟨k, by omega, ?_⟩
      rw [hx] at hne; cases h' : x (t - d - (k : Int)) <;> simp_all
    · exact ⟨0, Nat.zero_le _, by simpa using hx⟩

/-- No `x` pin: every policy gives the Kleene value. -/
theorem lutM_noX (pol : Nat → Pol) (init : Nat) (ins : List K3)
    (h : ∀ j, j < ins.length → ins.getD j .X ≠ .X) : lutM pol init ins = lutK init ins := by
  unfold lutM
  split
  · rfl
  · rename_i hc
    by_cases hk : lutK init ins = .X
    · rw [hk]
    · exact absurd ⟨hk, fun j hj hx => absurd hx (h j hj)⟩ hc

theorem admits_ofBool (v b : Bool) : K3.admits (K3.ofBool v) b = true ↔ b = v := by
  cases v <;> cases b <;> decide

/-! ### The real INITs on definite pins -/

theorem st_bin (pol : Nat → Pol) (a b c : Bool) :
    lutM pol C2N_SET [K3.ofBool a, K3.ofBool b, K3.ofBool c, .f, .f, .f] = K3.ofBool (stF a b c) := by
  rw [lutM_noX] <;> cases a <;> cases b <;> cases c <;> decide

theorem g5_bin (pol : Nat → Pol) (a b c : Bool) :
    o5M pol GRANT [K3.ofBool a, K3.ofBool b, K3.ofBool c, .f, .f, .t] = K3.ofBool (gr1 a b c) := by
  unfold o5M; rw [lutM_noX] <;> cases a <;> cases b <;> cases c <;> decide

theorem g6_bin (pol : Nat → Pol) (a b c : Bool) :
    lutM pol GRANT [K3.ofBool a, K3.ofBool b, K3.ofBool c, .f, .f, .t] = K3.ofBool (gr2 a b c) := by
  rw [lutM_noX] <;> cases a <;> cases b <;> cases c <;> decide

theorem det_bin (pol : Nat → Pol) (a b : Bool) :
    lutM pol DET [K3.ofBool a, K3.ofBool b] = K3.ofBool (det a b) := by
  rw [lutM_noX] <;> cases a <;> cases b <;> decide

/-! ## §2 The rig under a per-pin LUT model, X resolved per tick

`PRig`: every LUT output, at every tick, is ANY binary value admitted by the
model output (`lutM`, KleenePess) on its pins. This is the adversarial per-tick
resolution: a model `x` (mid-rail select / runt) may be read as 0 or 1 by each
reader, tick by tick, independently. Policies are per LUT and per pin. -/

/-- One policy family per LUT of a population copy of `hw/arb_mtbf.v`. -/
structure Pols where
  /-- `ustate` (`bd_c2n_set`), pins `[r1, r2, q, rst, 0, 0]`. -/
  st : Nat → Pol
  /-- `ugrant` (both outputs; one physical pin per input), pins `[r1, r2, q, 0, 0, 1]`. -/
  g : Nat → Pol
  /-- the detector LUT2 `raw = g1c & g2c`, pins `[g1c, g2c]`. -/
  det : Nat → Pol
  /-- the filter AND `upwand`, pins `[raw, bd_delay(2)(raw)]`. -/
  fa : Nat → Pol

/-- All Kleene (H_KLEENE_LUT). -/
def allKle : Pols := ⟨U kle, U kle, U kle, U kle⟩

/-- **The model.** `D` are Bov's per-pin transport delays (route + site pin +
arc), `c0` the delay raw → upwand.I0, `c0 + Dw` the delay through the two-link
chain to upwand.I1 (lumped; window `wd`), `w` the edge window of every other
pin. `rst` is 0 (after `arb_rst` released), tied pins are constants. -/
structure PRig (P : Pols) (D : Dl) (c0 Dw : Int) (w wd : Nat)
    (r1 r2 q g1 g2 raw flt : Sig) : Prop where
  H_ST : ∀ t, K3.admits (lutM P.st C2N_SET
    [pinW r1 D.s1 w t, pinW r2 D.s2 w t, pinW q D.L w t, .f, .f, .f]) (q t) = true
  H_G5 : ∀ t, K3.admits (o5M P.g GRANT
    [pinW r1 D.a1 w t, pinW r2 D.x2 w t, pinW q D.b5 w t, .f, .f, .t]) (g1 t) = true
  H_G6 : ∀ t, K3.admits (lutM P.g GRANT
    [pinW r1 D.x1 w t, pinW r2 D.a2 w t, pinW q D.b6 w t, .f, .f, .t]) (g2 t) = true
  H_DET : ∀ t, K3.admits (lutM P.det DET [pinW g1 D.e1 w t, pinW g2 D.e2 w t]) (raw t) = true
  H_AND : ∀ t, K3.admits (lutM P.fa DET [pinW raw c0 w t, pinW raw (c0 + Dw) wd t]) (flt t) = true

/-- The filtered sticky bit can be set: the filter output is 1 at some tick. -/
def Fires (flt : Sig) : Prop := ∃ t, flt t = true

/-- **Zero-width edges: every policy is the binary model.** With `w = wd = 0`
no pin is ever `x`, so whatever the per-pin policy, a `PRig` IS Bov's transport
`Rig` and the filter is `raw(t-c0) ∧ raw(t-c0-Dw)`. -/
theorem w0_rig {P : Pols} {D : Dl} {c0 Dw : Int} {r1 r2 q g1 g2 raw flt : Sig}
    (h : PRig P D c0 Dw 0 0 r1 r2 q g1 g2 raw flt) :
    Rig D r1 r2 q g1 g2 raw ∧ ∀ t, flt t = (raw (t - c0) && raw (t - c0 - Dw)) := by
  refine ⟨⟨⟨fun t => ?_, fun t => ?_, fun t => ?_⟩, fun t => ?_⟩, fun t => ?_⟩
  · have := h.H_G5 t; simp only [pinW_zero, g5_bin, admits_ofBool] at this; exact this
  · have := h.H_G6 t; simp only [pinW_zero, g6_bin, admits_ofBool] at this; exact this
  · have := h.H_DET t; simp only [pinW_zero, det_bin, admits_ofBool] at this; exact this
  · have := h.H_ST t; simp only [pinW_zero, st_bin, admits_ofBool] at this; exact this
  · have := h.H_AND t; simp only [pinW_zero, det_bin, admits_ofBool, det_eq] at this
    rw [this, show t - (c0 + Dw) = t - c0 - Dw by omega]

/-- Hence Bov's caps hold under EVERY policy at `w = 0`: no raw run is longer
than `|s + b|`, and no `g1 ∧ g2` run at the grant LUT reaches 113 ps. -/
theorem w0_raw_cap {P : Pols} {D : Dl} {c0 Dw : Int} {r1 r2 q g1 g2 raw flt : Sig}
    (h : PRig P D c0 Dw 0 0 r1 r2 q g1 g2 raw flt) (T ℓ : Int) (hr : HighOn raw T ℓ) :
    ℓ ≤ adist (D.e1 + D.b5) (D.e2 + D.b6) :=
  raw_cap (w0_rig h).1.toDec T ℓ hr

theorem w0_cell_never_203 {P : Pols} {D : Dl} {c0 Dw : Int} {r1 r2 q g1 g2 raw flt : Sig}
    (h : PRig P D c0 Dw 0 0 r1 r2 q g1 g2 raw flt) (Pd : Decomp D)
    (h5 : 42 ≤ Pd.o5q ∧ Pd.o5q ≤ 157) (h6 : 45 ≤ Pd.o6q ∧ Pd.o6q ≤ 124)
    (T ℓ : Int) (hg : HighOn (fun t => g1 t && g2 t) T ℓ) : ℓ < 203 :=
  (cell_never_203 (w0_rig h).1.toDec Pd h5 h6 T ℓ hg).2

/-- And the filter is Bov's width filter: on an isolated raw run it fires iff
`Dw` is shorter than the run. -/
theorem w0_filter_iff {P : Pols} {D : Dl} {c0 Dw : Int} {r1 r2 q g1 g2 raw flt : Sig}
    (h : PRig P D c0 Dw 0 0 r1 r2 q g1 g2 raw flt) (lo hi : Int)
    (hraw : ∀ t, raw t = true ↔ lo ≤ t ∧ t < hi) (hD : 0 ≤ Dw) :
    Fires flt ↔ Dw < hi - lo := by
  rw [← filter_iff raw lo hi c0 Dw hraw hD]
  unfold Fires
  simp only [(w0_rig h).2]

/-! ### Soundness transfers, exactness does not

Every Kleene-admissible value is admissible under every policy (`lutM ⊑ lutK`),
so a pessimistic model only ADDS traces (`prig_of_kle`). The traces it adds
have no Kleene witness: §4's `pess_fires` against `ctrl_kle_clean`. -/

theorem admits_of_kle (pol : Nat → Pol) (init : Nat) (ins : List K3) (b : Bool)
    (h : K3.admits (lutK init ins) b = true) : K3.admits (lutM pol init ins) b = true := by
  rcases lutM_le_lutK pol init ins with hx | he
  · rw [hx]; rfl
  · rw [he]; exact h

theorem prig_of_kle (P : Pols) {D : Dl} {c0 Dw : Int} {w wd : Nat} {r1 r2 q g1 g2 raw flt : Sig}
    (h : PRig allKle D c0 Dw w wd r1 r2 q g1 g2 raw flt) :
    PRig P D c0 Dw w wd r1 r2 q g1 g2 raw flt := by
  have k : ∀ (init : Nat) (ins : List K3) (b : Bool),
      K3.admits (lutM (U kle) init ins) b = true → K3.admits (lutM (fun _ => kle) init ins) b = true :=
    fun _ _ _ h => h
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · have := h.H_ST t; rw [show allKle.st = U kle from rfl, lutM_kle] at this
    exact admits_of_kle _ _ _ _ this
  · have := h.H_G5 t; unfold o5M at this ⊢; rw [show allKle.g = U kle from rfl, lutM_kle] at this
    exact admits_of_kle _ _ _ _ this
  · have := h.H_G6 t; rw [show allKle.g = U kle from rfl, lutM_kle] at this
    exact admits_of_kle _ _ _ _ this
  · have := h.H_DET t; rw [show allKle.det = U kle from rfl, lutM_kle] at this
    exact admits_of_kle _ _ _ _ this
  · have := h.H_AND t; rw [show allKle.fa = U kle from rfl, lutM_kle] at this
    exact admits_of_kle _ _ _ _ this

/-! ## §3 Detector path passing 0 (Kleene, weak1): the filter stays a width filter -/

/-- If every pin of a LUT passes 0, its 0s are exactly Kleene's. -/
theorem zero_iff (pol : Nat → Pol) (init : Nat) (ins : List K3)
    (hp : ∀ j, j < ins.length → (pol j).p0 = true) :
    lutM pol init ins = .f ↔ lutK init ins = .f := by
  have := lutM_definite pol init ins false
  constructor
  · exact fun h => (this.1 h).1
  · exact fun h => this.2 ⟨h, fun j hj _ => by simp [Pol.pass, hp j hj]⟩

theorem and_ne_f : ∀ a b : K3, lutK DET [a, b] ≠ .f → a ≠ .f ∧ b ≠ .f := by decide

theorem and_admits_true (pol : Nat → Pol) (h0 : (pol 0).p0 = true) (h1 : (pol 1).p0 = true)
    (a b : K3) (h : K3.admits (lutM pol DET [a, b]) true = true) : a ≠ .f ∧ b ≠ .f := by
  apply and_ne_f
  intro hk
  rw [← zero_iff pol DET [a, b] (fun j hj => by
    match j, hj with
    | 0, _ => exact h0
    | 1, _ => exact h1)] at hk
  rw [hk] at h
  exact absurd h (by decide)

/-- **Two-point filter.** If both filter pins pass 0, a filtered event at `t`
needs `raw = 1` somewhere in the direct pin's window AND somewhere in the
delayed pin's window. -/
theorem filter_two_point {P : Pols} {D : Dl} {c0 Dw : Int} {w wd : Nat}
    {r1 r2 q g1 g2 raw flt : Sig} (h : PRig P D c0 Dw w wd r1 r2 q g1 g2 raw flt)
    (h0 : (P.fa 0).p0 = true) (h1 : (P.fa 1).p0 = true) (t : Int) (hf : flt t = true) :
    (∃ k : Nat, k ≤ w ∧ raw (t - c0 - (k : Int)) = true) ∧
    (∃ k : Nat, k ≤ wd ∧ raw (t - (c0 + Dw) - (k : Int)) = true) := by
  have := h.H_AND t
  rw [hf] at this
  obtain ⟨h1, h2⟩ := and_admits_true _ h0 h1 _ _ this
  exact ⟨pinW_ne_f _ _ _ _ h1, pinW_ne_f _ _ _ _ h2⟩

/-- The same for the detector: raw = 1 needs both grants 1 in their windows. -/
theorem det_two_point {P : Pols} {D : Dl} {c0 Dw : Int} {w wd : Nat}
    {r1 r2 q g1 g2 raw flt : Sig} (h : PRig P D c0 Dw w wd r1 r2 q g1 g2 raw flt)
    (h0 : (P.det 0).p0 = true) (h1 : (P.det 1).p0 = true) (t : Int) (hr : raw t = true) :
    (∃ k : Nat, k ≤ w ∧ g1 (t - D.e1 - (k : Int)) = true) ∧
    (∃ k : Nat, k ≤ w ∧ g2 (t - D.e2 - (k : Int)) = true) := by
  have := h.H_DET t
  rw [hr] at this
  obtain ⟨h1, h2⟩ := and_admits_true _ h0 h1 _ _ this
  exact ⟨pinW_ne_f _ _ _ _ h1, pinW_ne_f _ _ _ _ h2⟩

/-- **Width filter with slack `w`.** If the filter pins pass 0 and every 1 of
`raw` lies in `[lo, hi)`, a filtered event needs `Dw < (hi - lo) + w`. -/
theorem filter_isolated {P : Pols} {D : Dl} {c0 Dw : Int} {w wd : Nat}
    {r1 r2 q g1 g2 raw flt : Sig} (h : PRig P D c0 Dw w wd r1 r2 q g1 g2 raw flt)
    (h0 : (P.fa 0).p0 = true) (h1 : (P.fa 1).p0 = true) (lo hi : Int)
    (hraw : ∀ t, raw t = true → lo ≤ t ∧ t < hi) (hF : Fires flt) : Dw < (hi - lo) + w := by
  obtain ⟨t, ht⟩ := hF
  obtain ⟨⟨k, hk, h1⟩, ⟨k', _, h2⟩⟩ := filter_two_point h h0 h1 t ht
  have a := hraw _ h1; have b := hraw _ h2
  omega

/-! ## §4 Weak 0 at the filter AND: a filtered event with no long overlap

The trace is Bov's SLOW_MAX handover (`slowD`; `ArbOverlapRace.slow_trace_*`):
`raw` is ONE run of 305 ps. The filter threshold is Bmt's median SLOW_MAX value
`Dw = 1348` ps; `c0 = 429` (300 ps route + A6 site pin 5 + arc 124). Edge window
`w = wd = 1` tick (1 ps). `ustate`, `ugrant` and the detector are Kleene. -/

/-- Closed forms of Bov's trace signals. -/
theorem sG1_eq (u : Int) : sG1 u = decide (u < 1068) := by
  simp only [sG1, gr1_eq, sR1, sQ]
  rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega

theorem sG2_eq (u : Int) : sG2 u = decide (1167 ≤ u) := by
  simp only [sG2, gr2_eq, sR2, sQ]
  rw [Bool.eq_iff_iff]; simp only [Bool.true_and, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq]; omega

theorem sRaw_eq (u : Int) : sRaw u = decide (1703 ≤ u ∧ u < 2008) := by
  rw [Bool.eq_iff_iff, slow_trace_raw]; simp

/-- The state LUT relation of the trace, Kleene `ustate`, `w = 1`. -/
theorem tr_st (t : Int) : K3.admits (lutM (U kle) C2N_SET
    [pinW sR1 slowD.s1 1 t, pinW sR2 slowD.s2 1 t, pinW sQ slowD.L 1 t, .f, .f, .f]) (sQ t) = true := by
  dsimp only [slowD]
  by_cases h1 : t = 636
  · subst h1; decide
  by_cases h2 : t = 1276
  · subst h2; decide
  rw [pinW_one_def sR1 636 t (by simp only [sR1]; exact decide_eq_decide.mpr (by omega)),
    pinW_one_def sR2 636 t rfl,
    pinW_one_def sQ 640 t (by simp only [sQ]; exact decide_eq_decide.mpr (by omega)),
    st_bin, admits_ofBool]
  exact slow_trace_rig.H_ST t

theorem tr_g5 (t : Int) : K3.admits (o5M (U kle) GRANT
    [pinW sR1 slowD.a1 1 t, pinW sR2 slowD.x2 1 t, pinW sQ slowD.b5 1 t, .f, .f, .t]) (sG1 t) = true := by
  dsimp only [slowD]
  by_cases h1 : t = 1068
  · subst h1; decide
  by_cases h2 : t = 1161
  · subst h2; decide
  rw [pinW_one_def sR1 1068 t (by simp only [sR1]; exact decide_eq_decide.mpr (by omega)),
    pinW_one_def sR2 1031 t rfl,
    pinW_one_def sQ 525 t (by simp only [sQ]; exact decide_eq_decide.mpr (by omega)),
    g5_bin, admits_ofBool]
  exact slow_trace_rig.H_G5 t

theorem tr_g6 (t : Int) : K3.admits (lutM (U kle) GRANT
    [pinW sR1 slowD.x1 1 t, pinW sR2 slowD.a2 1 t, pinW sQ slowD.b6 1 t, .f, .f, .t]) (sG2 t) = true := by
  dsimp only [slowD]
  by_cases h1 : t = 1068
  · subst h1; decide
  by_cases h2 : t = 1167
  · subst h2; decide
  rw [pinW_one_def sR1 1068 t (by simp only [sR1]; exact decide_eq_decide.mpr (by omega)),
    pinW_one_def sR2 1031 t rfl,
    pinW_one_def sQ 531 t (by simp only [sQ]; exact decide_eq_decide.mpr (by omega)),
    g6_bin, admits_ofBool]
  exact slow_trace_rig.H_G6 t

theorem tr_det (t : Int) : K3.admits (lutM (U kle) DET
    [pinW sG1 slowD.e1 1 t, pinW sG2 slowD.e2 1 t]) (sRaw t) = true := by
  dsimp only [slowD]
  by_cases h1 : t = 2008
  · subst h1; decide
  by_cases h2 : t = 1703
  · subst h2; decide
  rw [pinW_one_def sG1 940 t (by rw [sG1_eq, sG1_eq]; exact decide_eq_decide.mpr (by omega)),
    pinW_one_def sG2 536 t (by rw [sG2_eq, sG2_eq]; exact decide_eq_decide.mpr (by omega)),
    det_bin, admits_ofBool]
  exact slow_trace_rig.H_DET t

/-- The filter AND on `[x, 0]`: Kleene 0, but `x` if the `x` pin fails 0. -/
theorem and_x0 (pol : Nat → Pol) : lutM pol DET [.x, .f] = (if (pol 0).p0 then .f else .x) := by
  have hk : lutK DET [K3.x, K3.f] = K3.f := by decide
  cases h : (pol 0).p0
  · show lutM pol DET [.x, .f] = .x
    cases hm : lutM pol DET [.x, .f]
    · have := ((lutM_definite pol DET [.x, .f] false).1 hm).2 0 (by decide) rfl
      simp [Pol.pass, h] at this
    · have := ((lutM_definite pol DET [.x, .f] true).1 hm).1
      rw [hk] at this; exact absurd this (by decide)
    · rfl
  · show lutM pol DET [.x, .f] = .f
    refine (lutM_definite pol DET [.x, .f] false).2 ⟨hk, fun j hj hx => ?_⟩
    match j, hj with
    | 0, _ => simpa [Pol.pass] using h
    | 1, _ => exact absurd hx (by decide)

theorem and_0x (pol : Nat → Pol) : lutM pol DET [.f, .x] = (if (pol 1).p0 then .f else .x) := by
  have hk : lutK DET [K3.f, K3.x] = K3.f := by decide
  cases h : (pol 1).p0
  · show lutM pol DET [.f, .x] = .x
    cases hm : lutM pol DET [.f, .x]
    · have := ((lutM_definite pol DET [.f, .x] false).1 hm).2 1 (by decide) rfl
      simp [Pol.pass, h] at this
    · have := ((lutM_definite pol DET [.f, .x] true).1 hm).1
      rw [hk] at this; exact absurd this (by decide)
    · rfl
  · show lutM pol DET [.f, .x] = .f
    refine (lutM_definite pol DET [.f, .x] false).2 ⟨hk, fun j hj hx => ?_⟩
    match j, hj with
    | 0, _ => exact absurd hx (by decide)
    | 1, _ => simpa [Pol.pass] using h

theorem admits_f_or_x (k : K3) (hk : k = .f ∨ k = .x) : K3.admits k false = true := by
  rcases hk with h | h <;> rw [h] <;> rfl

theorem ite_fx (c : Bool) : (if c then K3.f else K3.x) = .f ∨ (if c then K3.f else K3.x) = .x := by
  cases c <;> simp

/-- The filter AND relation for the trace, for ANY policy on its two pins and
any filter output that is 1 only where a failing pin reads the raw edge. -/
theorem tr_and (pol : Nat → Pol) (flt : Sig)
    (hflt : ∀ t, flt t = true → (t = 2132 ∧ (pol 0).p0 = false) ∨ (t = 3480 ∧ (pol 1).p0 = false))
    (t : Int) :
    K3.admits (lutM pol DET [pinW sRaw 429 1 t, pinW sRaw (429 + 1348) 1 t]) (flt t) = true := by
  have hfx : ∀ k : K3, (k = .f ∨ k = .x) → (flt t = true → k = .x) → K3.admits k (flt t) = true := by
    intro k hk hx
    cases hf : flt t
    · exact admits_f_or_x k hk
    · rw [hx hf]; rfl
  by_cases h1 : t = 2132
  · subst h1
    have : pinW sRaw 429 1 2132 = .x ∧ pinW sRaw (429 + 1348) 1 2132 = .f := by decide
    rw [this.1, this.2, and_x0]
    refine hfx _ (ite_fx _) (fun hf => ?_)
    rcases hflt _ hf with ⟨_, hp⟩ | ⟨h, _⟩
    · rw [hp]; rfl
    · exact absurd h (by decide)
  by_cases h2 : t = 2437
  · subst h2
    have : pinW sRaw 429 1 2437 = .x ∧ pinW sRaw (429 + 1348) 1 2437 = .f := by decide
    rw [this.1, this.2, and_x0]
    refine hfx _ (ite_fx _) (fun hf => ?_)
    rcases hflt _ hf with ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)
  by_cases h3 : t = 3480
  · subst h3
    have : pinW sRaw 429 1 3480 = .f ∧ pinW sRaw (429 + 1348) 1 3480 = .x := by decide
    rw [this.1, this.2, and_0x]
    refine hfx _ (ite_fx _) (fun hf => ?_)
    rcases hflt _ hf with ⟨h, _⟩ | ⟨_, hp⟩
    · exact absurd h (by decide)
    · rw [hp]; rfl
  by_cases h4 : t = 3785
  · subst h4
    have : pinW sRaw 429 1 3785 = .f ∧ pinW sRaw (429 + 1348) 1 3785 = .x := by decide
    rw [this.1, this.2, and_0x]
    refine hfx _ (ite_fx _) (fun hf => ?_)
    rcases hflt _ hf with ⟨h, _⟩ | ⟨h, _⟩ <;> exact absurd h (by decide)
  have hf : flt t = false := by
    cases h : flt t
    · rfl
    · rcases hflt t h with ⟨h', _⟩ | ⟨h', _⟩ <;> omega
  rw [pinW_one_def sRaw 429 t (by rw [sRaw_eq, sRaw_eq]; exact decide_eq_decide.mpr (by omega)),
    pinW_one_def sRaw (429 + 1348) t (by rw [sRaw_eq, sRaw_eq]; exact decide_eq_decide.mpr (by omega)),
    det_bin, hf, admits_ofBool, det_eq, sRaw_eq, sRaw_eq]
  rw [eq_comm, Bool.eq_false_iff]
  simp only [ne_eq, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- The upper four LUTs are Kleene in both the pessimistic trace and the control. -/
def pessP (fa : Nat → Pol) : Pols := ⟨U kle, U kle, U kle, fa⟩

/-- Weak 0 on upwand.I0 (the pin that reads `raw` directly), Kleene elsewhere. -/
def fa0 : Nat → Pol := fun j => if j = 0 then weak0 else kle

def pFlt : Sig := fun t => decide (t = 2132)

/-- **The pessimistic trace.** Every gate relation of the copy holds, with
`ugrant`, `ustate` and the detector Kleene and upwand.I0 weak-0. -/
theorem pess_trace : PRig (pessP fa0) slowD 429 1348 1 1 sR1 sR2 sQ sG1 sG2 sRaw pFlt where
  H_ST := tr_st
  H_G5 := tr_g5
  H_G6 := tr_g6
  H_DET := tr_det
  H_AND := tr_and fa0 pFlt (fun t h => Or.inl ⟨by simpa [pFlt] using h, rfl⟩)

/-- **It fires**, at t = 2132 ps: the first tick of the raw edge at upwand.I0. -/
theorem pess_fires : Fires pFlt := ⟨2132, by decide⟩

/-- The raw run is 305 ps, far below the filter threshold: the BINARY filter
(`w = 0`, or any policy passing 0 at upwand) never fires on it. -/
theorem pess_raw_short : (∀ t, sRaw t = true ↔ 1703 ≤ t ∧ t < 2008) ∧
    ∀ t, (sRaw (t - 429) && sRaw (t - 429 - 1348)) = false := by
  refine ⟨slow_trace_raw, fun t => ?_⟩
  rw [sRaw_eq, sRaw_eq, Bool.eq_false_iff]
  simp only [ne_eq, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- **Control.** Same requests, same grants, same raw: with BOTH upwand pins
passing 0 (Kleene, weak1) no filter output is admissible except 0 for ever. -/
theorem ctrl_kle_clean (fa : Nat → Pol) (h0 : (fa 0).p0 = true) (h1 : (fa 1).p0 = true) (flt : Sig)
    (h : PRig (pessP fa) slowD 429 1348 1 1 sR1 sR2 sQ sG1 sG2 sRaw flt) : ¬ Fires flt := by
  intro hF
  have := filter_isolated h h0 h1 1703 2008 (fun t ht => (slow_trace_raw t).1 ht) hF
  omega

/-- The control is not vacuous: all-Kleene with `flt ≡ 0` is a model trace. -/
theorem ctrl_witness : PRig allKle slowD 429 1348 1 1 sR1 sR2 sQ sG1 sG2 sRaw (fun _ => false) where
  H_ST := tr_st
  H_G5 := tr_g5
  H_G6 := tr_g6
  H_DET := tr_det
  H_AND := tr_and (U kle) _ (fun _ h => absurd h (by decide))

/-- **The enabling condition, exactly** (this trace family: Kleene `ustate`,
`ugrant`, detector; any upwand policy): a filtered event is possible iff some
upwand pin fails to pass 0. Either pin will do: I0 fires on the direct raw
edge (t = 2132), I1 on the delayed one (t = 3480). -/
theorem fires_iff (fa : Nat → Pol) :
    (∃ flt, PRig (pessP fa) slowD 429 1348 1 1 sR1 sR2 sQ sG1 sG2 sRaw flt ∧ Fires flt) ↔
      ((fa 0).p0 = false ∨ (fa 1).p0 = false) := by
  constructor
  · rintro ⟨flt, h, hF⟩
    cases h0 : (fa 0).p0
    · exact Or.inl rfl
    cases h1 : (fa 1).p0
    · exact Or.inr rfl
    exact absurd hF (ctrl_kle_clean fa h0 h1 flt h)
  · intro hc
    by_cases h0 : (fa 0).p0 = false
    · refine ⟨pFlt, ⟨tr_st, tr_g5, tr_g6, tr_det, tr_and fa pFlt (fun t ht => Or.inl ⟨by simpa [pFlt] using ht, h0⟩)⟩, pess_fires⟩
    · have h1 : (fa 1).p0 = false := by rcases hc with h | h; exact absurd h h0; exact h
      refine ⟨fun t => decide (t = 3480), ⟨tr_st, tr_g5, tr_g6, tr_det,
        tr_and fa _ (fun t ht => Or.inr ⟨by simpa using ht, h1⟩)⟩, ⟨3480, by decide⟩⟩

/-! ### Non-vacuity of §2 and §3 -/

/-- Bov's trace with the binary filter is a model trace at `w = 0`, for EVERY
policy family (the hypotheses of `w0_rig` are satisfiable). -/
theorem w0_witness (P : Pols) (Dw : Int) :
    PRig P slowD 429 Dw 0 0 sR1 sR2 sQ sG1 sG2 sRaw
      (fun t => sRaw (t - 429) && sRaw (t - (429 + Dw))) where
  H_ST := fun t => by
    rw [pinW_zero, pinW_zero, pinW_zero, st_bin, admits_ofBool]; exact slow_trace_rig.H_ST t
  H_G5 := fun t => by
    rw [pinW_zero, pinW_zero, pinW_zero, g5_bin, admits_ofBool]; exact slow_trace_rig.H_G5 t
  H_G6 := fun t => by
    rw [pinW_zero, pinW_zero, pinW_zero, g6_bin, admits_ofBool]; exact slow_trace_rig.H_G6 t
  H_DET := fun t => by
    rw [pinW_zero, pinW_zero, det_bin, admits_ofBool]; exact slow_trace_rig.H_DET t
  H_AND := fun t => by
    rw [pinW_zero, pinW_zero, det_bin, admits_ofBool, det_eq]

/-- `filter_isolated`'s hypotheses with a firing filter are satisfiable (all
Kleene, `Dw = 203`): it fires, and the bound `203 < 305 + 0` holds. -/
theorem isolated_witness :
    PRig allKle slowD 429 203 0 0 sR1 sR2 sQ sG1 sG2 sRaw
      (fun t => sRaw (t - 429) && sRaw (t - (429 + 203))) ∧
    Fires (fun t => sRaw (t - 429) && sRaw (t - (429 + 203))) := by
  refine ⟨w0_witness allKle 203, ?_⟩
  obtain ⟨t, ht⟩ := (slow_trace_passes 429 203 (by decide)).2 (by decide)
  refine ⟨t, ?_⟩
  show (sRaw (t - 429) && sRaw (t - (429 + 203))) = true
  rw [show t - (429 + 203) = t - 429 - 203 by omega]; exact ht

/-! ## §5 Where pessimism enters the cell (combinational, per pin, real INITs)

`bd_c2n_set` pins `[I0 = r1, I1 = r2, I2 = q, I3 = rst, 0, 0]`. Each lemma is
for an arbitrary per-pin policy `pol`; `kle` passes everything. -/

/-- With exactly one `x` pin `j` and a definite Kleene value `v`, the model
gives `v` iff pin `j`'s level passes `v`, else `x`. -/
theorem lutM_single (pol : Nat → Pol) (init : Nat) (ins : List K3) (j : Nat)
    (hj : j < ins.length) (hx : ins.getD j .X = .X)
    (hothers : ∀ i, i < ins.length → i ≠ j → ins.getD i .X ≠ .X) (v : Bool)
    (hk : lutK init ins = K3.ofBool v) :
    lutM pol init ins = (if (pol j).pass (K3.ofBool v) then K3.ofBool v else .x) := by
  cases hp : (pol j).pass (K3.ofBool v)
  · show lutM pol init ins = .x
    cases hm : lutM pol init ins with
    | X => rfl
    | zero =>
      have hd := (lutM_definite pol init ins false).1 hm
      have hv : K3.ofBool v = K3.ofBool false := hk.symm.trans hd.1
      have := hd.2 j hj hx; rw [← hv, hp] at this; exact absurd this (by decide)
    | one =>
      have hd := (lutM_definite pol init ins true).1 hm
      have hv : K3.ofBool v = K3.ofBool true := hk.symm.trans hd.1
      have := hd.2 j hj hx; rw [← hv, hp] at this; exact absurd this (by decide)
  · show lutM pol init ins = K3.ofBool v
    refine (lutM_definite pol init ins v).2 ⟨hk, fun i hi hx' => ?_⟩
    by_cases hij : i = j
    · subst hij; exact hp
    · exact absurd hx' (hothers i hi hij)

/-- The Kleene value is `x`: every model gives `x`. -/
theorem lutM_of_kX (pol : Nat → Pol) (init : Nat) (ins : List K3) (hk : lutK init ins = .x) :
    lutM pol init ins = .x := by
  rcases lutM_le_lutK pol init ins with h | h
  · exact h
  · exact h.trans hk

/-- **q holding 1, r1 = 1, r2 edge** (the start of a both-high hold): `x`
iff r2's pin (I1) fails to pass 1. Kleene: 1. -/
theorem st_hold1_r2 (pol : Nat → Pol) :
    lutM pol C2N_SET [.t, .x, .t, .f, .f, .f] = (if (pol 1).p1 then .t else .x) :=
  lutM_single pol C2N_SET _ 1 (by decide) rfl
    (fun i hi hij => by match i, hi, hij with
      | 0, _, _ => decide | 2, _, _ => decide | 3, _, _ => decide
      | 4, _, _ => decide | 5, _, _ => decide) true (by decide)

/-- **q holding 1, r2 = 0, r1 edge**: `x` iff r1's pin (I0) fails 1. -/
theorem st_hold1_r1 (pol : Nat → Pol) :
    lutM pol C2N_SET [.x, .f, .t, .f, .f, .f] = (if (pol 0).p1 then .t else .x) :=
  lutM_single pol C2N_SET _ 0 (by decide) rfl
    (fun i hi hij => by match i, hi, hij with
      | 1, _, _ => decide | 2, _, _ => decide | 3, _, _ => decide
      | 4, _, _ => decide | 5, _, _ => decide) true (by decide)

/-- **q holding 0, r2 = 1, r1 edge** (the mirror both-high start): `x` iff
r1's pin fails to pass 0. -/
theorem st_hold0_r1 (pol : Nat → Pol) :
    lutM pol C2N_SET [.x, .t, .f, .f, .f, .f] = (if (pol 0).p0 then .f else .x) :=
  lutM_single pol C2N_SET _ 0 (by decide) rfl
    (fun i hi hij => by match i, hi, hij with
      | 1, _, _ => decide | 2, _, _ => decide | 3, _, _ => decide
      | 4, _, _ => decide | 5, _, _ => decide) false (by decide)

/-- **q holding 0, r1 = 0, r2 edge**: `x` iff r2's pin fails 0. -/
theorem st_hold0_r2 (pol : Nat → Pol) :
    lutM pol C2N_SET [.f, .x, .f, .f, .f, .f] = (if (pol 1).p0 then .f else .x) :=
  lutM_single pol C2N_SET _ 1 (by decide) rfl
    (fun i hi hij => by match i, hi, hij with
      | 0, _, _ => decide | 2, _, _ => decide | 3, _, _ => decide
      | 4, _, _ => decide | 5, _, _ => decide) false (by decide)

/-- **x on q is held on every hold input** (`r1 = r2`), in every model. -/
theorem st_xhold (pol : Nat → Pol) (v : Bool) :
    lutM pol C2N_SET [K3.ofBool v, K3.ofBool v, .x, .f, .f, .f] = .x :=
  lutM_of_kX pol _ _ (by cases v <;> decide)

/-- **Restoring q from x**: the reset input `(0, 1)` restores 0 iff q's own
pin (I2) passes 0; the set input `(1, 0)` restores 1 iff it passes 1. -/
theorem st_restore0 (pol : Nat → Pol) :
    lutM pol C2N_SET [.f, .t, .x, .f, .f, .f] = (if (pol 2).p0 then .f else .x) :=
  lutM_single pol C2N_SET _ 2 (by decide) rfl
    (fun i hi hij => by match i, hi, hij with
      | 0, _, _ => decide | 1, _, _ => decide | 3, _, _ => decide
      | 4, _, _ => decide | 5, _, _ => decide) false (by decide)

theorem st_restore1 (pol : Nat → Pol) :
    lutM pol C2N_SET [.t, .f, .x, .f, .f, .f] = (if (pol 2).p1 then .t else .x) :=
  lutM_single pol C2N_SET _ 2 (by decide) rfl
    (fun i hi hij => by match i, hi, hij with
      | 0, _, _ => decide | 1, _, _ => decide | 3, _, _ => decide
      | 4, _, _ => decide | 5, _, _ => decide) true (by decide)

/-- **x on q with both requests high reaches BOTH grants**, in every model. -/
theorem grants_both_x (pol : Nat → Pol) :
    o5M pol GRANT [.t, .t, .x, .f, .f, .t] = .x ∧ lutM pol GRANT [.t, .t, .x, .f, .f, .t] = .x :=
  ⟨lutM_of_kX pol _ _ (by decide), lutM_of_kX pol _ _ (by decide)⟩

/-- A detector or filter AND (LUT2 `8`) whose two inputs read `x`: `x` in every
model; with `[x, 0]` it is `x` iff I0 fails 0 (`and_x0`). -/
theorem and_xx (pol : Nat → Pol) : lutM pol DET [.x, .x] = .x := lutM_of_kX pol _ _ (by decide)

/-- **The weak-1 chain (untimed).** If `ustate`'s r2 pin fails to pass 1, one
r2 rise during a q = 1, r1 = 1 phase puts `x` on q; the both-high hold keeps it
(any model); both grants, the detector and the filter AND are then `x` (any
model): every stage may read 1. Under `kle` the same input leaves q = 1. -/
theorem weak1_chain (pst pg pd pa : Nat → Pol) (h : (pst 1).p1 = false) :
    lutM pst C2N_SET [.t, .x, .t, .f, .f, .f] = .x ∧
    lutM pst C2N_SET [.t, .t, .x, .f, .f, .f] = .x ∧
    o5M pg GRANT [.t, .t, .x, .f, .f, .t] = .x ∧ lutM pg GRANT [.t, .t, .x, .f, .f, .t] = .x ∧
    lutM pd DET [.x, .x] = .x ∧ lutM pa DET [.x, .x] = .x ∧
    lutM (U kle) C2N_SET [.t, .x, .t, .f, .f, .f] = .t := by
  refine ⟨by rw [st_hold1_r2, h]; rfl, st_xhold pst true, (grants_both_x pg).1, (grants_both_x pg).2,
    and_xx pd, and_xx pa, by rw [st_hold1_r2]; rfl⟩

/-- The weak-0 mirror: r1 rising into a both-high hold while q = 0. -/
theorem weak0_chain (pst : Nat → Pol) (h : (pst 0).p0 = false) :
    lutM pst C2N_SET [.x, .t, .f, .f, .f, .f] = .x ∧
    lutM (U kle) C2N_SET [.x, .t, .f, .f, .f, .f] = .f := by
  refine ⟨by rw [st_hold0_r1, h]; rfl, by rw [st_hold0_r1]; rfl⟩

/-- Under weak 1 the reset input still restores 0 from `x` (I2 passes 0), so an
`x` left by `arb_rst` (KleenePess `scen_weak1`) is cleared at the first reset
input `(r1, r2) = (0, 1)`; under weak 0 the set input restores 1. -/
theorem restore_weak (pst : Nat → Pol) :
    (pst 2 = weak1 → lutM pst C2N_SET [.f, .t, .x, .f, .f, .f] = .f) ∧
    (pst 2 = weak0 → lutM pst C2N_SET [.t, .f, .x, .f, .f, .f] = .t) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [st_restore0, h]; rfl
  · rw [st_restore1, h]; rfl

/-! ## §6 Timed consequences for any `ustate` model

`raw_needs_both`: with grants and detector passing 0 (Kleene or weak 1; any
model at `ustate`), `raw = 1` at `t` needs q = 1 within `2w` before
`t - (e1 + b5)` AND q = 0 within `2w` before `t - (e2 + b6)`. So a raw run of
length ℓ > |s + b| + 2w needs q to take BOTH values inside every window of
span |s + b| + 2w along the run: q must keep toggling for the whole run.
`toggle_echo`: while the requests are quiet at `ustate`'s pins, every toggle
of q is an echo of a toggle one loop delay earlier (any `ustate` model). -/

theorem pinW_ne_t (x : Sig) (d : Int) (w : Nat) (t : Int) (h : pinW x d w t ≠ .t) :
    ∃ k : Nat, k ≤ w ∧ x (t - d - (k : Int)) = false := by
  have := pinW_ne_f (fun u => !x u) d w t (by
    intro hf; apply h
    unfold pinW at hf ⊢
    have e : ∀ k : Nat, ((!x (t - d - (k : Int))) == (!x (t - d))) = (x (t - d - (k : Int)) == x (t - d)) := by
      intro k; cases x (t - d - (k : Int)) <;> cases x (t - d) <;> rfl
    simp only [e] at hf
    split at hf
    · cases hx : x (t - d) <;> simp_all
    · exact absurd hf (by decide))
  obtain ⟨k, hk, hx⟩ := this
  exact ⟨k, hk, by simpa using hx⟩

theorem pinW_const (x : Sig) (d : Int) (w : Nat) (t : Int) (c : Bool)
    (h : ∀ v, t - d - w ≤ v → v ≤ t - d → x v = c) : pinW x d w t = K3.ofBool c := by
  have h0 : x (t - d) = c := h _ (by omega) (Int.le_refl _)
  have hall : (List.range (w + 1)).all (fun k => x (t - d - (k : Int)) == x (t - d)) = true := by
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
    intro k hk
    rw [h0, h _ (by omega) (by omega)]
  unfold pinW
  rw [hall]; simp [h0]

theorem g5K_q (a b c : K3) (h : lutK (GRANT % 2 ^ 32) ([a, b, c, .f, .f, .t].take 5) ≠ .f) :
    c ≠ .f := by
  revert h; revert a b c; decide

theorem g6K_q (a b c : K3) (h : lutK GRANT [a, b, c, .f, .f, .t] ≠ .f) : c ≠ .t := by
  revert h; revert a b c; decide

/-- **raw needs q = 1 and q = 0, |s + b| apart (up to 2w).** -/
theorem raw_needs_both {P : Pols} {D : Dl} {c0 Dw : Int} {w wd : Nat}
    {r1 r2 q g1 g2 raw flt : Sig} (h : PRig P D c0 Dw w wd r1 r2 q g1 g2 raw flt)
    (hg : ∀ j, (P.g j).p0 = true) (hd0 : (P.det 0).p0 = true) (hd1 : (P.det 1).p0 = true)
    (t : Int) (hr : raw t = true) :
    (∃ k : Nat, k ≤ 2 * w ∧ q (t - (D.e1 + D.b5) - (k : Int)) = true) ∧
    (∃ k : Nat, k ≤ 2 * w ∧ q (t - (D.e2 + D.b6) - (k : Int)) = false) := by
  obtain ⟨⟨k1, hk1, h1⟩, ⟨k2, hk2, h2⟩⟩ := det_two_point h hd0 hd1 t hr
  constructor
  · have hG := h.H_G5 (t - D.e1 - k1)
    rw [h1] at hG
    have hne : o5M P.g GRANT [pinW r1 D.a1 w (t - D.e1 - k1), pinW r2 D.x2 w (t - D.e1 - k1),
        pinW q D.b5 w (t - D.e1 - k1), .f, .f, .t] ≠ .f := by
      intro hf; rw [hf] at hG; exact absurd hG (by decide)
    unfold o5M at hne
    rw [Ne, zero_iff _ _ _ (fun j _ => hg j)] at hne
    obtain ⟨k, hk, hq⟩ := pinW_ne_f _ _ _ _ (g5K_q _ _ _ hne)
    exact ⟨k1 + k, by omega, by rw [← hq]; congr 1; push_cast; omega⟩
  · have hG := h.H_G6 (t - D.e2 - k2)
    rw [h2] at hG
    have hne : lutM P.g GRANT [pinW r1 D.x1 w (t - D.e2 - k2), pinW r2 D.a2 w (t - D.e2 - k2),
        pinW q D.b6 w (t - D.e2 - k2), .f, .f, .t] ≠ .f := by
      intro hf; rw [hf] at hG; exact absurd hG (by decide)
    rw [Ne, zero_iff _ _ _ (fun j _ => hg j)] at hne
    obtain ⟨k, hk, hq⟩ := pinW_ne_t _ _ _ _ (g6K_q _ _ _ hne)
    exact ⟨k2 + k, by omega, by rw [← hq]; congr 1; push_cast; omega⟩

/-- **Every toggle of q is an echo** while the requests are quiet at `ustate`'s
pins: if r1, r2 are constant over both ticks' windows and q toggles between
`u - 1` and `u`, then q toggled somewhere in `[u - 1 - L - w, u - L]`.
Any `ustate` policy. -/
theorem toggle_echo {P : Pols} {D : Dl} {c0 Dw : Int} {w wd : Nat}
    {r1 r2 q g1 g2 raw flt : Sig} (h : PRig P D c0 Dw w wd r1 r2 q g1 g2 raw flt) (u : Int)
    (hr1 : ∀ v, u - 1 - D.s1 - w ≤ v → v ≤ u - D.s1 → r1 v = r1 (u - D.s1))
    (hr2 : ∀ v, u - 1 - D.s2 - w ≤ v → v ≤ u - D.s2 → r2 v = r2 (u - D.s2))
    (htog : q (u - 1) ≠ q u) :
    ∃ v, u - 1 - D.L - w ≤ v ∧ v < u - D.L ∧ q v ≠ q (v + 1) := by
  apply Classical.byContradiction
  intro hn
  have hc : ∀ v, u - 1 - D.L - w ≤ v → v ≤ u - D.L → q v = q (u - D.L) := by
    intro v hv1 hv2
    -- q is constant on the closed range: walk up from v
    have step : ∀ n : Nat, v + n ≤ u - D.L → q v = q (v + n) := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro hn'
        rw [ih (by omega)]
        apply Classical.byContradiction; intro hne
        exact hn ⟨v + n, by omega, by omega, by
          rw [show v + (n : Int) + 1 = v + ((n + 1 : Nat) : Int) by push_cast; omega]; exact hne⟩
    have := step (u - D.L - v).toNat (by omega)
    rw [this, show v + ((u - D.L - v).toNat : Int) = u - D.L by omega]
  have pins : ∀ t', (t' = u - 1 ∨ t' = u) →
      [pinW r1 D.s1 w t', pinW r2 D.s2 w t', pinW q D.L w t', .f, .f, .f] =
      [K3.ofBool (r1 (u - D.s1)), K3.ofBool (r2 (u - D.s2)), K3.ofBool (q (u - D.L)), .f, .f, .f] := by
    intro t' ht'
    rw [pinW_const r1 D.s1 w t' _ (fun v a b => hr1 v (by omega) (by omega)),
      pinW_const r2 D.s2 w t' _ (fun v a b => hr2 v (by omega) (by omega)),
      pinW_const q D.L w t' _ (fun v a b => hc v (by omega) (by omega))]
  have e1 := h.H_ST (u - 1)
  have e2 := h.H_ST u
  rw [pins _ (Or.inl rfl), st_bin, admits_ofBool] at e1
  rw [pins _ (Or.inr rfl), st_bin, admits_ofBool] at e2
  exact htog (e1.trans e2.symm)

/-! ### Non-vacuity of §6 -/

/-- `raw_needs_both`'s hypotheses hold on Bov's trace (all Kleene, `w = 0`) with
raw = 1 at 1703. -/
theorem raw_needs_both_witness :
    PRig allKle slowD 429 1348 0 0 sR1 sR2 sQ sG1 sG2 sRaw
      (fun t => sRaw (t - 429) && sRaw (t - (429 + 1348))) ∧ sRaw 1703 = true :=
  ⟨w0_witness allKle 1348, by decide⟩

def eR : Sig := fun _ => true
/-- A 1 ps runt circulating in q's loop (L = 640) during a both-high hold. -/
def eQ : Sig := fun t => decide (t % 640 = 0)
def eG1 : Sig := fun t => gr1 (eR (t - 1068)) (eR (t - 1031)) (eQ (t - 525))
def eG2 : Sig := fun t => gr2 (eR (t - 1068)) (eR (t - 1031)) (eQ (t - 531))
def eRaw : Sig := fun t => det (eG1 (t - 940)) (eG2 (t - 536))
def eFlt : Sig := fun t => eRaw (t - 429) && eRaw (t - (429 + 1348))

/-- `toggle_echo`'s hypotheses are satisfiable: requests constant, q toggles
(the circulating runt of pure transport), every policy. -/
theorem echo_witness (P : Pols) :
    PRig P slowD 429 1348 0 0 eR eR eQ eG1 eG2 eRaw eFlt ∧ eQ 0 ≠ eQ 1 := by
  refine ⟨⟨fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_, fun t => ?_⟩, by decide⟩
  · rw [pinW_zero, pinW_zero, pinW_zero, st_bin, admits_ofBool, stF_eq]
    simp only [eR, eQ, slowD, Bool.not_true, Bool.and_false, Bool.false_or,
      Bool.not_false, Bool.and_true]
    exact decide_eq_decide.mpr (by omega)
  · rw [pinW_zero, pinW_zero, pinW_zero, g5_bin, admits_ofBool]; rfl
  · rw [pinW_zero, pinW_zero, pinW_zero, g6_bin, admits_ofBool]; rfl
  · rw [pinW_zero, pinW_zero, det_bin, admits_ofBool]; rfl
  · rw [pinW_zero, pinW_zero, det_bin, admits_ofBool, det_eq]; rfl

end Formal.Cells.ArbOverlapPess
