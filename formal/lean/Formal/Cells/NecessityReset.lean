import Formal.Cells.LibGapMux
import Formal.Cells.ResetContract
import Formal.Cells.Latch
open Formal.Core.LutList

/-!
# NecessityReset: the reset-width rows, sufficient AND necessary, per pin

Probe Bsx (shard B). Rows `bd_c2.reset_width`, `bd_c2n.reset_width`,
`bd_c3.reset_width`, `bd_c4.reset_width`, `design.rst_hold`,
`bd_latch_rst.reset` (its H_RST_PW form), and the loop (H_RST_LONG) terms of
`bd_merge.reset_first`, `bd_mux.reset_first`, `bd_pipe.rst_lines` were proved
sufficient only (lumped LUT: `CElemTiming.c2_reset`, `CTreeTimed.c3_reset`,
`ResetContract.c2n_reset`, ...). "Necessity not shown separately (same loop as
pulse_width)". This file shows it on the real INITs in B's per-pin model
(the model of `LibGapSteer` / `LibGapMux`).

## Model (Int ps, named hypotheses)

* **H_PIN_READ** (`LoopEq`): for `t ≥ 0` the cell's output is its REAL INIT
  (`lutB`) applied to: the rst driver read at `pr.σ t`, its own output read at
  `pq.σ t`, and the other pins at a constant vector (H_IN_HELD below). Each
  read map lies in its window: `pr ∈ [Rlo, Rhi]` = rst wire + site pin +
  that pin's arc to O; `pq ∈ [Qlo, Qhi]`, `Qlo ≥ 1` = the loop (feedback
  pin's arc to O + feedback wire + feedback site pin). Read maps need not be
  monotone (as in LibGapSteer).
* **H_RST_PULSE**: rst at its driver is high exactly on `[0, W)`.
* **H_IN_HELD**: the other pins are constant at a NON-enabling vector (the
  cell holds when rst = 0: `RstCell.hold`). This is admissible under every
  cited sufficient theorem (`c2_reset`'s H_RELEASE: `a, b` never both 1;
  `c3_reset`, `c4_reset`, `c2n_reset` likewise) and it is the physical
  case of an input still at a power-up value, or (for `bd_c2n`) every input
  at its reset value (`c2n_resetstate_holds`).
* Power-up: the output before 0 is arbitrary (sufficiency); the counter-trace
  uses the non-reset value (any power-up state is in the rows' scope).

Spec (`ResetOK r0 Rhi q`): from `Rhi` (the first instant rst is surely read
high) the output is the reset value `r0` for ever.

## Results

* `reset_ok` (sufficient, any read maps in the box): `Rhi + Qhi ≤ W + Rlo`.
* `reset_fails` (necessity): if `W + Rlo < Rhi + Qhi`, then for the read
  maps `prAdv` (rst seen late at its rise, early at its fall) and a fixed loop
  `Qhi`, EVERY trace satisfying H_PIN_READ from the non-reset power-up value
  shows the non-reset value at some `t ≥ Rhi`; `runB_loopEq` shows such a
  trace exists.
* `reset_box_exact` (headline): ResetOK for every read-map pair in the box,
  every trace and every power-up **iff** `Rhi + Qhi ≤ W + Rlo`.
* `reset_pin_exact` (fixed delays, one corner realisation): iff `dq ≤ W`;
  the rst path delay `dr` DROPS OUT.
* Instances on the real INITs (`cells`): bd_c2, bd_c2n, bd_c2n_set, bd_c3,
  bd_c4, bd_mux.uj0/uj1, bd_latch_rst (RESET_VALUE 0 and 1).
* `c2_inputs0_selfreset`: with every input at 0, bd_c2 / bd_c3 / bd_c4 /
  uj0 / uj1 reach and hold 0 with NO reset pulse at all (W = 0): at design
  level the width is not needed for those cells once their inputs are
  flushed; bd_c2n and bd_c2n_set hold with inputs at their reset values
  (`c2n_resetstate_holds`), so there it is needed.
* Counter-traces with numbers: `c2_short_reset` (loop 400 ps, rst 399 ps:
  bd_c2 is 1 again at 899), `c2_ok_reset` (rst 400 ps: 0 for ever).
* `json_box_gap`: numbers that satisfy the JSON `design.rst_hold` form in box
  mode (every hi SLOW_MAX, every lo FAST_MIN) but violate the exact box
  condition: the JSON form charges the I_rst arc only on the data side; in
  the per-pin box the rst arc's own spread is missing. In 1C mode (both
  sides one corner, flat O6 arcs) the JSON form is the exact condition plus
  its 1 ps strictness margin.
* Kleene remark (`kleene_release_harmless`, `kleene_rise_x`): an X window on
  rst at its FALL is harmless once the feedback reads the reset value; at
  its RISE (feedback still non-reset) the output is X. So the strict `+1`
  of the rows is the rise window of rst, not the fall.

* `early_request_ok` / `early_request_numbers` (section 10): the rows'
  "released before the first request" clause (H_RST_EARLY) is NOT necessary:
  a request reaching its pin 1100 ps before release, and staying, gets the
  clean response. `returned_pulse_lost`: what IS needed is H_NO_RETURN (no
  input completes a pulse while rst is read high).

NOT covered: the arbiter ustate (two outputs); the X-window (Kleene) version
of the box theorem (only the two pointwise facts above); inputs that move
during reset (the row's H_RELEASE scope is only "not enabling"); the flush
of stateless lines (`design.rst_flush`); correlated pin delays (the box
treats rst rise and fall reads as independent).
-/

namespace Formal.Cells.NecessityReset
open Formal.Cells
open Formal.Cells.LibGapSteer (Rd pulse)
open Formal.Cells.LibGapMux (int_ind)

/-! ## 0. The cell abstraction -/

/-- With the other pins held at a non-enabling vector, the cell's next-state
function of (rst read, feedback read): rst forces `r0`, rst = 0 holds. -/
structure RstCell (F : Bool → Bool → Bool) (r0 : Bool) : Prop where
  force : ∀ q, F true q = r0
  hold : ∀ q, F false q = q

/-- **H_PIN_READ** with **H_RST_PULSE** (rst high on `[0, W)` at its driver). -/
def LoopEq (F : Bool → Bool → Bool) (pr pq : Rd) (W : Int) (q : Int → Bool) : Prop :=
  ∀ t, 0 ≤ t → q t = F (pulse 0 W (pr.σ t)) (q (pq.σ t))

/-- The spec: reset value from `Rhi` on, for ever. -/
def ResetOK (r0 : Bool) (Rhi : Int) (q : Int → Bool) : Prop := ∀ t, Rhi ≤ t → q t = r0

/-! ## 1. Sufficient -/

theorem reset_ok {F : Bool → Bool → Bool} {r0 : Bool} (C : RstCell F r0)
    (pr pq : Rd) (W Rlo Rhi Qhi : Int) (q : Int → Bool)
    (h0 : 0 ≤ Rlo) (hR1 : Rlo ≤ pr.lo) (hR2 : pr.hi ≤ Rhi) (hQ1 : 1 ≤ pq.lo) (hQ2 : pq.hi ≤ Qhi)
    (H_RST_WIDTH : Rhi + Qhi ≤ W + Rlo) (hL : LoopEq F pr pq W q) : ResetOK r0 Rhi q := by
  have hlh : pr.lo ≤ pr.hi := by have := pr.ge 0; have := pr.le 0; omega
  apply int_ind (fun t => Rhi ≤ t → q t = r0) (fun t ht h => by omega)
  intro t ht ih hR
  rw [hL t ht]
  have g1 := pr.ge t; have g2 := pr.le t; have g3 := pq.ge t; have g4 := pq.le t
  by_cases hw : pr.σ t < W
  · have : pulse 0 W (pr.σ t) = true := by simp [pulse]; omega
    rw [this, C.force]
  · have : pulse 0 W (pr.σ t) = false := by simp [pulse]; omega
    rw [this, C.hold]
    exact ih _ (by omega) (by omega)

/-! ## 2. Necessary -/

/-- The adversarial rst read map: the rise is seen through `Rhi`, the fall
through `Rlo` (the switch happens at `t = Rhi`). -/
def prAdv (Rlo Rhi : Int) (h : Rlo ≤ Rhi) : Rd :=
  ⟨fun t => if t < Rhi then t - Rhi else t - Rlo, Rlo, Rhi,
   fun t => by split <;> omega, fun t => by split <;> omega⟩

/-- Before `Rhi` the adversarial read never sees rst high, so the cell keeps
its power-up value (non-reset). -/
theorem before_forced {F : Bool → Bool → Bool} {r0 : Bool} (C : RstCell F r0)
    (pr : Rd) (Rlo Rhi W : Int) (d : Int) (hd : 1 ≤ d) (q : Int → Bool)
    (hσ : ∀ t, pr.σ t = if t < Rhi then t - Rhi else t - Rlo)
    (hL : LoopEq F pr (Rd.const d) W q) (hP : ∀ t, t < 0 → q t = !r0) :
    ∀ t, t < Rhi → q t = !r0 := by
  apply int_ind (fun t => t < Rhi → q t = !r0) (fun t ht _ => hP t ht)
  intro t ht ih hlt
  rw [hL t ht, hσ t]
  have : pulse 0 W (if t < Rhi then t - Rhi else t - Rlo) = false := by
    simp [pulse, hlt]; omega
  rw [this, C.hold]
  exact ih _ (by simp [Rd.const]; omega) (by simp [Rd.const]; omega)

theorem reset_fails {F : Bool → Bool → Bool} {r0 : Bool} (C : RstCell F r0)
    (pr : Rd) (Rlo Rhi W : Int) (d : Int) (hd : 1 ≤ d) (q : Int → Bool)
    (h0 : 0 ≤ Rlo) (hR : Rlo ≤ Rhi)
    (hσ : ∀ t, pr.σ t = if t < Rhi then t - Rhi else t - Rlo)
    (hbad : W + Rlo < Rhi + d)
    (hL : LoopEq F pr (Rd.const d) W q) (hP : ∀ t, t < 0 → q t = !r0) :
    ∃ t, Rhi ≤ t ∧ q t = !r0 := by
  have A := before_forced C pr Rlo Rhi W d hd q hσ hL hP
  by_cases hc : W + Rlo ≤ Rhi
  · refine ⟨Rhi, Int.le_refl _, ?_⟩
    rw [hL Rhi (by omega), hσ Rhi]
    have : pulse 0 W (if Rhi < Rhi then Rhi - Rhi else Rhi - Rlo) = false := by
      simp [pulse]; omega
    rw [this, C.hold]
    exact A _ (by simp [Rd.const]; omega)
  · refine ⟨W + Rlo, by omega, ?_⟩
    rw [hL (W + Rlo) (by omega), hσ (W + Rlo)]
    have : pulse 0 W (if W + Rlo < Rhi then W + Rlo - Rhi else W + Rlo - Rlo) = false := by
      simp [pulse]; omega
    rw [this, C.hold]
    exact A _ (by simp [Rd.const]; omega)

/-! ## 3. Traces exist (the necessity is not vacuous) -/

/-- Trace constructor: loop delay `d ≥ 1`, power-up value `p`, next-state `f`. -/
def runN (f : Int → Bool → Bool) (d : Nat) (p : Bool) (hd : 0 < d) : Nat → Bool
  | n => f n (if _h : n < d then p else runN f d p hd (n - d))
termination_by n => n
decreasing_by omega

def runB (f : Int → Bool → Bool) (d : Nat) (p : Bool) (hd : 0 < d) (t : Int) : Bool :=
  if t < 0 then p else runN f d p hd t.toNat

theorem runB_pre (f : Int → Bool → Bool) (d : Nat) (p : Bool) (hd : 0 < d) :
    ∀ t, t < 0 → runB f d p hd t = p := by
  intro t ht; simp [runB, ht]

theorem runB_eq (f : Int → Bool → Bool) (d : Nat) (p : Bool) (hd : 0 < d) (t : Int) (ht : 0 ≤ t) :
    runB f d p hd t = f t (runB f d p hd (t - d)) := by
  unfold runB
  rw [ite_eq_right (by omega), runN]
  have e : ((t.toNat : Nat) : Int) = t := Int.toNat_of_nonneg ht
  rw [e]
  congr 1
  by_cases h : t.toNat < d
  · rw [dite_eq_left h, ite_eq_left (by omega)]
  · rw [dite_eq_right h, ite_eq_right (by omega)]
    congr 1; omega

theorem runB_loopEq (F : Bool → Bool → Bool) (pr : Rd) (W : Int) (d : Nat) (p : Bool) (hd : 0 < d) :
    LoopEq F pr (Rd.const d) W (runB (fun t v => F (pulse 0 W (pr.σ t)) v) d p hd) := by
  intro t ht
  exact runB_eq _ d p hd t ht

/-! ## 4. Exact -/

/-- **Headline (box).** -/
theorem reset_box_exact {F : Bool → Bool → Bool} {r0 : Bool} (C : RstCell F r0)
    (W Rlo Rhi Qlo Qhi : Int) (h0 : 0 ≤ Rlo) (hR : Rlo ≤ Rhi) (hQ : 1 ≤ Qlo) (hQQ : Qlo ≤ Qhi) :
    (∀ pr pq : Rd, Rlo ≤ pr.lo → pr.hi ≤ Rhi → Qlo ≤ pq.lo → pq.hi ≤ Qhi →
      ∀ q, LoopEq F pr pq W q → ResetOK r0 Rhi q) ↔ Rhi + Qhi ≤ W + Rlo := by
  constructor
  · intro h
    apply Classical.byContradiction; intro hn
    have hd : 0 < Qhi.toNat := by omega
    have eQ : ((Qhi.toNat : Nat) : Int) = Qhi := Int.toNat_of_nonneg (by omega)
    let pr := prAdv Rlo Rhi hR
    let q := runB (fun t v => F (pulse 0 W (pr.σ t)) v) Qhi.toNat (!r0) hd
    have hL := runB_loopEq F pr W Qhi.toNat (!r0) hd
    have hok := h pr (Rd.const (Qhi.toNat : Int)) (Int.le_refl _) (Int.le_refl _)
      (by simp [Rd.const]; omega) (by simp [Rd.const]; omega) q hL
    obtain ⟨t, ht, hq⟩ := reset_fails C pr Rlo Rhi W (Qhi.toNat : Int) (by omega) q h0 hR
      (fun t => rfl) (by omega) hL (runB_pre _ _ _ hd)
    have := hok t ht
    rw [hq] at this; cases r0 <;> simp at this
  · intro hc pr pq a1 a2 a3 a4 q hL
    exact reset_ok C pr pq W Rlo Rhi Qhi q h0 a1 a2 (by omega) a4 hc hL

/-- **Fixed delays (one corner realisation).** The rst path `dr` drops out:
exact iff the rst pulse is at least the loop. -/
theorem reset_pin_exact {F : Bool → Bool → Bool} {r0 : Bool} (C : RstCell F r0)
    (W dr : Int) (dq : Nat) (h0 : 0 ≤ dr) (hq : 0 < dq) :
    (∀ q, LoopEq F (Rd.const dr) (Rd.const dq) W q → ResetOK r0 dr q) ↔ (dq : Int) ≤ W := by
  constructor
  · intro h
    apply Classical.byContradiction; intro hn
    let q := runB (fun t v => F (pulse 0 W ((Rd.const dr).σ t)) v) dq (!r0) hq
    have hL := runB_loopEq F (Rd.const dr) W dq (!r0) hq
    obtain ⟨t, ht, hqq⟩ := reset_fails C (Rd.const dr) dr dr W (dq : Int) (by omega) q h0
      (Int.le_refl _) (fun t => by simp [Rd.const]) (by omega) hL (runB_pre _ _ _ hq)
    have := h q hL t ht
    rw [hqq] at this; cases r0 <;> simp at this
  · intro hc q hL
    exact reset_ok C _ _ W dr dr dq q h0 (by simp [Rd.const]) (by simp [Rd.const])
      (by simp [Rd.const]; omega) (by simp [Rd.const]) (by omega) hL

/-! ## 5. The real INITs (gcd_hw's reset-carrying LUTs) -/

open Formal.Cells.ResetContract (I_c2 I_c2n I_c2n_set I_c3 I_c4 I_uj0 I_uj1)

/-- bd_c2 `[a, b, q, rst]`, held at `a = 1, b = 0` (e.g. merge `uxa`: x_req
up from a frontier token, z_ack 0). -/
def Fc2 (r q : Bool) : Bool := lutB I_c2 [true, false, q, r, false, false]
/-- bd_c2n `[a, b, q, rst]` = C(a, ~b), held at `a = 1, b = 1`. -/
def Fc2n (r q : Bool) : Bool := lutB I_c2n [true, true, q, r, false, false]
/-- bd_c2n with every input at its reset value 0 (`a = 0, ~b = 1`: mixed). -/
def Fc2n0 (r q : Bool) : Bool := lutB I_c2n [false, false, q, r, false, false]
/-- bd_c2n_set (gcd_rig `uenv1`, reset value 1), inputs 0. -/
def Fc2ns (r q : Bool) : Bool := lutB I_c2n_set [false, false, q, r, false, false]
/-- bd_c3 `[a, b, c, q, rst]`, held at `(1, 0, 0)`. -/
def Fc3 (r q : Bool) : Bool := lutB I_c3 [true, false, false, q, r, false]
/-- bd_c4 `[a, b, c, d, q, rst]`, held at `(1, 0, 0, 0)`. -/
def Fc4 (r q : Bool) : Bool := lutB I_c4 [true, false, false, false, q, r]
/-- bd_mux.uj0 `[x_req, ctl_req, s, j0, rst]`, held at x_req = 1, ctl_req = 0. -/
def Fuj0 (r q : Bool) : Bool := lutB I_uj0 [true, false, false, q, r, false]
def Fuj1 (r q : Bool) : Bool := lutB I_uj1 [true, false, true, q, r, false]
/-- bd_latch_rst `[d, en, q, rst]` with en = 0 and d = !RESET_VALUE. -/
def Flr0 (r q : Bool) : Bool := lutB Latch.RST0 [true, false, q, r, false, false]
def Flr1 (r q : Bool) : Bool := lutB Latch.RST1 [false, false, q, r, false, false]

theorem cells :
    RstCell Fc2 false ∧ RstCell Fc2n false ∧ RstCell Fc2n0 false ∧ RstCell Fc2ns true ∧
    RstCell Fc3 false ∧ RstCell Fc4 false ∧ RstCell Fuj0 false ∧ RstCell Fuj1 false ∧
    RstCell Flr0 false ∧ RstCell Flr1 true := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> decide

/-- `bd_c2n` with all inputs at their reset values HOLDS (named for the note). -/
theorem c2n_resetstate_holds : RstCell Fc2n0 false := cells.2.2.1

/-- Exact per cell, box form, for each real INIT. -/
theorem c2_box_exact (W Rlo Rhi Qlo Qhi : Int) (h0 : 0 ≤ Rlo) (hR : Rlo ≤ Rhi) (hQ : 1 ≤ Qlo)
    (hQQ : Qlo ≤ Qhi) :
    (∀ pr pq : Rd, Rlo ≤ pr.lo → pr.hi ≤ Rhi → Qlo ≤ pq.lo → pq.hi ≤ Qhi →
      ∀ q, LoopEq Fc2 pr pq W q → ResetOK false Rhi q) ↔ Rhi + Qhi ≤ W + Rlo :=
  reset_box_exact cells.1 W Rlo Rhi Qlo Qhi h0 hR hQ hQQ
theorem c2n_box_exact (W Rlo Rhi Qlo Qhi : Int) (h0 : 0 ≤ Rlo) (hR : Rlo ≤ Rhi) (hQ : 1 ≤ Qlo)
    (hQQ : Qlo ≤ Qhi) :
    (∀ pr pq : Rd, Rlo ≤ pr.lo → pr.hi ≤ Rhi → Qlo ≤ pq.lo → pq.hi ≤ Qhi →
      ∀ q, LoopEq Fc2n0 pr pq W q → ResetOK false Rhi q) ↔ Rhi + Qhi ≤ W + Rlo :=
  reset_box_exact cells.2.2.1 W Rlo Rhi Qlo Qhi h0 hR hQ hQQ
theorem c2ns_box_exact (W Rlo Rhi Qlo Qhi : Int) (h0 : 0 ≤ Rlo) (hR : Rlo ≤ Rhi) (hQ : 1 ≤ Qlo)
    (hQQ : Qlo ≤ Qhi) :
    (∀ pr pq : Rd, Rlo ≤ pr.lo → pr.hi ≤ Rhi → Qlo ≤ pq.lo → pq.hi ≤ Qhi →
      ∀ q, LoopEq Fc2ns pr pq W q → ResetOK true Rhi q) ↔ Rhi + Qhi ≤ W + Rlo :=
  reset_box_exact cells.2.2.2.1 W Rlo Rhi Qlo Qhi h0 hR hQ hQQ
theorem c3_box_exact (W Rlo Rhi Qlo Qhi : Int) (h0 : 0 ≤ Rlo) (hR : Rlo ≤ Rhi) (hQ : 1 ≤ Qlo)
    (hQQ : Qlo ≤ Qhi) :
    (∀ pr pq : Rd, Rlo ≤ pr.lo → pr.hi ≤ Rhi → Qlo ≤ pq.lo → pq.hi ≤ Qhi →
      ∀ q, LoopEq Fc3 pr pq W q → ResetOK false Rhi q) ↔ Rhi + Qhi ≤ W + Rlo :=
  reset_box_exact cells.2.2.2.2.1 W Rlo Rhi Qlo Qhi h0 hR hQ hQQ
theorem c4_box_exact (W Rlo Rhi Qlo Qhi : Int) (h0 : 0 ≤ Rlo) (hR : Rlo ≤ Rhi) (hQ : 1 ≤ Qlo)
    (hQQ : Qlo ≤ Qhi) :
    (∀ pr pq : Rd, Rlo ≤ pr.lo → pr.hi ≤ Rhi → Qlo ≤ pq.lo → pq.hi ≤ Qhi →
      ∀ q, LoopEq Fc4 pr pq W q → ResetOK false Rhi q) ↔ Rhi + Qhi ≤ W + Rlo :=
  reset_box_exact cells.2.2.2.2.2.1 W Rlo Rhi Qlo Qhi h0 hR hQ hQQ
theorem uj0_box_exact (W Rlo Rhi Qlo Qhi : Int) (h0 : 0 ≤ Rlo) (hR : Rlo ≤ Rhi) (hQ : 1 ≤ Qlo)
    (hQQ : Qlo ≤ Qhi) :
    (∀ pr pq : Rd, Rlo ≤ pr.lo → pr.hi ≤ Rhi → Qlo ≤ pq.lo → pq.hi ≤ Qhi →
      ∀ q, LoopEq Fuj0 pr pq W q → ResetOK false Rhi q) ↔ Rhi + Qhi ≤ W + Rlo :=
  reset_box_exact cells.2.2.2.2.2.2.1 W Rlo Rhi Qlo Qhi h0 hR hQ hQQ
theorem uj1_box_exact (W Rlo Rhi Qlo Qhi : Int) (h0 : 0 ≤ Rlo) (hR : Rlo ≤ Rhi) (hQ : 1 ≤ Qlo)
    (hQQ : Qlo ≤ Qhi) :
    (∀ pr pq : Rd, Rlo ≤ pr.lo → pr.hi ≤ Rhi → Qlo ≤ pq.lo → pq.hi ≤ Qhi →
      ∀ q, LoopEq Fuj1 pr pq W q → ResetOK false Rhi q) ↔ Rhi + Qhi ≤ W + Rlo :=
  reset_box_exact cells.2.2.2.2.2.2.2.1 W Rlo Rhi Qlo Qhi h0 hR hQ hQQ
theorem latch_rst0_box_exact (W Rlo Rhi Qlo Qhi : Int) (h0 : 0 ≤ Rlo) (hR : Rlo ≤ Rhi)
    (hQ : 1 ≤ Qlo) (hQQ : Qlo ≤ Qhi) :
    (∀ pr pq : Rd, Rlo ≤ pr.lo → pr.hi ≤ Rhi → Qlo ≤ pq.lo → pq.hi ≤ Qhi →
      ∀ q, LoopEq Flr0 pr pq W q → ResetOK false Rhi q) ↔ Rhi + Qhi ≤ W + Rlo :=
  reset_box_exact cells.2.2.2.2.2.2.2.2.1 W Rlo Rhi Qlo Qhi h0 hR hQ hQQ
theorem latch_rst1_box_exact (W Rlo Rhi Qlo Qhi : Int) (h0 : 0 ≤ Rlo) (hR : Rlo ≤ Rhi)
    (hQ : 1 ≤ Qlo) (hQQ : Qlo ≤ Qhi) :
    (∀ pr pq : Rd, Rlo ≤ pr.lo → pr.hi ≤ Rhi → Qlo ≤ pq.lo → pq.hi ≤ Qhi →
      ∀ q, LoopEq Flr1 pr pq W q → ResetOK true Rhi q) ↔ Rhi + Qhi ≤ W + Rlo :=
  reset_box_exact cells.2.2.2.2.2.2.2.2.2 W Rlo Rhi Qlo Qhi h0 hR hQ hQQ

/-! ## 6. Inputs already at 0: bd_c2 / c3 / c4 / uj reset themselves -/

/-- With every input 0 these cells compute 0 whatever rst and the feedback. -/
theorem inputs0_force : ∀ r q : Bool,
    lutB I_c2 [false, false, q, r, false, false] = false ∧
    lutB I_c3 [false, false, false, q, r, false] = false ∧
    lutB I_c4 [false, false, false, false, q, r] = false ∧
    lutB I_uj0 [false, false, false, q, r, false] = false ∧
    lutB I_uj0 [false, false, true, q, r, false] = false ∧
    lutB I_uj1 [false, false, false, q, r, false] = false ∧
    lutB I_uj1 [false, false, true, q, r, false] = false := by decide

/-- So with inputs 0 from time 0 and NO reset pulse (`W = 0`), bd_c2 is 0 at
every `t ≥ 0`: the reset-width row is not needed for such an instance. -/
theorem c2_inputs0_selfreset (pr pq : Rd) (q : Int → Bool)
    (hL : LoopEq (fun r v => lutB I_c2 [false, false, v, r, false, false]) pr pq 0 q) :
    ∀ t, 0 ≤ t → q t = false := by
  intro t ht; rw [hL t ht]; exact (inputs0_force _ _).1

/-! ## 7. Counter-trace and witness with numbers -/

/-- bd_c2 held at `(1, 0)`, power-up 1, rst path 500 ps, loop 400 ps, rst
driver high for 399 ps: the cell is 0 on [500, 899) and 1 AGAIN at 899
(the reset value is lost; transport loop: it recirculates). Holds for EVERY
trace meeting H_PIN_READ from that power-up. -/
theorem c2_short_reset (q : Int → Bool)
    (hL : LoopEq Fc2 (Rd.const 500) (Rd.const ((400 : Nat) : Int)) 399 q)
    (hP : ∀ t, t < 0 → q t = true) :
    q 600 = false ∧ q 899 = true := by
  have A := before_forced cells.1 (Rd.const 500) 500 500 399 ((400 : Nat) : Int) (by omega) q
    (fun t => by simp [Rd.const]) hL hP
  constructor
  · rw [hL 600 (by omega)]
    have : pulse 0 399 ((Rd.const 500).σ 600) = true := by decide
    rw [this]; exact cells.1.force _
  · rw [hL 899 (by omega)]
    have : pulse 0 399 ((Rd.const 500).σ 899) = false := by decide
    rw [this, cells.1.hold]
    exact A _ (by simp [Rd.const])

/-- Same cell with the rst pulse at 400 ps (= the loop): 0 from 500 for ever. -/
theorem c2_ok_reset (q : Int → Bool)
    (hL : LoopEq Fc2 (Rd.const 500) (Rd.const ((400 : Nat) : Int)) 400 q) :
    ResetOK false 500 q :=
  reset_ok cells.1 _ _ 400 500 500 400 q (by omega) (by simp [Rd.const]) (by simp [Rd.const])
    (by simp [Rd.const]) (by simp [Rd.const]) (by omega) hL

/-- Non-vacuity of both: traces exist (power-up 1). -/
theorem c2_traces_exist :
    LoopEq Fc2 (Rd.const 500) (Rd.const ((400 : Nat) : Int)) 399
      (runB (fun t v => Fc2 (pulse 0 399 ((Rd.const 500).σ t)) v) 400 true (by decide)) ∧
    LoopEq Fc2 (Rd.const 500) (Rd.const ((400 : Nat) : Int)) 400
      (runB (fun t v => Fc2 (pulse 0 400 ((Rd.const 500).σ t)) v) 400 true (by decide)) :=
  ⟨runB_loopEq _ _ _ 400 true (by decide), runB_loopEq _ _ _ 400 true (by decide)⟩

/-! ## 8. The JSON box form versus the exact box -/

/-- prjxray-shaped numbers (ps): rst wire [200, 300], rst site pin A4
[86, 284], O6 arc [45, 124] (flat over pins, used for BOTH the rst arc and the
feedback arc), feedback wire [100, 150], feedback site pin A3 [107, 344].
JSON `design.rst_hold`, box mode: `w.hi + SP.hi + dlmax + dwmax + SPfb.hi + 1
≤ W + w.lo + SP.lo` holds at `W = 917`; the exact per-pin box condition
`Rhi + Qhi ≤ W + Rlo` with `Rhi = 300+284+124`, `Rlo = 200+86+45`,
`Qhi = 124+150+344` fails (it needs `W ≥ 995`). -/
theorem json_box_gap :
    (300 + 284 + 124 + 150 + 344 + 1 : Int) ≤ 917 + 200 + 86 ∧
    ¬ ((300 + 284 + 124 : Int) + (124 + 150 + 344) ≤ 917 + (200 + 86 + 45)) ∧
    ((300 + 284 + 124 : Int) + (124 + 150 + 344) ≤ 995 + (200 + 86 + 45)) := by decide

/-- ... so by `c2_box_exact` some admissible read maps and trace of the real
bd_c2 break ResetOK at `W = 917` in that box. -/
theorem json_box_gap_fails :
    ¬ (∀ pr pq : Rd, (200 + 86 + 45 : Int) ≤ pr.lo → pr.hi ≤ 300 + 284 + 124 →
      (1 : Int) ≤ pq.lo → pq.hi ≤ 124 + 150 + 344 →
      ∀ q, LoopEq Fc2 pr pq 917 q → ResetOK false (300 + 284 + 124) q) := by
  intro h
  have := (c2_box_exact 917 (200 + 86 + 45) (300 + 284 + 124) 1 (124 + 150 + 344)
    (by decide) (by decide) (by decide) (by decide)).mp h
  exact json_box_gap.2.1 this

/-! ## 9. Kleene remark (pointwise, real INIT) -/

/-- rst read X while the feedback reads the reset value: output definite 0. -/
theorem kleene_release_harmless :
    lutK I_c2 [.t, .f, .f, .x, .f, .f] = .f ∧ lutK I_c2n [.f, .f, .f, .x, .f, .f] = .f ∧
    lutK I_c3 [.t, .f, .f, .f, .x, .f] = .f ∧ lutK I_c4 [.t, .f, .f, .f, .f, .x] = .f := by
  decide

/-- rst read X while the feedback still reads the non-reset value: X. -/
theorem kleene_rise_x :
    lutK I_c2 [.t, .f, .t, .x, .f, .f] = .x ∧ lutK I_c2n [.f, .f, .t, .x, .f, .f] = .x := by
  decide


/-! ## 10. "Released before the first request" is NOT necessary; H_NO_RETURN is

Every reset row also says "release before the first request reaches the
pins" (`bd_c*.reset_width`; `H_RST_EARLY` of `bd_merge.reset_first` /
`bd_mux.reset_first`; `design.rst_release_skew`). Per-pin bd_c2, all four
pins read through fixed delays (`C2Eq`): a request that reaches its pin
WHILE rst is still read high and then STAYS (four-phase: it cannot return
before the acknowledge, which reset holds at 0) is processed exactly as if
it had arrived at release (`early_request_ok`). What does break the cell is
an input pulse that rises and falls while rst is read high
(`returned_pulse_lost`): the event is lost. -/

/-- **H_PIN_READ** for bd_c2 with every pin read (fixed delays). -/
def C2Eq (da db dr : Int) (dq : Int) (W : Int) (a b q : Int → Bool) : Prop :=
  ∀ t, 0 ≤ t → q t = lutB I_c2 [a (t - da), b (t - db), q (t - dq), pulse 0 W (t - dr), false, false]

theorem c2_low_b : ∀ a q r : Bool, q = false → lutB I_c2 [a, false, q, r, false, false] = false := by
  decide
theorem c2_rst_low : ∀ a b q : Bool, lutB I_c2 [a, b, q, true, false, false] = false := by decide
theorem c2_fire : ∀ q : Bool, lutB I_c2 [true, true, q, false, false, false] = true := by decide

/-- **Early request, harmless.** `a` rises at `A` (ANY time: here it may
reach its pin during reset) and stays; `b` rises at `B` and stays, read after
the release is read (`W + dr ≤ B + db`). With the exact reset width
(`dq ≤ W`), from `dr` on the cell is exactly the clean response: 0 until
`B + db`, 1 from there. Nothing about `A` beyond `A + da ≤ B + db`. -/
theorem early_request_ok (da db dr dq W A B : Int) (a b q : Int → Bool)
    (ha : ∀ t, a t = decide (A ≤ t)) (hb : ∀ t, b t = decide (B ≤ t))
    (hdr : 0 ≤ dr) (hdq : 1 ≤ dq) (H_RST_WIDTH : dq ≤ W)
    (H_B_AFTER_RELEASE : W + dr ≤ B + db) (H_A_BEFORE_B : A + da ≤ B + db)
    (hL : C2Eq da db dr dq W a b q) :
    ∀ t, dr ≤ t → q t = decide (B + db ≤ t) := by
  apply int_ind (fun t => dr ≤ t → q t = decide (B + db ≤ t)) (fun t ht h => by omega)
  intro t ht ih h1
  rw [hL t ht]
  by_cases hr : t < W + dr
  · have : pulse 0 W (t - dr) = true := by simp [pulse]; omega
    rw [this, c2_rst_low]
    symm; simp; omega
  · have hp : pulse 0 W (t - dr) = false := by simp [pulse]; omega
    rw [hp]
    by_cases hbt : B + db ≤ t
    · rw [ha, hb, decide_eq_true (by omega), decide_eq_true (by omega), c2_fire]
      symm; simp; omega
    · rw [hb, decide_eq_false (by omega)]
      rw [c2_low_b _ _ _ (by rw [ih _ (by omega) (by omega)]; simp; omega)]
      symm; simp; omega

/-- **Returned pulse, lost (H_NO_RETURN is needed).** `a` arbitrary (e.g. high for ever),
`b` high on `[B, B')` only, the whole pulse read while rst is read high
(`B' + db ≤ W + dr`), reset width exact. The cell is 0 at every `t ≥ dr`:
the enabling event never produces its acknowledge. -/
theorem returned_pulse_lost (da db dr dq W B B' : Int) (a b q : Int → Bool)
    (hb : ∀ t, b t = decide (B ≤ t ∧ t < B'))
    (hdr : 0 ≤ dr) (hdq : 1 ≤ dq) (H_RST_WIDTH : dq ≤ W)
    (H_RETURNED : B' + db ≤ W + dr) (hL : C2Eq da db dr dq W a b q) :
    ∀ t, dr ≤ t → q t = false := by
  apply int_ind (fun t => dr ≤ t → q t = false) (fun t ht h => by omega)
  intro t ht ih h1
  rw [hL t ht]
  by_cases hr : t < W + dr
  · have : pulse 0 W (t - dr) = true := by simp [pulse]; omega
    rw [this, c2_rst_low]
  · have hp : pulse 0 W (t - dr) = false := by simp [pulse]; omega
    rw [hp, hb, decide_eq_false (by omega)]
    exact c2_low_b _ _ _ (ih _ (by omega) (by omega))

/-- Numbers (non-vacuity / the violation is real): rst `[0, 1000)` read
through 500 ps, so released at the pin from 1500; loop 400 ps. `a` rises at
100 and is read through 300 ps: it reaches its pin at 400, DURING reset
(H_RST_EARLY violated by 1100 ps). `b` rises at 2000, read through 300 ps.
Every trace is 0 at 2299 and 1 at 2300 (the clean response). Traces exist. -/
theorem early_request_numbers (q : Int → Bool)
    (hL : C2Eq 300 300 500 400 1000 (fun t => decide (100 ≤ t)) (fun t => decide (2000 ≤ t)) q) :
    (100 : Int) + 300 < 1000 + 500 ∧ q 2299 = false ∧ q 2300 = true := by
  have h := early_request_ok 300 300 500 400 1000 100 2000 _ _ q (fun _ => rfl) (fun _ => rfl)
    (by omega) (by omega) (by omega) (by omega) (by omega) hL
  refine ⟨by omega, ?_, ?_⟩
  · rw [h 2299 (by omega)]; decide
  · rw [h 2300 (by omega)]; decide

theorem early_request_exists (p : Bool) :
    C2Eq 300 300 500 400 1000 (fun t => decide (100 ≤ t)) (fun t => decide (2000 ≤ t))
      (runB (fun t v => lutB I_c2 [decide (100 ≤ t - 300), decide (2000 ≤ t - 300), v,
        pulse 0 1000 (t - 500), false, false]) 400 p (by decide)) := by
  intro t ht
  exact runB_eq _ 400 p (by decide) t ht

end Formal.Cells.NecessityReset
