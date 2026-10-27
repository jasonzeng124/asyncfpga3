import Formal.Cells.CElemStrict
import Formal.Cells.LibGapMuxN
import Formal.Cells.LibGapLatch
import Formal.Cells.NecessityReset
/-!
# Self-audit of shard B (probe Bsa2), part 5: non-degenerate witnesses for the box-exact theorems

The headline "exact over the box" theorems of LibGapSteer, LibGapMux, LibGapMuxN,
LibGapLatch, NecessityReset and CElemStrict are witnessed in their files only by runs
with CONSTANT read maps (lo = hi): the box is nonempty, but no run with a read map that
actually moves inside its window was shown to meet the hypotheses. Here each one gets a
run in which every read map that the cell's trace constructor lets vary is
**non-monotone and spans its window with lo < hi** (`alt lo hi`: even instants read through
`lo`, odd instants through `hi`), every hypothesis of the theorem's left side holds, the
box inequalities hold with lo < hi, and the conclusion is non-trivial (the selected output
fires / the latch writes / the reset value is reached from the non-reset power-up value).

What stays constant: the feedback read map `pq` (the trace constructors `run`/`runB`
take a fixed loop delay); for LibGapMuxN also the request and decode->join maps. The box
for those still has lo < hi; only the run's own map is a point inside it.

Core Lean only; no sorry, no axiom, no native_decide.
-/
namespace Formal.Cells.SelfAuditB5
open Formal.Cells
open Formal.Cells.LibGapSteer (Rd Rd.const pulse Stable sAdv sAdv_stable SpecOK outB)

/-- A non-monotone read map spanning `[lo, hi]`: even instants read `t - lo`,
odd instants `t - hi`. -/
def alt (lo hi : Int) (h : lo ≤ hi) : Rd :=
  ⟨fun t => if t % 2 = 0 then t - lo else t - hi, lo, hi,
   fun t => by split <;> omega, fun t => by split <;> omega⟩

theorem alt_nonmono (lo hi : Int) (h : lo + 1 < hi) :
    (alt lo hi (by omega)).σ 1 < (alt lo hi (by omega)).σ 0 := by
  show (if (1 : Int) % 2 = 0 then 1 - lo else 1 - hi) < (if (0 : Int) % 2 = 0 then 0 - lo else 0 - hi)
  simp; omega

/-! ## 1. LibGapSteer.steer_box_exact -/

def sr : Rd := alt 200 400 (by decide)
def ss : Rd := alt 300 600 (by decide)

/-- Box `req ∈ [200, 400]`, `s ∈ [300, 600]` (both read maps non-monotone, spanning the
box), token `[1000, 3000)`, `s = 1` on `[500, 4000)`, `!s` outside: every hypothesis of
the left side, the box inequalities, SpecOK on both branches, and the selected branch
O6 is high at 1400 while O5 is low there. -/
theorem steer_nd :
    (500 : Int) + 600 ≤ 1000 + 200 ∧ (3000 : Int) + 400 ≤ 4000 + 300 ∧
    SpecOK true true sr ss 1000 3000 (sAdv true 500 4000) ∧
    SpecOK false true sr ss 1000 3000 (sAdv true 500 4000) ∧
    outB true (pulse 1000 3000 (sr.σ 1400)) (sAdv true 500 4000 (ss.σ 1400)) = true ∧
    outB false (pulse 1000 3000 (sr.σ 1400)) (sAdv true 500 4000 (ss.σ 1400)) = false := by
  have H := fun b => (LibGapSteer.steer_box_exact b true 200 400 300 600 1000 3000 500 4000
    (by decide) (by decide) (by decide)).mpr ⟨by decide, by decide⟩ sr ss
    (Int.le_refl _) (Int.le_refl _) (Int.le_refl _) (Int.le_refl _) _ (sAdv_stable true 500 4000)
  refine ⟨by decide, by decide, H true, H false, ?_, ?_⟩ <;> decide

/-! ## 2. LibGapMux.join_box_exact -/

open Formal.Cells.LibGapMux (LutEq Rest JSpec jB run run_eq run_rest unsel_low sel_fires)

def mr : Rd := alt 0 80 (by decide)
def mc : Rd := alt 200 400 (by decide)
def ms : Rd := alt 300 600 (by decide)

/-- The join trace for non-constant request / ctl_req / select read maps and a 100 ps
feedback loop, both requests waiting. -/
def jN (b : Bool) : Int → Bool :=
  run (fun t q => jB b ((fun _ => true) (mr.σ t)) (pulse 1000 3000 (mc.σ t))
    (sAdv true 500 4000 (ms.σ t)) q) 100 (by decide)

theorem jN_luteq (b : Bool) :
    LutEq b mr mc ms (Rd.const (100 : Nat)) (fun _ => true) (pulse 1000 3000) (sAdv true 500 4000) (jN b) :=
  fun t ht => run_eq _ 100 (by decide) t ht

/-- Box `r ∈ [0, 80]`, `ctl_req ∈ [200, 400]`, `s ∈ [300, 600]` (all non-monotone),
feedback in `[50, 150]` (run at 100): every hypothesis of `join_box_exact`'s left side
holds for both joins, the box inequalities hold, uj1 (selected) is 1 at 1600 and uj0
(unselected, x_req waiting) is 0 at every instant. -/
theorem join_nd :
    (500 : Int) + 600 ≤ 1000 + 200 ∧ (3000 : Int) + 400 ≤ 4000 + 300 ∧
    jN true 1600 = true ∧ ∀ t, jN false t = false := by
  have H := fun b => (LibGapMux.join_box_exact b true 0 80 200 400 300 600 50 150 1000 3000 500 4000
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).mpr
    ⟨by decide, by decide⟩ mr mc ms (Rd.const (100 : Nat)) (Int.le_refl _) (Int.le_refl _) (Int.le_refl _)
    (Int.le_refl _) (Int.le_refl _) (Int.le_refl _) (by show (50 : Int) ≤ 100; decide)
    (by show (100 : Int) ≤ 150; decide) _ _ (jN b) (sAdv_stable true 500 4000) (jN_luteq b)
    (run_rest _ 100 (by decide))
  refine ⟨by decide, by decide, ?_, ?_⟩
  · exact sel_fires true mr mc (Rd.const (100 : Nat)) _ _ _ (H true) 1600 (by decide) rfl (by decide)
  · exact unsel_low false true (by decide) mr mc (Rd.const (100 : Nat)) (by show (1 : Int) ≤ 100; decide)
      _ _ _ (H false) (run_rest _ 100 (by decide))

/-! ## 3. LibGapMuxN.sel_box_exact (decode pins non-monotone) -/

section MuxN
open Formal.Cells.LibGapMuxN

def n0 : Rd := alt 100 450 (by decide)
def n1 : Rd := alt 100 450 (by decide)
def nc : Rd := alt 250 350 (by decide)
def s0N : Int → Bool := sW (bit0 2) (!bit0 2) 500 4000
def s1N : Int → Bool := sW (bit1 2) (!bit1 2) 500 4000
def DN : Int → Bool := fun t => dec 2 (s0N (n0.σ t)) (s1N (n1.σ t)) (pulse 1000 3000 (nc.σ t))
def jMN : Int → Bool := LibGapMux.run (jfN 0 100 (fun _ => true) DN) 50 (by decide)

/-- Join 2 of `bdc_muxn3`, token `v = 2`: index bits stable on `[500, 4000)`, wrong code
outside; the two index pins read through non-monotone maps spanning `[100, 450]`, ctl_req
through one spanning `[250, 350]`; the box (request `[0, 10]`, decode->join `[100, 200]`,
feedback `[50, 60]`) meets `SelCond`; every hypothesis of `sel_box_exact`'s left side
holds and join 2 fires at 1400. -/
theorem muxn_nd : SelCond 250 350 100 450 100 450 1000 3000 500 4000 500 4000 ∧ jMN 1400 = true := by
  have hD : DecEq 2 n0 n1 nc s0N s1N (pulse 1000 3000) DN := fun _ => rfl
  have hJ := run_jeq 0 100 50 (by decide) (fun _ => true) DN
  have B := (sel_box_exact 2 (by decide) 0 10 100 200 250 350 100 450 100 450 50 60 1000 3000
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) 500 4000 500 4000).mpr selcond_witness s0N s1N (sW_stable _ _ _ _) (sW_stable _ _ _ _)
    (C 0) (C 100) nc n0 n1 (C 50) (inbox_const (by decide) (by decide))
    (inbox_const (by decide) (by decide)) ⟨Int.le_refl _, Int.le_refl _⟩ ⟨Int.le_refl _, Int.le_refl _⟩
    ⟨Int.le_refl _, Int.le_refl _⟩ (inbox_const (by decide) (by decide)) _ _ _ hD hJ
    (LibGapMux.run_rest _ 50 (by decide))
  exact ⟨selcond_witness, sel_fires 2 _ _ _ _ _ _ _ B 1400 (by decide) rfl (by decide)⟩

end MuxN

/-! ## 4. LibGapLatch.box_exact -/

section Latch
open Formal.Cells.LibGapLatch

def ld : Rd := alt 300 700 (by decide)
def le' : Rd := alt 400 800 (by decide)
def wqN : Int → K3 :=
  LibGapLatch.run (lf ld le' (dAdv true 1000 3801) (eAdv 2000 3300 3301)) (kb false) 700 (by decide)

/-- Box `d ∈ [300, 700]`, `en ∈ [400, 800]` (both non-monotone, spanning the box),
feedback `[300, 900]` (run at 700), power-up 0, enable `[2000, 3300)`, X on `[3300,
3301)`, data 1 on `[1000, 3801)`, 0 outside: the three box inequalities hold (setup_pulse
and hold with slack 0), every hypothesis of `box_exact`'s left side holds, the latch is 0
before time 0 and captures 1 at every instant whose enable read is closed; such instants
exist (4200). -/
theorem latch_nd :
    ((2000 : Int) + 800 + 900 ≤ 3300 + 400 ∧ (1000 : Int) + 700 + 900 ≤ 3300 + 400 ∧
      (3301 : Int) + 800 ≤ 3801 + 300) ∧
    wqN (-1) = kb false ∧ Capt true 3300 le' wqN ∧ 3300 ≤ le'.σ 4200 ∧ 3300 ≤ le'.σ 4201 := by
  have hL : LutEq ld le' (Rd.const (700 : Nat)) (dAdv true 1000 3801) (eAdv 2000 3300 3301) wqN :=
    run_luteq _ _ _ _ _ 700 (by decide)
  refine ⟨⟨by decide, by decide, by decide⟩, run_neg _ _ _ _ _ (by decide), ?_, by decide, by decide⟩
  exact (box_exact true 2000 3300 3301 1000 3801 300 700 400 800 300 900 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).mpr
      ⟨by decide, by decide, by decide⟩ ld le' _ (Int.le_refl _) (Int.le_refl _) (Int.le_refl _) (Int.le_refl _)
      (by show (300 : Int) ≤ 700; decide) (by show (700 : Int) ≤ 900; decide)
      _ _ _ (dAdv_stab _ _ _) (eAdv_tok (by decide) (by decide)) hL

end Latch

/-! ## 5. NecessityReset.c2_box_exact -/

section Reset
open Formal.Cells.NecessityReset

def rr : Rd := alt 100 300 (by decide)
def qR : Int → Bool := runB (fun t v => Fc2 (pulse 0 350 (rr.σ t)) v) 100 true (by decide)

/-- bd_c2 (real INIT) held at `a = 1, b = 0`, powered up at the NON-reset value 1, rst
`[0, 350)` read through a non-monotone map spanning `[100, 300]`, loop 100 in the box
`[50, 150]`: `Rhi + Qhi = 450 ≤ W + Rlo = 450` (slack 0), every hypothesis holds, and the
cell is 1 before 0 and 0 from 300 on, for ever. -/
theorem reset_nd : (300 : Int) + 150 ≤ 350 + 100 ∧ qR (-1) = true ∧ ResetOK false 300 qR := by
  refine ⟨by decide, runB_pre _ _ _ _ _ (by decide), ?_⟩
  exact (c2_box_exact 350 100 300 50 150 (by decide) (by decide) (by decide) (by decide)).mpr
    (by decide) rr (Rd.const (100 : Nat)) (Int.le_refl _) (Int.le_refl _) (by show (50 : Int) ≤ 100; decide)
    (by show (100 : Int) ≤ 150; decide) _ (runB_loopEq _ _ _ _ _ _)

end Reset

/-! ## 6. CElemStrict.box_iff / env_latency_iff with lo < hi -/

section CE
open Formal.Cells.CElemStrict

abbrev cyc := c2Cycle false false true

/-- Delay box `D ∈ [200, 420]` (lo < hi), follow X window 1, release X window 1:
safe for every D in the box and every release start from 421 on; NOT safe from 420
(the necessity direction at a non-point box). -/
theorem celem_box_nd :
    SafeBox c2F cyc.1 cyc.2.1 cyc.2.2.1 cyc.2.2.2.1 cyc.2.2.2.2 false true 0 1 1 200 420 421 ∧
    ¬ SafeBox c2F cyc.1 cyc.2.1 cyc.2.2.1 cyc.2.2.2.1 cyc.2.2.2.2 false true 0 1 1 200 420 420 :=
  ⟨(box_iff (c2_all false false true) (by decide) (by decide) (by decide)).mpr (by decide),
   fun h => absurd ((box_iff (c2_all false false true) (by decide) (by decide) (by decide)).mp h)
     (by decide)⟩

/-- A concrete behaviour strictly inside that box (D = 300, release start 500): clean. -/
theorem celem_inside :
    Spec false true 0 1 (simG c2F (phase cyc.1 cyc.2.1 cyc.2.2.1 cyc.2.2.2.1 cyc.2.2.2.2 0 1 500 1) false 299) :=
  clean (sim_loop _ _ _ _ (fun _ => rfl)) (c2_all false false true) (by omega) (by omega)

/-- `env_latency_iff` with a non-degenerate arc band `dlmin = 100 < dlmax = 124`
(prjxray-like LUT arc), feedback wire up to 300, E = 325, one tick of X: safe exactly at
`124 + 300 + 1 ≤ 100 + 325`, unsafe at E = 324. -/
theorem env_nd :
    SafeBox c2F cyc.1 cyc.2.1 cyc.2.2.1 cyc.2.2.2.1 cyc.2.2.2.2 false true 0 1 1 150 (124 + 300)
      (0 + 1 + 100 + 325 - 1) ∧
    ¬ SafeBox c2F cyc.1 cyc.2.1 cyc.2.2.1 cyc.2.2.2.1 cyc.2.2.2.2 false true 0 1 1 150 (124 + 300)
      (0 + 1 + 100 + 324 - 1) :=
  ⟨(env_latency_iff (dlmin := 100) (E := 325) (c2_all false false true) (by decide) (by decide)
      (by decide)).mpr (by decide),
   fun h => absurd ((env_latency_iff (dlmin := 100) (E := 324) (c2_all false false true) (by decide)
      (by decide) (by decide)).mp h) (by decide)⟩

end CE

end Formal.Cells.SelfAuditB5
