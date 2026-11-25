-- MUTANT M04_ArbAMergeRunWit of Formal/Cells/ArbAMergeRunWit.lean: witness server answers in 2 ps (A0 t = R0 (t - 2)) under smin = 3 (must FAIL)
import Formal.Cells.ArbAMergeRunStitch

/-!
# Probe Barb4 (part 3): non-vacuity of the schedule class, and the H_SEP counter-run

* **`amerge_witness`** (non-vacuity of `amerge_of_plan`): one run from reset, every delay
  nonzero (`Dw`: 1 ps per route and arc, server minimum 3 ps, the server the pure delay
  `A0 t = R0 (t - 3)`), z line 2 ps, CHECKED against every gate relation and the server
  relation at every `t ∈ ℤ` (`Wt_run`), with a schedule `Wplan` covering: the reset epoch,
  grant from idle with a waiter arriving, handover 1 → 2 with an early re-request, handover
  2 → 1, a solo re-request (same client wins twice), release to idle, the idle race with
  client 2 first under H_SEP (q flips), handover 2 → 1, release to idle, idle for ever.
  C's `AMerge` holds on it (data buses chosen to meet H_DAT).
* **`sep_cex_run`**: without H_SEP, B's model admits a run violating C's fields: a
  from-reset run meeting every hypothesis of the idle-race window `WX` except H_SEP (loop
  clause missed by exactly 1 ps) in which q, g2 and g1 make 1 ps runts and both H_ARB2 and
  H_ARB1 fail.
* Tools: `tb` (traces as tables), `chk`, `range_chk`, `all_int` (bounded checks by kernel
  `decide`, the unbounded rest by `tb_lo` / `tb_hi`).

Traces come from a scratch simulator (`/tmp/claude-0/probes/Barb4/gen.py`, `gen_sep.py`);
Lean re-checks them, so the simulator is not trusted. **Assumed:** nothing (concrete).
**NOT covered:** a witness for the mirror epochs (not in the class); a concrete run for
`cex_RA1` (it is a universal lemma only).
-/

set_option maxRecDepth 100000

namespace Formal.Cells.ArbAMergeRun
open Formal.Cells Formal.Cells.ArbHeldTimed Formal.Cells.ArbHeldTimed2
open Formal.Cells.ArbMultiToken (MB Dw Dw_MB Dw_rt CArb)
open Formal.Cells.ArbAMerge

/-! ## Finite tables and bounded checks -/

/-- A trace given by a table on `[0, length)`, the value `i` before 0 and `f` after. -/
def tb (l : List Bool) (i f : Bool) (t : Int) : Bool := if t < 0 then i else l.getD t.toNat f

theorem tb_lo {l : List Bool} {i f : Bool} {t : Int} (h : t < 0) : tb l i f t = i := by
  simp [tb, h]

theorem tb_hi {l : List Bool} {N : Nat} (hl : l.length = N) {i f : Bool} {t : Int} (h : (N : Int) ≤ t) :
    tb l i f t = f := by
  unfold tb
  rw [ite_cond_eq_false _ _ (by simp; omega), List.getD_eq_getElem?_getD]
  have : l[t.toNat]? = none := by rw [List.getElem?_eq_none_iff]; omega
  rw [this]; rfl

/-- `chk f lo n`: `f` holds at `lo, lo + 1, ..., lo + n - 1`. -/
def chk (f : Int → Bool) (lo : Int) : Nat → Bool
  | 0 => true
  | n + 1 => f (lo + n) && chk f lo n

theorem chk_ok {f : Int → Bool} {lo : Int} : ∀ {n : Nat}, chk f lo n = true →
    ∀ t, lo ≤ t → t < lo + n → f t = true := by
  intro n
  induction n with
  | zero => intro _ t h1 h2; omega
  | succ n ih =>
    intro h t h1 h2
    simp only [chk, Bool.and_eq_true] at h
    by_cases ht : t = lo + n
    · rw [ht]; exact h.1
    · exact ih h.2 t h1 (by omega)

theorem range_chk {P : Int → Prop} [DecidablePred P] (lo hi : Int)
    (h : chk (fun t => decide (P t)) lo (hi - lo).toNat = true) :
    ∀ t, lo ≤ t → t < hi → P t := by
  intro t h1 h2
  have := chk_ok h t h1 (by omega)
  simpa using this

theorem all_int {P : Int → Prop} [DecidablePred P] (lo hi : Int) (hl : ∀ t, t < lo → P t)
    (hh : ∀ t, hi ≤ t → P t) (hm : chk (fun t => decide (P t)) lo (hi - lo).toNat = true) :
    ∀ t, P t := by
  intro t
  by_cases h1 : t < lo
  · exact hl t h1
  by_cases h2 : hi ≤ t
  · exact hh t h2
  exact range_chk lo hi hm t (by omega) (by omega)

/-! ## The witness run (from a scratch simulation, `/tmp/claude-0/probes/Barb4/gen.py`)

Delays `Dw` (every route and arc 1 ps, server minimum 3 ps), `M = 2`, z line `dz = 2`, the
server the pure delay `A0 t = R0 (t - 3)`. Reset past: every signal low, q = 1. Client 1
requests at 20 (grant from idle), client 2 at 30 (waits); client 1 releases at 50 and
re-requests EARLY at 58 (handover 1 → 2); client 2 releases at 90 without re-requesting
(handover 2 → 1); client 1 releases at 120 and re-requests at 128 with nobody waiting (solo,
same client wins twice), releases at 160 for good (release to idle); client 2 requests at 200
from idle (q flips), client 1 at 205 (H_SEP met with slack 3); client 2 releases at 240
(handover 2 → 1); client 1 releases at 270; idle for ever after. The traces are tables on
`[0, 300)`, CHECKED here against every gate relation and the server relation at every
`t ∈ ℤ`. -/

def Lr1 : List Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]
theorem Lr1_len : Lr1.length = 300 := rfl
def Lr2 : List Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]
theorem Lr2_len : Lr2.length = 300 := rfl
def Lq : List Bool := [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]
theorem Lq_len : Lq.length = 300 := rfl
def LR0 : List Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]
theorem LR0_len : LR0.length = 300 := rfl
def Lg1 : List Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]
theorem Lg1_len : Lg1.length = 300 := rfl
def Lg2 : List Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]
theorem Lg2_len : Lg2.length = 300 := rfl
def LA1 : List Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]
theorem LA1_len : LA1.length = 300 := rfl
def LA2 : List Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]
theorem LA2_len : LA2.length = 300 := rfl

def Wt : Sigs where
  r1 := tb Lr1 false false
  r2 := tb Lr2 false false
  q := tb Lq true true
  R0 := tb LR0 false false
  g1 := tb Lg1 false false
  g2 := tb Lg2 false false
  A0 := fun t => tb LR0 false false (t - 2)
  A1 := tb LA1 false false
  A2 := tb LA2 false false

def zt : Int → Bool := fun t => Wt.R0 (t - 2)

theorem zt_line : ZLine Wt zt 2 := fun _ => rfl

theorem Wt_srv : Server Dw.smin Wt.R0 Wt.A0 := by
  have key : ∀ t, (Wt.A0 t ≠ Wt.A0 (t - 1) → Wt.A0 (t - 3) = Wt.A0 (t - 1) ∧
      Wt.A0 (t - 2) = Wt.A0 (t - 1)) := by
    refine all_int 0 310 (fun t h => ?_) (fun t h => ?_) (by decide +kernel)
    · simp only [Wt]; simp (disch := omega) only [tb_lo]; simp
    · simp only [Wt]; simp (disch := omega) only [tb_hi LR0_len]; simp
  intro t h
  refine ⟨t - 3, by simp [Dw], rfl, fun v h1 h2 => ?_⟩
  obtain ⟨k1, k2⟩ := key t h
  have : v = t - 3 ∨ v = t - 2 ∨ v = t - 1 := by omega
  rcases this with rfl | rfl | rfl
  · exact k1
  · exact k2
  · rfl

macro "lo_tac" : tactic => `(tactic| (simp only [Wt, Dw]; simp (disch := omega) only [tb_lo] <;> decide))
macro "hi_tac" : tactic => `(tactic| (simp only [Wt, Dw]; simp (disch := omega) only [tb_hi Lq_len,
  tb_hi Lr1_len, tb_hi Lr2_len, tb_hi LR0_len, tb_hi Lg1_len, tb_hi Lg2_len, tb_hi LA1_len,
  tb_hi LA2_len] <;> decide))

theorem Wt_H_q : ∀ t, Wt.q t = (FS (Wt.r1 (t - Dw.wr1s - Dw.qr)) (Wt.r2 (t - Dw.wr2s - Dw.qr)) (Wt.q (t - Dw.wfb - Dw.qr)) (Wt.A0 (t - Dw.wa0s - Dw.qr)) || FS (Wt.r1 (t - Dw.wr1s - Dw.qf)) (Wt.r2 (t - Dw.wr2s - Dw.qf)) (Wt.q (t - Dw.wfb - Dw.qf)) (Wt.A0 (t - Dw.wa0s - Dw.qf))) := by
  refine all_int 0 310 (fun t h => ?_) (fun t h => ?_) ?_
  · lo_tac
  · hi_tac
  · decide +kernel

theorem Wt_H_R0 : ∀ t, Wt.R0 t = (FR (Wt.r1 (t - Dw.wr1s - Dw.Rr1)) (Wt.r2 (t - Dw.wr2s - Dw.Rr2)) (Wt.q (t - Dw.wfb - Dw.Rrq)) || FR (Wt.r1 (t - Dw.wr1s - Dw.Rf1)) (Wt.r2 (t - Dw.wr2s - Dw.Rf2)) (Wt.q (t - Dw.wfb - Dw.Rfq))) := by
  refine all_int 0 310 (fun t h => ?_) (fun t h => ?_) ?_
  · lo_tac
  · hi_tac
  · decide +kernel

theorem Wt_H_g1 : ∀ t, Wt.g1 t = (FG1 (Wt.r1 (t - Dw.wr1g - Dw.g1r1)) (Wt.r2 (t - Dw.wr2g - Dw.g1r2)) (Wt.q (t - Dw.wq - Dw.g1rq)) || FG1 (Wt.r1 (t - Dw.wr1g - Dw.g1f1)) (Wt.r2 (t - Dw.wr2g - Dw.g1f2)) (Wt.q (t - Dw.wq - Dw.g1fq))) := by
  refine all_int 0 310 (fun t h => ?_) (fun t h => ?_) ?_
  · lo_tac
  · hi_tac
  · decide +kernel

theorem Wt_H_g2 : ∀ t, Wt.g2 t = (FG2 (Wt.r1 (t - Dw.wr1g - Dw.g2r)) (Wt.r2 (t - Dw.wr2g - Dw.g2r)) (Wt.q (t - Dw.wq - Dw.g2r)) || FG2 (Wt.r1 (t - Dw.wr1g - Dw.g2f)) (Wt.r2 (t - Dw.wr2g - Dw.g2f)) (Wt.q (t - Dw.wq - Dw.g2f))) := by
  refine all_int 0 310 (fun t h => ?_) (fun t h => ?_) ?_
  · lo_tac
  · hi_tac
  · decide +kernel

theorem Wt_H_A1 : ∀ t, Wt.A1 t = (CE (Wt.g1 (t - Dw.wg1 - Dw.c1r)) (Wt.A0 (t - Dw.wa01 - Dw.c1r)) (Wt.A1 (t - Dw.wfa1 - Dw.c1r)) || CE (Wt.g1 (t - Dw.wg1 - Dw.c1f)) (Wt.A0 (t - Dw.wa01 - Dw.c1f)) (Wt.A1 (t - Dw.wfa1 - Dw.c1f))) := by
  refine all_int 0 310 (fun t h => ?_) (fun t h => ?_) ?_
  · lo_tac
  · hi_tac
  · decide +kernel

theorem Wt_H_A2 : ∀ t, Wt.A2 t = (CE (Wt.g2 (t - Dw.wg2 - Dw.c2r)) (Wt.A0 (t - Dw.wa02 - Dw.c2r)) (Wt.A2 (t - Dw.wfa2 - Dw.c2r)) || CE (Wt.g2 (t - Dw.wg2 - Dw.c2f)) (Wt.A0 (t - Dw.wa02 - Dw.c2f)) (Wt.A2 (t - Dw.wfa2 - Dw.c2f))) := by
  refine all_int 0 310 (fun t h => ?_) (fun t h => ?_) ?_
  · lo_tac
  · hi_tac
  · decide +kernel

theorem Wt_run : Run Dw Wt :=
  ⟨Wt_H_q, Wt_H_R0, Wt_H_g1, Wt_H_g2, Wt_H_A1, Wt_H_A2, Wt_srv⟩

/-! ## The schedule of the witness run -/

-- fields: kind, a, L, t0, TA, TA2, u, v, Hz
def E0 : Ep := ⟨.hold .I false false, -10, -10, 0, 0, 0, 0, 0, 15⟩
def E1 : Ep := ⟨.wg, -10, 10, 0, 0, 25, 20, 30, 50⟩
def E2 : Ep := ⟨.e1, 25, 32, 50, 55, 62, 58, 0, 90⟩
def E3 : Ep := ⟨.e2, 62, 70, 90, 95, 102, 1000, 0, 120⟩
def E4 : Ep := ⟨.wrr, 102, 106, 120, 125, 133, 128, 200, 160⟩
def E5 : Ep := ⟨.wri, 133, 135, 160, 165, 195, 190, 200, 190⟩
def E6 : Ep := ⟨.wx, 165, 170, 0, 0, 207, 205, 200, 240⟩
def E7 : Ep := ⟨.e2, 207, 212, 240, 245, 252, 1000, 0, 270⟩
def E8 : Ep := ⟨.wri, 252, 256, 270, 275, 10010, 10000, 10000, 290⟩
def Et (j : Nat) : Ep := ⟨.hold .I false false, 275, 280 + 20 * (j : Int), 0, 0, 0, 0, 0, 310 + 20 * (j : Int)⟩

def Wep : Nat → Ep
  | 0 => E0 | 1 => E1 | 2 => E2 | 3 => E3 | 4 => E4 | 5 => E5 | 6 => E6 | 7 => E7 | 8 => E8
  | j + 9 => Et j

theorem Wt_tail : ∀ t, 280 ≤ t → Wt.r1 t = false ∧ Wt.r2 t = false ∧ Wt.A0 t = false := by
  intro t h
  by_cases h2 : t < 310
  · exact range_chk (P := fun t => Wt.r1 t = false ∧ Wt.r2 t = false ∧ Wt.A0 t = false)
      280 310 (by decide +kernel) t h h2
  · simp only [Wt]; simp (disch := omega) only [tb_hi Lr1_len, tb_hi Lr2_len, tb_hi LR0_len]
    simp

theorem ok0 : EpOK Dw 2 Wt 2 E0 :=
  epok_hold (m := .I) (c1 := false) (c2 := false) rfl fix_I (range_chk _ _ (by decide +kernel))
theorem ok1 : EpOK Dw 2 Wt 2 E1 :=
  epok_wg rfl (by decide) (range_chk _ _ (by decide +kernel)) (range_chk _ _ (by decide +kernel))
    (by decide) (range_chk _ _ (by decide +kernel)) (by constructor <;> decide)
theorem ok2 : EpOK Dw 2 Wt 2 E2 :=
  epok_e1 rfl (by decide) (range_chk _ _ (by decide +kernel)) (range_chk _ _ (by decide +kernel))
    (range_chk _ _ (by decide +kernel))
    ⟨by unfold RQ; decide, by unfold RRc; decide, by unfold RG; decide, Dw_rt.1, by decide,
      by decide, by decide⟩ (by constructor <;> decide)
theorem ok3 : EpOK Dw 2 Wt 2 E3 :=
  epok_e2 rfl (by decide) (range_chk _ _ (by decide +kernel)) (range_chk _ _ (by decide +kernel))
    (range_chk _ _ (by decide +kernel))
    ⟨by unfold RQ2; decide, by unfold RRc2; decide, by unfold RG2; decide, Dw_rt.2.2.1, by decide,
      by decide, by decide⟩ (by constructor <;> decide)
theorem ok4 : EpOK Dw 2 Wt 2 E4 :=
  epok_wrr rfl (by decide) (range_chk _ _ (by decide +kernel)) (range_chk _ _ (by decide +kernel))
    (by decide) (range_chk _ _ (by decide +kernel)) (by decide) (by constructor <;> decide)
theorem ok5 : EpOK Dw 2 Wt 2 E5 :=
  epok_wri rfl (by decide) (range_chk _ _ (by decide +kernel)) (range_chk _ _ (by decide +kernel))
    (by decide) (range_chk _ _ (by decide +kernel)) (by decide) (by constructor <;> decide)
theorem ok6 : EpOK Dw 2 Wt 2 E6 :=
  epok_wx rfl (by decide) (range_chk _ _ (by decide +kernel)) (range_chk _ _ (by decide +kernel))
    (range_chk _ _ (by decide +kernel)) (by constructor <;> decide) (by constructor <;> decide)
theorem ok7 : EpOK Dw 2 Wt 2 E7 :=
  epok_e2 rfl (by decide) (range_chk _ _ (by decide +kernel)) (range_chk _ _ (by decide +kernel))
    (range_chk _ _ (by decide +kernel))
    ⟨by unfold RQ2; decide, by unfold RRc2; decide, by unfold RG2; decide, Dw_rt.2.2.1, by decide,
      by decide, by decide⟩ (by constructor <;> decide)
theorem ok8 : EpOK Dw 2 Wt 2 E8 :=
  epok_wri rfl (by decide) (range_chk _ _ (by decide +kernel)) (range_chk _ _ (by decide +kernel))
    (by decide) (range_chk _ _ (by decide +kernel)) (by decide) (by constructor <;> decide)
theorem okt (j : Nat) : EpOK Dw 2 Wt 2 (Et j) :=
  epok_hold (m := .I) (c1 := false) (c2 := false) rfl fix_I
    (fun t h1 _ => Wt_tail t (by simp only [Et] at h1; omega))

theorem lk_t (j : Nat) : Link Dw 2 2 (Et j) (Et (j + 1)) := by
  unfold Link; refine ⟨rfl, rfl, ?_, ?_, ?_⟩ <;> simp only [Et, Lend, first] <;> omega

theorem Wep_ok : ∀ k, EpOK Dw 2 Wt 2 (Wep k)
  | 0 => ok0 | 1 => ok1 | 2 => ok2 | 3 => ok3 | 4 => ok4 | 5 => ok5 | 6 => ok6 | 7 => ok7
  | 8 => ok8 | j + 9 => okt j

theorem Wep_link : ∀ k, Link Dw 2 2 (Wep k) (Wep (k + 1))
  | 0 => by unfold Link; decide
  | 1 => by unfold Link; decide
  | 2 => by unfold Link; decide
  | 3 => by unfold Link; decide
  | 4 => by unfold Link; decide
  | 5 => by unfold Link; decide
  | 6 => by unfold Link; decide
  | 7 => by unfold Link; decide
  | 8 => by unfold Link; decide
  | j + 9 => lk_t j

theorem Wt_rst : ∀ t, t < 0 → InSt Wt .I t := by
  intro t h
  simp only [InSt, Wt]; simp (disch := omega) only [tb_lo]
  simp [Md.q, Md.g1, Md.g2, Md.A1, Md.A2, Md.R0]

/-- The witness schedule: reset (hold), grant from idle to client 1 with client 2 arriving,
handover 1 → 2 with an early re-request, handover 2 → 1, a solo re-request by client 1
(same client wins twice), a release to idle, the idle race with client 2 first under H_SEP
(q flips), handover 2 → 1, a release to idle, then idle for ever. -/
def Wplan : Plan Dw 2 Wt 2 where
  ep := Wep
  ok := Wep_ok
  link := Wep_link
  unb := fun t => ⟨(t - 280).toNat + 9, by show t < (Et _).Hz - 1; simp only [Et]; omega⟩
  k0 := rfl
  a0 := rfl
  L0 := by decide
  Hz0 := by decide
  rst := Wt_rst
  dz0 := by decide

open Formal.Net.Handshake (Chan) in
open Formal.Net.Ops.CM (AMerge) in
open Formal.Net.Ops.Mux (b2n) in
/-- **Non-vacuity of `amerge_of_plan`**: on the witness run (every delay nonzero, a real
server relation, from reset) C's `AMerge` holds, with the data buses chosen so that H_DAT
holds (`x.dat = 5`, `y.dat = 9`, `z.dat` the mux: B has no data timing model); the run
really contains the epoch kinds named in `Wplan` (checked on its kinds) and the grants
really move (g1 rises at 22, g2 at 59, g2 again at 204 after the idle race). -/
theorem amerge_witness :
    AMerge ⟨fun n => Wt.r1 n, fun n => Wt.A1 n, fun _ => 5⟩ ⟨fun n => Wt.r2 n, fun n => Wt.A2 n, fun _ => 9⟩
      ⟨fun n => zt n, fun n => Wt.A0 n,
        fun n => 2 * (if (Wt.g2 n || Wt.A2 n) then 9 else 5) + b2n (Wt.g2 n || Wt.A2 n)⟩
      (fun n => Wt.g1 n) (fun n => Wt.g2 n) ∧
    (Wplan.ep 0).k = .hold .I false false ∧ (Wplan.ep 1).k = .wg ∧ (Wplan.ep 2).k = .e1 ∧
    (Wplan.ep 3).k = .e2 ∧ (Wplan.ep 4).k = .wrr ∧ (Wplan.ep 5).k = .wri ∧
    (Wplan.ep 6).k = .wx ∧ (Wplan.ep 7).k = .e2 ∧ (Wplan.ep 8).k = .wri ∧
    Wt.g1 21 = false ∧ Wt.g1 22 = true ∧ Wt.g2 58 = false ∧ Wt.g2 59 = true ∧
    Wt.g2 203 = false ∧ Wt.g2 204 = true ∧ Wt.q 201 = true ∧ Wt.q 202 = false :=
  ⟨amerge_of_plan Wt_run Dw_MB zt_line Wplan _ _ _ (fun _ => rfl),
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-! ## H_SEP is needed: a concrete counter-run in the held arbiter's gate model

`Ds` = `Dw` with ustate's O6 fall arc 2 ps (rise 1 ps: the rise-fast channel, so a runt on
q shrinks and dies instead of circulating; rise = fall would make it circulate for ever, the
pure-transport artefact of `ArbBinary`). From reset (idle, q = 1) client 2 requests at 10 and
client 1 at 12: client 1's request reaches ustate 2 ps after client 2's, one tick before
q's fall has come round ustate's loop (H_SEP's loop clause missed by exactly 1 ps). q makes a
1 ps low runt at 13; g2 makes a 1 ps runt at 15 (and g1 one at 14); client 1 then wins.
Both C's H_ARB2 (g2 falls with r2 high) and H_ARB1 (g1 falls with r1 high) fail. The traces
(scratch `/tmp/claude-0/probes/Barb4/gen_sep.py`) are CHECKED against every gate relation
and the server relation at every `t ∈ ℤ`. -/

def Ds : Dl where
  wr1s := 1
  wr2s := 1
  wr1g := 1
  wr2g := 1
  wfb := 1
  wa0s := 1
  wq := 1
  wg1 := 1
  wa01 := 1
  wfa1 := 1
  wg2 := 1
  wa02 := 1
  wfa2 := 1
  qr := 1
  qf := 2
  Rr1 := 1
  Rf1 := 1
  Rr2 := 1
  Rf2 := 1
  Rrq := 1
  Rfq := 1
  g1r1 := 1
  g1f1 := 1
  g1r2 := 1
  g1f2 := 1
  g1rq := 1
  g1fq := 1
  g2r := 1
  g2f := 1
  c1r := 1
  c1f := 1
  c2r := 1
  c2f := 1
  smin := 3
  H_NONNEG := by decide
  H_RISE_LE_FALL := by decide
  H_LOOP_POS := by decide

def Sr1 : List Bool := [false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]
theorem Sr1_len : Sr1.length = 40 := rfl
def Sr2 : List Bool := [false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]
theorem Sr2_len : Sr2.length = 40 := rfl
def Sq : List Bool := [true, true, true, true, true, true, true, true, true, true, true, true, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]
theorem Sq_len : Sq.length = 40 := rfl
def SR0 : List Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]
theorem SR0_len : SR0.length = 40 := rfl
def Sg1 : List Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]
theorem Sg1_len : Sg1.length = 40 := rfl
def Sg2 : List Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]
theorem Sg2_len : Sg2.length = 40 := rfl
def SA1 : List Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]
theorem SA1_len : SA1.length = 40 := rfl
def SA2 : List Bool := [false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false, false]
theorem SA2_len : SA2.length = 40 := rfl


def Ws : Sigs where
  r1 := tb Sr1 false true
  r2 := tb Sr2 false true
  q := tb Sq true true
  R0 := tb SR0 false true
  g1 := tb Sg1 false true
  g2 := tb Sg2 false false
  A0 := fun t => tb SR0 false true (t - 3)
  A1 := tb SA1 false true
  A2 := tb SA2 false false

macro "slo_tac" : tactic => `(tactic| (simp only [Ws, Ds]; simp (disch := omega) only [tb_lo] <;> decide))
macro "shi_tac" : tactic => `(tactic| (simp only [Ws, Ds]; simp (disch := omega) only [tb_hi Sq_len,
  tb_hi Sr1_len, tb_hi Sr2_len, tb_hi SR0_len, tb_hi Sg1_len, tb_hi Sg2_len, tb_hi SA1_len,
  tb_hi SA2_len] <;> decide))

theorem Ws_srv : Server Ds.smin Ws.R0 Ws.A0 := by
  have key : ∀ t, (Ws.A0 t ≠ Ws.A0 (t - 1) → Ws.A0 (t - 3) = Ws.A0 (t - 1) ∧
      Ws.A0 (t - 2) = Ws.A0 (t - 1)) := by
    refine all_int 0 50 (fun t h => ?_) (fun t h => ?_) (by decide +kernel)
    · simp only [Ws]; simp (disch := omega) only [tb_lo]; simp
    · simp only [Ws]; simp (disch := omega) only [tb_hi SR0_len]; simp
  intro t h
  refine ⟨t - 3, by simp [Ds], rfl, fun v h1 h2 => ?_⟩
  obtain ⟨k1, k2⟩ := key t h
  have : v = t - 3 ∨ v = t - 2 ∨ v = t - 1 := by omega
  rcases this with rfl | rfl | rfl
  · exact k1
  · exact k2
  · rfl

theorem Ws_H_q : ∀ t, Ws.q t = (FS (Ws.r1 (t - Ds.wr1s - Ds.qr)) (Ws.r2 (t - Ds.wr2s - Ds.qr)) (Ws.q (t - Ds.wfb - Ds.qr)) (Ws.A0 (t - Ds.wa0s - Ds.qr)) || FS (Ws.r1 (t - Ds.wr1s - Ds.qf)) (Ws.r2 (t - Ds.wr2s - Ds.qf)) (Ws.q (t - Ds.wfb - Ds.qf)) (Ws.A0 (t - Ds.wa0s - Ds.qf))) := by
  refine all_int 0 50 (fun t h => ?_) (fun t h => ?_) ?_
  · slo_tac
  · shi_tac
  · decide +kernel

theorem Ws_H_R0 : ∀ t, Ws.R0 t = (FR (Ws.r1 (t - Ds.wr1s - Ds.Rr1)) (Ws.r2 (t - Ds.wr2s - Ds.Rr2)) (Ws.q (t - Ds.wfb - Ds.Rrq)) || FR (Ws.r1 (t - Ds.wr1s - Ds.Rf1)) (Ws.r2 (t - Ds.wr2s - Ds.Rf2)) (Ws.q (t - Ds.wfb - Ds.Rfq))) := by
  refine all_int 0 50 (fun t h => ?_) (fun t h => ?_) ?_
  · slo_tac
  · shi_tac
  · decide +kernel

theorem Ws_H_g1 : ∀ t, Ws.g1 t = (FG1 (Ws.r1 (t - Ds.wr1g - Ds.g1r1)) (Ws.r2 (t - Ds.wr2g - Ds.g1r2)) (Ws.q (t - Ds.wq - Ds.g1rq)) || FG1 (Ws.r1 (t - Ds.wr1g - Ds.g1f1)) (Ws.r2 (t - Ds.wr2g - Ds.g1f2)) (Ws.q (t - Ds.wq - Ds.g1fq))) := by
  refine all_int 0 50 (fun t h => ?_) (fun t h => ?_) ?_
  · slo_tac
  · shi_tac
  · decide +kernel

theorem Ws_H_g2 : ∀ t, Ws.g2 t = (FG2 (Ws.r1 (t - Ds.wr1g - Ds.g2r)) (Ws.r2 (t - Ds.wr2g - Ds.g2r)) (Ws.q (t - Ds.wq - Ds.g2r)) || FG2 (Ws.r1 (t - Ds.wr1g - Ds.g2f)) (Ws.r2 (t - Ds.wr2g - Ds.g2f)) (Ws.q (t - Ds.wq - Ds.g2f))) := by
  refine all_int 0 50 (fun t h => ?_) (fun t h => ?_) ?_
  · slo_tac
  · shi_tac
  · decide +kernel

theorem Ws_H_A1 : ∀ t, Ws.A1 t = (CE (Ws.g1 (t - Ds.wg1 - Ds.c1r)) (Ws.A0 (t - Ds.wa01 - Ds.c1r)) (Ws.A1 (t - Ds.wfa1 - Ds.c1r)) || CE (Ws.g1 (t - Ds.wg1 - Ds.c1f)) (Ws.A0 (t - Ds.wa01 - Ds.c1f)) (Ws.A1 (t - Ds.wfa1 - Ds.c1f))) := by
  refine all_int 0 50 (fun t h => ?_) (fun t h => ?_) ?_
  · slo_tac
  · shi_tac
  · decide +kernel

theorem Ws_H_A2 : ∀ t, Ws.A2 t = (CE (Ws.g2 (t - Ds.wg2 - Ds.c2r)) (Ws.A0 (t - Ds.wa02 - Ds.c2r)) (Ws.A2 (t - Ds.wfa2 - Ds.c2r)) || CE (Ws.g2 (t - Ds.wg2 - Ds.c2f)) (Ws.A0 (t - Ds.wa02 - Ds.c2f)) (Ws.A2 (t - Ds.wfa2 - Ds.c2f))) := by
  refine all_int 0 50 (fun t h => ?_) (fun t h => ?_) ?_
  · slo_tac
  · shi_tac
  · decide +kernel

theorem Ws_run : Run Ds Ws :=
  ⟨Ws_H_q, Ws_H_R0, Ws_H_g1, Ws_H_g2, Ws_H_A1, Ws_H_A2, Ws_srv⟩

theorem Ds_MB : MB Ds 3 := by
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Ds]

theorem Ws_WX : WX Ds 3 Ws 0 0 10 17 12 100 where
  ord := by decide
  r1 := range_chk _ _ (by decide +kernel)
  r2 := range_chk _ _ (by decide +kernel)
  A0 := range_chk _ _ (by decide +kernel)
  anc := Or.inr ⟨rfl, fun t h => by simp only [Ws]; rw [tb_lo h]⟩
  R0a := range_chk _ _ (by decide +kernel)
  q0 := range_chk _ _ (by decide +kernel)
  g10 := range_chk _ _ (by decide +kernel)
  g20 := range_chk _ _ (by decide +kernel)
  A10 := range_chk _ _ (by decide +kernel)
  A20 := range_chk _ _ (by decide +kernel)

/-- **Without H_SEP, B's model admits a run violating C's fields.** A from-reset run of the
held arbiter's gates (every delay nonzero, a real server) meets every hypothesis of the
idle-race window `WX` except H_SEP, which it misses by exactly 1 ps on the loop clause (the
side conditions of `cex_SEP` hold), and C's H_ARB2 and H_ARB1 both fail (`CArb` fails at
ticks 15 and 14). -/
theorem sep_cex_run : ∃ (D : Dl) (s : Sigs) (M : Int),
    Run D s ∧ MB D M ∧ WX D M s 0 0 10 17 12 100 ∧ ¬ HSep D 12 10 ∧
    12 + D.wr1s + 1 = QX D 10 + D.wfb ∧ 10 + D.wr2s ≤ 12 + D.wr1s ∧
    (∀ t, t < 0 → s.r1 t = false ∧ s.r2 t = false ∧ s.g1 t = false ∧ s.g2 t = false ∧
      s.A0 t = false ∧ s.q t = true) ∧
    s.q 13 = false ∧ s.g2 15 = true ∧ s.g2 16 = false ∧ s.r2 15 = true ∧
    s.g1 14 = true ∧ s.g1 15 = false ∧ s.r1 14 = true ∧ ¬ CArb s 15 ∧ ¬ CArb s 14 := by
  refine ⟨Ds, Ws, 3, Ws_run, Ds_MB, Ws_WX, ?_, by decide, by decide, ?_, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · rintro (h | h)
    · exact absurd h (by decide)
    · exact absurd h.q (by unfold QX; decide)
  · intro t h; simp only [Ws]; simp (disch := omega) only [tb_lo]; simp
  · intro h; have := (h.2 (by decide)).1; exact absurd this (by decide)
  · intro h; have := (h.1 (by decide)).1; exact absurd this (by decide)

end Formal.Cells.ArbAMergeRun
