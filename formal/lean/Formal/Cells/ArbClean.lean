import Formal.Cells.SpecFb
import Formal.Cells.ArbT

/-!
# Formal.Cells.ArbClean — a separated arbitration needs no H_ARB (frozen Spec semantics)

Shard B, THE goal. On the decoded target, simulated arbitrations are lopsided by tens of ns
(JOURNAL-B 08:43: the second request arrives 60-95 ns after the first, far beyond any band
slack). This file gives the Lean side of that route: when the set condition of the held
arbiter's state LUT is visible for at least its feedback arc, q goes to 1 cleanly and stays 1
while r1 stays high, whatever r2 and A0 do afterwards. No resolution hypothesis is used: an
arbitration that is separated in time is decided by the gate relation alone (`SpecFb`).

## Problem, plainly
Can the proof of THE theorem avoid H_ARB(T) at an arbiter whose requests are separated?

## Results (state LUT in logical pin order r1, r2, q, rst, A0, table `qInit`)
* `q_clean_set`: GateOK; Nat bounds on the arcs; the feedback arc's lower bound ≥ 1; over
  the read windows of `[s, e]`, r1 = 1, r2 = 0, rst = 0, A0 = 0 (set), with `e + 1 ≥ s + hi_q`;
  over the read windows of `[e + 1, e']`, r1 = 1 and rst = 0 (r2 and A0 free). Then q = 1 on
  `[s, e']`.
* `q_clean_reset`: the mirror (r1 = 0, r2 = 1 forces 0; afterwards r2 = 1, rst = 0 keeps it).
Both are `SpecFb.fb_switch` with the table facts checked by `decide`.

## What it means
For each arbitration of the target the proof can choose: either show the two requests are
separated by at least the state gate's feedback arc at its pins (then this file, plus
`ArbT.one_ack`, decides it without H_ARB), or rely on H_ARB(T) and then show q settles before A0
rises (`ArbT.one_ack`), which bounds T. The simulated target runs are all of the first kind.

## Not covered
The physical pin order of each decoded ustate (nextpnr permutes LUT pins; the table is then a
permutation of `qInit`, a mechanical restatement); proving the separation from the bands for
every behaviour (a checker obligation).
-/

namespace Formal.Cells.ArbClean

open Formal.Target Formal.Cells.SpecFb
open Formal.Cells.ArbT (qInit)

/-- The table facts (logical pin order r1, r2, q, rst, A0). -/
theorem set_forces (v : Nat → Bool) (h0 : v 0 = true) (h1 : v 1 = false) (h3 : v 3 = false)
    (h4 : v 4 = false) : qInit.testBit (addr 5 v) = true := by
  simp only [addr, h0, h1, h3, h4]
  cases v 2 <;> decide

theorem one_confirms (v : Nat → Bool) (h0 : v 0 = true) (h2 : v 2 = true) (h3 : v 3 = false) :
    qInit.testBit (addr 5 v) = true := by
  simp only [addr, h0, h2, h3]
  cases v 1 <;> cases v 4 <;> decide

theorem reset_forces (v : Nat → Bool) (h0 : v 0 = false) (h1 : v 1 = true) (h3 : v 3 = false)
    (h4 : v 4 = false) : qInit.testBit (addr 5 v) = false := by
  simp only [addr, h0, h1, h3, h4]
  cases v 2 <;> decide

theorem zero_confirms (v : Nat → Bool) (h1 : v 1 = true) (h2 : v 2 = false) (h3 : v 3 = false) :
    qInit.testBit (addr 5 v) = false := by
  simp only [addr, h1, h2, h3]
  cases v 0 <;> cases v 4 <;> decide

/-- Node `n` has value `b` over pin `i`'s read windows of every `t ∈ [s, e]`. -/
def OnReads (x : Beh) (lo hi : Nat → Nat) (i n : Nat) (b : Bool) (s e : Nat) : Prop :=
  ∀ t u, s ≤ t → t ≤ e → u + lo i ≤ t → t ≤ u + hi i → x n u = b

theorem visible_val {x : Beh} {g : Gate} {lo hi : Nat → Nat} {j t : Nat} {v : Nat → Bool}
    (hv : Visible x g lo hi j t v) {i : Nat} (hi' : i < g.k) (hij : i ≠ j) {b : Bool} {s e : Nat}
    (hst : s ≤ t) (hte : t ≤ e) (h : OnReads x lo hi i (g.ins.getD i 0) b s e) : v i = b := by
  obtain ⟨u, h1, h2, h3⟩ := hv i hi' hij
  rw [h3]; exact h t u hst hte h1 h2

/-- **Clean set.** -/
theorem q_clean_set {p : DelayPar} {c : ℚ} {g : Gate} {x : Beh} (hg : GateOK p c g x)
    (hk : g.k = 5) (hinit : g.init = qInit) (hfb : g.ins.getD 2 0 = g.out)
    {lo hi : Nat → Nat} (hb : Bands p c g lo hi) (hlo : 1 ≤ lo 2) {s e e' : Nat}
    (hs : g.start p ≤ s) (hlong : s + hi 2 ≤ e + 1) (hee : e ≤ e')
    (hr1 : OnReads x lo hi 0 (g.ins.getD 0 0) true s e')
    (hr2 : OnReads x lo hi 1 (g.ins.getD 1 0) false s e)
    (hrs : OnReads x lo hi 3 (g.ins.getD 3 0) false s e')
    (ha0 : OnReads x lo hi 4 (g.ins.getD 4 0) false s e) :
    ∀ t, s ≤ t → t ≤ e' → x g.out t = true := by
  apply fb_switch hg hb (j := 2) (by omega) hfb hlo hs hlong
  · intro t h1 h2 v hv
    rw [hinit, hk]
    exact set_forces v (visible_val hv (by omega) (by omega) h1 (by omega) hr1)
      (visible_val hv (by omega) (by omega) h1 h2 hr2)
      (visible_val hv (by omega) (by omega) h1 (by omega) hrs)
      (visible_val hv (by omega) (by omega) h1 h2 ha0)
  · intro t h1 h2 v hv2 hv
    rw [hinit, hk]
    exact one_confirms v (visible_val hv (by omega) (by omega) (by omega) h2 hr1) hv2
      (visible_val hv (by omega) (by omega) (by omega) h2 hrs)

/-- **Clean reset** (the mirror). -/
theorem q_clean_reset {p : DelayPar} {c : ℚ} {g : Gate} {x : Beh} (hg : GateOK p c g x)
    (hk : g.k = 5) (hinit : g.init = qInit) (hfb : g.ins.getD 2 0 = g.out)
    {lo hi : Nat → Nat} (hb : Bands p c g lo hi) (hlo : 1 ≤ lo 2) {s e e' : Nat}
    (hs : g.start p ≤ s) (hlong : s + hi 2 ≤ e + 1) (hee : e ≤ e')
    (hr1 : OnReads x lo hi 0 (g.ins.getD 0 0) false s e)
    (hr2 : OnReads x lo hi 1 (g.ins.getD 1 0) true s e')
    (hrs : OnReads x lo hi 3 (g.ins.getD 3 0) false s e')
    (ha0 : OnReads x lo hi 4 (g.ins.getD 4 0) false s e) :
    ∀ t, s ≤ t → t ≤ e' → x g.out t = false := by
  apply fb_switch hg hb (j := 2) (by omega) hfb hlo hs hlong
  · intro t h1 h2 v hv
    rw [hinit, hk]
    exact reset_forces v (visible_val hv (by omega) (by omega) h1 h2 hr1)
      (visible_val hv (by omega) (by omega) h1 (by omega) hr2)
      (visible_val hv (by omega) (by omega) h1 (by omega) hrs)
      (visible_val hv (by omega) (by omega) h1 h2 ha0)
  · intro t h1 h2 v hv2 hv
    rw [hinit, hk]
    exact zero_confirms v (visible_val hv (by omega) (by omega) (by omega) h2 hr2) hv2
      (visible_val hv (by omega) (by omega) (by omega) h2 hrs)

end Formal.Cells.ArbClean
