import Formal.Cells.SpecFb
import Formal.Cells.ArbT
import Formal.Cells.PrimTables

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

/-! ## Any pin order (the decoded ustates are pin-permuted and have tied pins)

`Roles`: the indices of r1, r2, the feedback, rst and A0 among the gate's pins, plus the set
of tied pins with their constant values. The two table facts are hypotheses, decidable per
gate (64 addresses for a LUT6), so each decoded target ustate discharges them by `decide`. -/

structure Roles where
  r1 : Nat
  r2 : Nat
  fb : Nat
  rst : Nat
  a0 : Nat
  tied : List (Nat × Bool)

/-- **Clean set, any pin order.** -/
theorem q_clean_set_gen {p : DelayPar} {c : ℚ} {g : Gate} {x : Beh} (hg : GateOK p c g x) (R : Roles)
    (hk : R.r1 < g.k ∧ R.r2 < g.k ∧ R.fb < g.k ∧ R.rst < g.k ∧ R.a0 < g.k)
    (hne : R.r1 ≠ R.fb ∧ R.r2 ≠ R.fb ∧ R.rst ≠ R.fb ∧ R.a0 ≠ R.fb)
    (htk : ∀ jb ∈ R.tied, jb.1 < g.k ∧ jb.1 ≠ R.fb)
    (hset : ∀ v : Nat → Bool, v R.r1 = true → v R.r2 = false → v R.rst = false → v R.a0 = false →
      (∀ jb ∈ R.tied, v jb.1 = jb.2) → g.init.testBit (addr g.k v) = true)
    (hconf : ∀ v : Nat → Bool, v R.r1 = true → v R.fb = true → v R.rst = false →
      (∀ jb ∈ R.tied, v jb.1 = jb.2) → g.init.testBit (addr g.k v) = true)
    (hfb : g.ins.getD R.fb 0 = g.out)
    {lo hi : Nat → Nat} (hb : Bands p c g lo hi) (hlo : 1 ≤ lo R.fb) {s e e' : Nat}
    (hs : g.start p ≤ s) (hlong : s + hi R.fb ≤ e + 1) (hee : e ≤ e')
    (htied : ∀ jb ∈ R.tied, OnReads x lo hi jb.1 (g.ins.getD jb.1 0) jb.2 s e')
    (hr1 : OnReads x lo hi R.r1 (g.ins.getD R.r1 0) true s e')
    (hr2 : OnReads x lo hi R.r2 (g.ins.getD R.r2 0) false s e)
    (hrs : OnReads x lo hi R.rst (g.ins.getD R.rst 0) false s e')
    (ha0 : OnReads x lo hi R.a0 (g.ins.getD R.a0 0) false s e) :
    ∀ t, s ≤ t → t ≤ e' → x g.out t = true := by
  apply fb_switch hg hb (j := R.fb) hk.2.2.1 hfb hlo hs hlong
  · intro t h1 h2 v hv
    exact hset v (visible_val hv hk.1 hne.1 h1 (by omega) hr1)
      (visible_val hv hk.2.1 hne.2.1 h1 h2 hr2)
      (visible_val hv hk.2.2.2.1 hne.2.2.1 h1 (by omega) hrs)
      (visible_val hv hk.2.2.2.2 hne.2.2.2 h1 h2 ha0)
      (fun jb hj => visible_val hv (htk jb hj).1 (htk jb hj).2 h1 (by omega) (htied jb hj))
  · intro t h1 h2 v hv2 hv
    exact hconf v (visible_val hv hk.1 hne.1 (by omega) h2 hr1) hv2
      (visible_val hv hk.2.2.2.1 hne.2.2.1 (by omega) h2 hrs)
      (fun jb hj => visible_val hv (htk jb hj).1 (htk jb hj).2 (by omega) h2 (htied jb hj))

/-- The logical layout is an instance (sanity check of the general form). -/
example : ∀ v : Nat → Bool, v 0 = true → v 1 = false → v 3 = false → v 4 = false →
    (∀ jb ∈ ([] : List (Nat × Bool)), v jb.1 = jb.2) → qInit.testBit (addr 5 v) = true :=
  fun v h0 h1 h3 h4 _ => set_forces v h0 h1 h3 h4

/-! ### The nine decoded target ustates (GENERATED by the shard-B script in the commit message from
tools-B/target/lean2json.py output of Formal/Target/Net; INIT, k and roles are data of the generated
netlist, the role assignment from tools-B/target/adv.py `roles`; untrusted until linked to
`Formal.Target.Decoded.net` by an equality on these gates). -/

/-- (name, k, INIT, roles) of each target ustate O6 gate; the one tied pin is VCC. -/
def targetQ : List (String × Nat × Nat × Roles) := [
  ("SLICE_X0Y18.DLUT.O6", 6, 0xffefff02aaaaf0f0, ⟨0, 2, 4, 3, 1, [(5, true)]⟩),
  ("SLICE_X4Y97.ALUT.O6", 6, 0xffefff02aaaaf0f0, ⟨0, 2, 4, 3, 1, [(5, true)]⟩),
  ("SLICE_X32Y80.ALUT.O6", 6, 0xfeffccdcf0f0ff00, ⟨2, 3, 4, 1, 0, [(5, true)]⟩),
  ("SLICE_X31Y83.ALUT.O6", 6, 0xfffbf0f2aaaacccc, ⟨0, 1, 4, 2, 3, [(5, true)]⟩),
  ("SLICE_X42Y83.BLUT.O6", 6, 0xfffffb02aaccaacc, ⟨0, 1, 3, 4, 2, [(5, true)]⟩),
  ("SLICE_X42Y42.ALUT.O6", 6, 0xfffdf0f4ccccaaaa, ⟨1, 0, 4, 2, 3, [(5, true)]⟩),
  ("SLICE_X41Y24.CLUT.O6", 6, 0xffcdfdccffaa00aa, ⟨4, 0, 3, 1, 2, [(5, true)]⟩),
  ("SLICE_X9Y95.CLUT.O6", 6, 0xfff0fdf4ccaaccaa, ⟨1, 0, 3, 2, 4, [(5, true)]⟩),
  ("SLICE_X0Y96.ALUT.O6", 6, 0xfcfdfcdcfafa0a0a, ⟨4, 0, 2, 1, 3, [(5, true)]⟩)]

/-- Table facts of one gate, as Booleans over all `2^k` pin vectors (decidable). -/
def setFact (k init : Nat) (R : Roles) : Bool :=
  (List.range (2 ^ k)).all fun a =>
    let v := fun i => a.testBit i
    !(v R.r1 && !v R.r2 && !v R.rst && !v R.a0 && R.tied.all (fun jb => v jb.1 == jb.2)) ||
      init.testBit a

def confFact (k init : Nat) (R : Roles) : Bool :=
  (List.range (2 ^ k)).all fun a =>
    let v := fun i => a.testBit i
    !(v R.r1 && v R.fb && !v R.rst && R.tied.all (fun jb => v jb.1 == jb.2)) || init.testBit a

/-- **All nine target ustates meet both table facts** (kernel `decide`). -/
theorem targetQ_facts : targetQ.all (fun r => setFact r.2.1 r.2.2.1 r.2.2.2 && confFact r.2.1 r.2.2.1 r.2.2.2) = true := by
  decide +kernel

/-- Negative control: with r1 and r2 swapped, the set fact fails for the first gate. -/
theorem targetQ_swap_fails :
    setFact 6 0xffefff02aaaaf0f0 ⟨2, 0, 4, 3, 1, [(5, true)]⟩ = false := by decide +kernel


/-- The Boolean set fact gives `q_clean_set_gen`'s `hset`. -/
theorem hset_of_fact {k init : Nat} {R : Roles} (h : setFact k init R = true)
    (hk : R.r1 < k ∧ R.r2 < k ∧ R.rst < k ∧ R.a0 < k) (htk : ∀ jb ∈ R.tied, jb.1 < k) :
    ∀ v : Nat → Bool, v R.r1 = true → v R.r2 = false → v R.rst = false → v R.a0 = false →
      (∀ jb ∈ R.tied, v jb.1 = jb.2) → init.testBit (addr k v) = true := by
  intro v h1 h2 h3 h4 ht
  have ha := Formal.Cells.PrimTables.addr_lt k v
  have hb := fun i hi => Formal.Cells.PrimTables.addr_testBit k v i hi
  unfold setFact at h
  have := List.all_eq_true.mp h (addr k v) (List.mem_range.mpr ha)
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
  rcases this with hc | hc
  · exfalso
    rw [hb _ hk.1, hb _ hk.2.1, hb _ hk.2.2.1, hb _ hk.2.2.2, h1, h2, h3, h4] at hc
    simp only [Bool.not_false, Bool.and_true, Bool.true_and] at hc
    have : (R.tied.all fun jb => (addr k v).testBit jb.1 == jb.2) = true := by
      rw [List.all_eq_true]; intro jb hj; rw [hb _ (htk jb hj), ht jb hj]; simp
    rw [this] at hc; exact Bool.false_ne_true hc.symm
  · exact hc

/-- The Boolean confirm fact gives `q_clean_set_gen`'s `hconf`. -/
theorem hconf_of_fact {k init : Nat} {R : Roles} (h : confFact k init R = true)
    (hk : R.r1 < k ∧ R.fb < k ∧ R.rst < k) (htk : ∀ jb ∈ R.tied, jb.1 < k) :
    ∀ v : Nat → Bool, v R.r1 = true → v R.fb = true → v R.rst = false →
      (∀ jb ∈ R.tied, v jb.1 = jb.2) → init.testBit (addr k v) = true := by
  intro v h1 h2 h3 ht
  have ha := Formal.Cells.PrimTables.addr_lt k v
  have hb := fun i hi => Formal.Cells.PrimTables.addr_testBit k v i hi
  unfold confFact at h
  have := List.all_eq_true.mp h (addr k v) (List.mem_range.mpr ha)
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
  rcases this with hc | hc
  · exfalso
    rw [hb _ hk.1, hb _ hk.2.1, hb _ hk.2.2, h1, h2, h3] at hc
    simp only [Bool.not_false, Bool.and_true, Bool.true_and] at hc
    have : (R.tied.all fun jb => (addr k v).testBit jb.1 == jb.2) = true := by
      rw [List.all_eq_true]; intro jb hj; rw [hb _ (htk jb hj), ht jb hj]; simp
    rw [this] at hc; exact Bool.false_ne_true hc.symm
  · exact hc

end Formal.Cells.ArbClean
