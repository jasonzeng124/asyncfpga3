import Formal.Target.SpecRunt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Formal.Cells.RuntForbid — H_RUNT(w) on a LUT pin whose delay window is narrower than w forbids pulses

Shard B, 2026-11-07 (H_PRIM). A follow-up to audit row T9 (the zero-delay-pin case, fixed by A on 2026-11-06 by
restricting `NoRuntRead` to LUT pins).

## Problem, plainly
The owner's H_RUNT(w) says: a LUT input pulse narrower than `w` ps does not propagate to the LUT's output.
`SpecRunt.GateOKRuntOn` states it as a restriction on the read map: a LUT pin's read time never lands inside a
pulse narrower than `w`. But a read time must also lie in the pin's delay window `[t - dhi, t - dlo]`. If the
pulse is LONGER than that window (`dhi - dlo < b - a`) and still shorter than `w`, then at `t = a + dhi` every
admissible read time lies inside the pulse: no read map exists, so the behaviour is not a behaviour of the
statement at all. The pulse is not filtered; it is FORBIDDEN, and with it every delay choice (and every
environment move) that would create it.

## Proved (standard axioms)
* `runt_forbids`: the generic fact above, for any gate of the class `L`, any pin, any corner.
* `fixed_*`, `toy_*`: a five-gate toy net at g = 1, κ = 0 (fixed-delay arcs, so every corner is the same): the
  input `in` fans out through a 10 ps and a 25 ps copy into an XOR LUT (`z`, a reconvergent-fanout hazard: a
  15 ps pulse at every clean input step), and `z` is read by a LUT pin with a 5 ps arc (window width 0).
  `toy_no_clean_step`: in EVERY `BehavesRunt 20` behaviour, the environment's input never makes a clean step
  (constant 30 ps before and after) at any time ≥ 30. With w = 0 (the frozen statement) the step is admitted
  (`toy_step_w0`: a behaviour with the step exists).

## What it means for THE statement
`NetCorrectSeqRunt w` quantifies only over `BehavesRunt w` behaviours. Wherever the circuit (by a hazard of its
own LUTs, for any admissible delays) would put a pulse of width in `(dhi - dlo, w)` on the source of a LUT pin,
the statement silently drops that behaviour, or, if the pulse is forced, the environment move that causes it: a
proof of `NetCorrectSeqRunt 20` could then hold for a circuit that fails on the chip, and a refutation cannot use
such behaviours. On THE target (Python, untrusted, `tools-B/ps/lutwin.py`): 3,317 support LUT pins have fewer than
20 admissible integer delays at the fast corner with κ = 0 (window widths 12-19 ps), 2,307 at c = 0.5, none at
c = 1, and none once κ ≥ 0.1 (c = 0) or κ ≥ 0.05 (c = 0.5). So the hole is in the small-κ, fast-corner part of
the headline (w = 20) statement.

## Not shown
That THE target's behaviours actually carry such pulses (a forced one would make the statement vacuous for that
environment; an optional one only removes behaviours). A filtering definition that matches the owner's wording is
proposed in `formal/notes/B-hrunt-forbid.md`; `SpecRunt.lean` is shard A's file.
-/

namespace Formal.Cells.RuntForbid

open Formal.Target

/-- **H_RUNT(w) forbids, not filters, pulses longer than a pin's window.** If gate `g` is in the filtered class,
every admissible delay of its pin `i` at corner `c` lies in `[dlo, dhi]`, and the pin's source holds a pulse on
`[a, b)` with `dhi - dlo < b - a < w`, from the gate's start on, then `g` has no runt-respecting read map. -/
theorem runt_forbids {L : Gate → Bool} {w : Nat} {p : DelayPar} {c : ℚ} {g : Gate} {x : Beh}
    (hL : L g = true) {i : Nat} (hi : i < g.k) {dlo dhi : Nat}
    (hband : ∀ d, Adm p c (g.arcs.getD i default) d → dlo ≤ d ∧ d ≤ dhi)
    {a b : Nat} (hP : Pulse (x (g.ins.getD i 0)) a b) (hw : b - a < w) (hwide : dhi - dlo < b - a)
    (hstart : g.start p ≤ a + dhi) :
    ¬ GateOKRuntOn L w p c g x := by
  rintro ⟨f, -, ht⟩
  obtain ⟨hle, hadm, hnr⟩ := (ht (a + dhi) hstart).1 i hi
  obtain ⟨h1, h2⟩ := hband _ hadm
  exact hnr hL a b hP hw ⟨by omega, by omega⟩

/-! ## The toy net -/

/-- g = 1, κ = 0. -/
def p0 : DelayPar := ⟨1, 0⟩

/-- A fixed-delay arc: `n` ps at every corner. -/
def fx (n : Nat) : Arc := ⟨n, n, n, n⟩

theorem fixed_adm (n : Nat) (c : ℚ) (d : Nat) : Adm p0 c (fx n) d ↔ d = n := by
  simp only [Adm, p0, fx, lerp]
  constructor
  · rintro ⟨h1, h2⟩
    have h1' : (n : ℚ) ≤ d := by linarith
    have h2' : (d : ℚ) ≤ n := by linarith
    have : (d : ℚ) = n := le_antisymm h2' h1'
    exact_mod_cast this
  · rintro rfl
    have e : ((1 : ℚ) - c) * d + c * d = d := by ring
    constructor <;> simp [e]

/-- Nodes: 0 `in` (environment), 1 `a`, 2 `b`, 3 `z`, 4 `y`. -/
def gA : Gate := ⟨"hop a", 1, 2, [0], [fx 10], 1⟩
def gB : Gate := ⟨"hop b", 1, 2, [0], [fx 25], 2⟩
/-- XOR of `a` and `b` (INIT 6), a LUT (name ends in `LUT.O6`), zero-delay pins. -/
def gZ : Gate := ⟨"T.ALUT.O6", 2, 6, [1, 2], [fx 0, fx 0], 3⟩
/-- A buffer LUT reading `z` through a 5 ps arc (window width 0). -/
def gY : Gate := ⟨"T.BLUT.O6", 1, 2, [3], [fx 5], 4⟩

def toy : Net := ⟨5, ["in", "a", "b", "z", "y"], [gA, gB, gZ, gY]⟩

theorem start_copy (s : String) (i o n : Nat) : Gate.start p0 ⟨s, 1, 2, [i], [fx n], o⟩ = n := by
  simp [Gate.start, p0, fx, Rat.ceil]

theorem copy_bit (v : Nat → Bool) : (2 : Nat).testBit (addr 1 v) = v 0 := by
  cases h : v 0 <;> simp [addr, h] <;> decide

theorem xor_bit (v : Nat → Bool) : (6 : Nat).testBit (addr 2 v) = (v 0 != v 1) := by
  cases h0 : v 0 <;> cases h1 : v 1 <;> simp [addr, h0, h1] <;> decide

/-- A fixed-delay copy gate: output = input `n` ps earlier, from time `n` on. -/
theorem copy_fixed {c : ℚ} {x : Beh} {s : String} {i o n : Nat}
    (h : GateOK p0 c ⟨s, 1, 2, [i], [fx n], o⟩ x) : ∀ t, n ≤ t → x o t = x i (t - n) := by
  obtain ⟨f, -, ht⟩ := h
  intro t htn
  obtain ⟨hr, ho⟩ := ht t (by rw [start_copy]; exact htn)
  obtain ⟨hle, hadm⟩ := hr 0 Nat.zero_lt_one
  have hd := (fixed_adm n c _).1 (by simpa using hadm)
  have hf : f 0 t = t - n := by omega
  rw [ho, copy_bit]; simp [hf]

/-- The XOR gate with zero-delay pins: `z t = a t xor b t` from time 0. -/
theorem xor_now {c : ℚ} {x : Beh} (h : GateOK p0 c gZ x) : ∀ t, x 3 t = (x 1 t != x 2 t) := by
  obtain ⟨f, -, ht⟩ := h
  intro t
  have hs : gZ.start p0 ≤ t := by simp [Gate.start, gZ, p0, fx, Rat.ceil]
  obtain ⟨hr, ho⟩ := ht t hs
  have e0 := (fixed_adm 0 c _).1 (by simpa [gZ] using (hr 0 (by decide)).2)
  have e1 := (fixed_adm 0 c _).1 (by simpa [gZ] using (hr 1 (by decide)).2)
  have l0 := (hr 0 (by decide)).1
  have l1 := (hr 1 (by decide)).1
  have f0 : f 0 t = t := by omega
  have f1 : f 1 t = t := by omega
  have := ho
  simp only [gZ] at this
  rw [this, xor_bit]; simp [f0, f1]

/-- **The toy: H_RUNT(20) forbids the environment's clean step.** In every `BehavesRunt 20` behaviour of `toy`
(g = 1, κ = 0), the input never toggles at a time `u ≥ 30` around which it is otherwise constant for 30 ps. -/
theorem toy_no_clean_step (x : Beh) (hb : BehavesRunt 20 p0 toy x) (u : Nat) (hu : 30 ≤ u)
    (hpre : ∀ t, u - 30 ≤ t → t < u → x 0 t = x 0 (u - 1))
    (hpost : ∀ t, u ≤ t → t ≤ u + 30 → x 0 t = x 0 u) :
    x 0 (u - 1) = x 0 u := by
  obtain ⟨c, -, -, hg⟩ := hb
  have hA := copy_fixed (gateOK_of_runt (hg gA (by simp [toy])))
  have hB := copy_fixed (gateOK_of_runt (hg gB (by simp [toy])))
  have hZ := xor_now (gateOK_of_runt (hg gZ (by simp [toy])))
  by_contra hne
  -- z holds a 15 ps pulse on [u + 10, u + 25)
  have zin : ∀ t, u + 10 ≤ t → t < u + 25 → x 3 t = true := by
    intro t h1 h2
    rw [hZ, hA t (by omega), hB t (by omega), hpost (t - 10) (by omega) (by omega),
      hpre (t - 25) (by omega) (by omega)]
    cases h : x 0 u <;> cases h' : x 0 (u - 1) <;> simp_all
  have zbefore : x 3 (u + 10 - 1) = false := by
    rw [hZ, hA _ (by omega), hB _ (by omega), hpre (u + 10 - 1 - 10) (by omega) (by omega),
      hpre (u + 10 - 1 - 25) (by omega) (by omega)]
    simp
  have zafter : x 3 (u + 25) = false := by
    rw [hZ, hA _ (by omega), hB _ (by omega), hpost (u + 25 - 10) (by omega) (by omega),
      hpost (u + 25 - 25) (by omega) (by omega)]
    simp
  have hP : Pulse (x 3) (u + 10) (u + 25) := by
    refine ⟨by omega, fun t h1 h2 => ?_, fun _ => ?_, ?_⟩
    · rw [zin t h1 h2, zin (u + 10) le_rfl (by omega)]
    · rw [zbefore, zin (u + 10) le_rfl (by omega)]; decide
    · rw [zafter, zin (u + 10) le_rfl (by omega)]; decide
  refine runt_forbids (L := lutGate) (g := gY) (i := 0) (dlo := 5) (dhi := 5) (a := u + 10) (b := u + 25)
    (by decide) (by decide) ?_ (by simpa [gY] using hP) (by omega) (by omega) ?_ (hg gY (by simp [toy]))
  · intro d hd
    have := (fixed_adm 5 c d).1 (by simpa [gY] using hd)
    omega
  · simp [Gate.start, gY, p0, fx, Rat.ceil]

/-! ## With w = 0 (the frozen statement) the clean step is a behaviour -/

/-- Converse of `copy_fixed`: a fixed-delay copy relation is a `GateOK` behaviour (read map `t - n`). -/
theorem copy_ok {c : ℚ} {x : Beh} {s : String} {i o n : Nat} (h : ∀ t, n ≤ t → x o t = x i (t - n)) :
    GateOK p0 c ⟨s, 1, 2, [i], [fx n], o⟩ x := by
  refine ⟨fun _ t => t - n, fun _ _ a b hab => Nat.sub_le_sub_right hab n, fun t ht => ⟨fun j hj => ?_, ?_⟩⟩
  · have hs : n ≤ t := by rwa [start_copy] at ht
    have hj0 : j = 0 := by simpa using hj
    subst hj0
    refine ⟨Nat.sub_le t n, ?_⟩
    simp only [List.getD_cons_zero]
    exact (fixed_adm n c _).2 (by omega)
  · have hs : n ≤ t := by rwa [start_copy] at ht
    simp only [copy_bit, List.getD_cons_zero]
    exact h t hs

/-- The clean step of the input at `u`, propagated with the toy's fixed delays (z pulses on `[u+10, u+25)`). -/
def stepBeh (u : Nat) : Beh := fun n t =>
  if n = 0 then decide (u ≤ t) else if n = 1 then decide (u + 10 ≤ t) else if n = 2 then decide (u + 25 ≤ t)
  else if n = 3 then decide (u + 10 ≤ t ∧ t < u + 25) else decide (u + 15 ≤ t ∧ t < u + 30)

/-- **Non-vacuity of the contrast:** for every `u ≥ 30`, `stepBeh u` is a behaviour of `toy` under the frozen
H_PRIM (`Behaves`, i.e. w = 0), and in it the input makes exactly the clean step that `toy_no_clean_step`
forbids under H_RUNT(20). -/
theorem toy_step_w0 (u : Nat) (hu : 30 ≤ u) :
    Behaves p0 toy (stepBeh u) ∧ stepBeh u 0 (u - 1) ≠ stepBeh u 0 u ∧
    (∀ t, u - 30 ≤ t → t < u → stepBeh u 0 t = stepBeh u 0 (u - 1)) ∧
    (∀ t, u ≤ t → t ≤ u + 30 → stepBeh u 0 t = stepBeh u 0 u) := by
  refine ⟨⟨0, le_rfl, by norm_num, fun g hg => ?_⟩, ?_, ?_, ?_⟩
  · simp only [toy, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact copy_ok fun t ht => by
        show decide (u + 10 ≤ t) = decide (u ≤ t - 10); exact decide_eq_decide.mpr (by omega)
    · exact copy_ok fun t ht => by
        show decide (u + 25 ≤ t) = decide (u ≤ t - 25); exact decide_eq_decide.mpr (by omega)
    · refine ⟨fun _ t => t, fun _ _ a b hab => hab, fun t _ => ⟨fun j hj => ?_, ?_⟩⟩
      · refine ⟨le_rfl, ?_⟩
        have : j = 0 ∨ j = 1 := by simp [gZ] at hj; omega
        rcases this with rfl | rfl <;> simpa [gZ] using (fixed_adm 0 0 0).2 rfl
      · simp only [gZ]
        rw [xor_bit]
        show decide (u + 10 ≤ t ∧ t < u + 25) = (decide (u + 10 ≤ t) != decide (u + 25 ≤ t))
        by_cases h1 : u + 10 ≤ t <;> by_cases h2 : u + 25 ≤ t <;> simp [h1, h2] <;> omega
    · exact copy_ok (s := "T.BLUT.O6") (i := 3) (o := 4) (n := 5) fun t ht => by
        show decide (u + 15 ≤ t ∧ t < u + 30) = decide (u + 10 ≤ t - 5 ∧ t - 5 < u + 25)
        exact decide_eq_decide.mpr (by omega)
  · show decide (u ≤ u - 1) ≠ decide (u ≤ u); simp; omega
  · intro t h1 h2; show decide (u ≤ t) = decide (u ≤ u - 1); exact decide_eq_decide.mpr (by omega)
  · intro t h1 h2; show decide (u ≤ t) = decide (u ≤ u); exact decide_eq_decide.mpr (by omega)

end Formal.Cells.RuntForbid
