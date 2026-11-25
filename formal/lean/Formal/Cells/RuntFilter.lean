import Formal.Cells.RuntForbid

/-!
# Formal.Cells.RuntFilter — a filtering form of H_RUNT(w) (a proposal for shard A's SpecRunt)

Shard B, 2026-11-07. Companion of `RuntForbid` (which shows that SpecRunt's read-time form of H_RUNT(w) forbids,
rather than filters, a sub-`w` pulse that is longer than a LUT pin's delay window).

## Problem, plainly
State "a LUT input pulse narrower than `w` ps does not propagate to its output" so that it removes pulses from what
the LUT sees and never removes a behaviour. Here a LUT pin reads `filt w s`, the input `s` with every maximal
constant run shorter than `w` (that ends) replaced by the filtered value just before it (so a whole train of
narrow pulses disappears), instead of `s` itself. The read map and its delay window are the frozen ones.

## Proved (standard axioms)
* `filt_zero`: with `w = 0` the filter is the identity, so `GateOKFilt 0 = GateOK` (`gateOKFilt_zero`).
* `filt_long`: on a run of length ≥ `w`, or one that never ends, `filt w s = s`.
* `toy_filtered`: in the toy of `RuntForbid` (XOR reconvergence hazard of 15 ps, read through a 5 ps LUT pin), the
  clean input step that `RuntForbid.toy_no_clean_step` forbids under SpecRunt's H_RUNT(20) is a behaviour under the
  filtered H_RUNT(20), and in it the reader `y` stays low for ever: the pulse is filtered, the step is allowed.
  `toy_frozen_glitch`: under the frozen H_PRIM every behaviour with that step has the 15 ps pulse on `y` as well.

## Not shown / caveats
* The filter is not causal (whether a run is short is known only at its end). It is a statement about which
  traces the pin "sees", which is what the owner's wording asks for, not a circuit model of the filter.
* With the filter, `NetCorrectSeq → NetCorrectSeqRunt w` is no longer a restriction of behaviours (a filtered read
  sees different values), so the owner's "w = 0 is the pessimistic bound" would need its own argument.
* Not applied to THE statement; `SpecRunt.lean` is shard A's.
-/

namespace Formal.Cells.RuntFilter

open Formal.Target
open Formal.Cells.RuntForbid

/-- Start of the maximal constant run of `s` containing `t`. -/
def rs (s : Sig) : Nat → Nat
  | 0 => 0
  | t + 1 => if s t = s (t + 1) then rs s t else t + 1

theorem rs_le (s : Sig) : ∀ t, rs s t ≤ t
  | 0 => le_rfl
  | t + 1 => by
    simp only [rs]; split
    · exact Nat.le_succ_of_le (rs_le s t)
    · exact le_rfl

/-- `t`'s run is short: `s` changes after `t` but before `w` ps after the run's start. -/
def Short (w : Nat) (s : Sig) (t : Nat) : Prop := ∃ u, u < rs s t + w ∧ t < u ∧ s u ≠ s t

instance (w : Nat) (s : Sig) (t : Nat) : Decidable (Short w s t) := by
  unfold Short; exact inferInstance

/-- **The filter.** On a short run, the value just before the run (filtered); `s 0` if the run starts at 0. -/
def filt (w : Nat) (s : Sig) (t : Nat) : Bool :=
  if Short w s t then (if h : rs s t = 0 then s 0 else filt w s (rs s t - 1)) else s t
termination_by t
decreasing_by have := rs_le s t; omega

theorem filt_zero (s : Sig) : filt 0 s = s := by
  funext t
  rw [filt]
  have : ¬ Short 0 s t := by
    rintro ⟨u, h1, h2, -⟩; have := rs_le s t; omega
  simp [this]

theorem filt_long {w : Nat} {s : Sig} {t : Nat} (h : ¬ Short w s t) : filt w s t = s t := by
  rw [filt]; simp [h]

/-- H_PRIM with the filtered H_RUNT(w): a gate of class `L` evaluates its INIT on the FILTERED values of its
inputs at the (frozen) read times; other gates as `GateOK`. -/
def GateOKFiltOn (L : Gate → Bool) (w : Nat) (p : DelayPar) (c : ℚ) (g : Gate) (x : Beh) : Prop :=
  ∃ f : Nat → Nat → Nat,
    (∀ i, i < g.k → Monotone (f i)) ∧
    ∀ t, g.start p ≤ t →
      (∀ i, i < g.k → f i t ≤ t ∧ Adm p c (g.arcs.getD i default) (t - f i t)) ∧
      x g.out t = g.init.testBit (addr g.k fun i =>
        if L g then filt w (x (g.ins.getD i 0)) (f i t) else x (g.ins.getD i 0) (f i t))

theorem gateOKFilt_zero {L : Gate → Bool} {p : DelayPar} {c : ℚ} {g : Gate} {x : Beh} :
    GateOKFiltOn L 0 p c g x ↔ GateOK p c g x := by
  simp only [GateOKFiltOn, GateOK, filt_zero, ite_self]

def BehavesFilt (w : Nat) (p : DelayPar) (N : Net) (x : Beh) : Prop :=
  ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ g ∈ N.gates, GateOKFiltOn lutGate w p c g x

/-! ## The toy, filtered -/

/-- The clean step at `u` with the XOR's 15 ps pulse on `z`, and `y` low for ever (the pulse filtered). -/
def stepF (u : Nat) : Beh := fun n t =>
  if n = 0 then decide (u ≤ t) else if n = 1 then decide (u + 10 ≤ t) else if n = 2 then decide (u + 25 ≤ t)
  else if n = 3 then decide (u + 10 ≤ t ∧ t < u + 25) else false

/-- Characterisation of `rs`: if `a ≤ t` starts a run (`a = 0` or a change at `a`) and `s` is constant on `[a, t]`,
then `rs s t = a`. -/
theorem rs_eq (s : Sig) (a : Nat) (ha : a = 0 ∨ s (a - 1) ≠ s a) :
    ∀ t, a ≤ t → (∀ v, a ≤ v → v ≤ t → s v = s a) → rs s t = a := by
  intro t
  induction t with
  | zero => intro h _; simp [rs]; omega
  | succ t ih =>
    intro hat hc
    by_cases hat' : a = t + 1
    · subst hat'
      rcases ha with h | h
      · omega
      · simp only [rs, Nat.add_sub_cancel] at h ⊢; simp [h]
    · have e1 := hc t (by omega) (by omega)
      have e2 := hc (t + 1) (by omega) le_rfl
      simp only [rs]
      rw [if_pos (by rw [e1, e2])]
      exact ih (by omega) fun v h1 h2 => hc v h1 (by omega)

theorem iff_of_omega {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) : decide P = decide Q :=
  decide_eq_decide.mpr h

/-- A step at `k ≥ w`, `k > 0`, is never filtered (both of its runs are long or unending). -/
theorem step_filt (k : Nat) {w : Nat} (hk : w ≤ k) (hk0 : 0 < k) :
    filt w (fun t => decide (k ≤ t)) = fun t => decide (k ≤ t) := by
  funext t
  apply filt_long
  rintro ⟨v, hv1, hv2, hv3⟩
  by_cases h : t < k
  · rw [rs_eq _ 0 (Or.inl rfl) t (Nat.zero_le _) fun v _ h2 => iff_of_omega (by omega)] at hv1
    exact hv3 (iff_of_omega (by omega))
  · exact hv3 (iff_of_omega (by omega))

theorem zv (u t : Nat) : stepF u 3 t = decide (u + 10 ≤ t ∧ t < u + 25) := rfl

/-- The filtered `z` is low everywhere. -/
theorem filt_z (u : Nat) (hu : 30 ≤ u) (t : Nat) : filt 20 (stepF u 3) t = false := by
  have low : ∀ t, t < u + 10 → filt 20 (stepF u 3) t = false := by
    intro t h1
    rw [filt_long]
    · rw [zv]; simp; omega
    · rintro ⟨v, hv1, hv2, hv3⟩
      rw [rs_eq _ 0 (Or.inl rfl) t (Nat.zero_le _) fun v _ h2 => by rw [zv, zv]; exact iff_of_omega (by omega)]
        at hv1
      exact hv3 (by rw [zv, zv]; exact iff_of_omega (by omega))
  by_cases h1 : t < u + 10
  · exact low t h1
  · by_cases h2 : t < u + 25
    · have hr : rs (stepF u 3) t = u + 10 :=
        rs_eq _ _ (Or.inr (by rw [zv, zv]; simp)) t (by omega)
          fun v h3 h4 => by rw [zv, zv]; exact iff_of_omega (by omega)
      have hs : Short 20 (stepF u 3) t :=
        ⟨u + 25, by omega, by omega, by rw [zv, zv]; simp; omega⟩
      rw [filt, if_pos hs, dif_neg (by omega), hr]
      exact low _ (by omega)
    · rw [filt_long]
      · rw [zv]; simp; omega
      · rintro ⟨v, -, hv2, hv3⟩
        exact hv3 (by rw [zv, zv]; exact iff_of_omega (by omega))

/-- **The filtered H_RUNT(20) allows the step and filters the hazard:** `stepF u` is a `BehavesFilt 20` behaviour
of the toy (g = 1, κ = 0), the input steps cleanly at `u`, and `y` is low at every time. -/
theorem toy_filtered (u : Nat) (hu : 30 ≤ u) :
    BehavesFilt 20 p0 toy (stepF u) ∧ stepF u 0 (u - 1) ≠ stepF u 0 u ∧ ∀ t, stepF u 4 t = false := by
  refine ⟨⟨0, le_rfl, by norm_num, fun g hg => ?_⟩, ?_, fun t => rfl⟩
  · simp only [toy, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · -- gA: not a LUT
      have := copy_ok (c := 0) (x := stepF u) (s := "hop a") (i := 0) (o := 1) (n := 10)
        fun t ht => by show decide (u + 10 ≤ t) = decide (u ≤ t - 10); exact decide_eq_decide.mpr (by omega)
      obtain ⟨f, hm, ht⟩ := this
      have hL : lutGate gA = false := by decide
      refine ⟨f, hm, fun t h => ⟨(ht t h).1, ?_⟩⟩
      rw [hL]; simp only [Bool.false_eq_true, if_false]; exact (ht t h).2
    · have := copy_ok (c := 0) (x := stepF u) (s := "hop b") (i := 0) (o := 2) (n := 25)
        fun t ht => by show decide (u + 25 ≤ t) = decide (u ≤ t - 25); exact decide_eq_decide.mpr (by omega)
      obtain ⟨f, hm, ht⟩ := this
      have hL : lutGate gB = false := by decide
      refine ⟨f, hm, fun t h => ⟨(ht t h).1, ?_⟩⟩
      rw [hL]; simp only [Bool.false_eq_true, if_false]; exact (ht t h).2
    · -- gZ: a LUT; its inputs (steps at u + 10 and u + 25) are never filtered
      have hL : lutGate gZ = true := by decide
      have e1 : stepF u 1 = fun t => decide (u + 10 ≤ t) := rfl
      have e2 : stepF u 2 = fun t => decide (u + 25 ≤ t) := rfl
      refine ⟨fun _ t => t, fun _ _ a b hab => hab, fun t _ => ⟨fun j hj => ?_, ?_⟩⟩
      · refine ⟨le_rfl, ?_⟩
        have : j = 0 ∨ j = 1 := by simp [gZ] at hj; omega
        rcases this with rfl | rfl <;> simpa [gZ] using (fixed_adm 0 0 0).2 rfl
      · simp only [hL, if_true]
        simp only [gZ]
        rw [xor_bit]
        show stepF u 3 t = (filt 20 (stepF u 1) t != filt 20 (stepF u 2) t)
        rw [e1, e2, step_filt (u + 10) (w := 20) (by omega) (by omega), step_filt (u + 25) (w := 20) (by omega) (by omega)]
        show decide (u + 10 ≤ t ∧ t < u + 25) = (decide (u + 10 ≤ t) != decide (u + 25 ≤ t))
        by_cases h1 : u + 10 ≤ t <;> by_cases h2 : u + 25 ≤ t <;> simp [h1, h2] <;> omega
    · -- gY: a LUT reading z through 5 ps; the filtered z is low, so y is low
      have hL : lutGate gY = true := by decide
      refine ⟨fun _ t => t - 5, fun _ _ a b hab => Nat.sub_le_sub_right hab 5, fun t ht => ⟨fun j hj => ?_, ?_⟩⟩
      · have hs : 5 ≤ t := by simpa [Gate.start, gY, p0, fx, Rat.ceil] using ht
        have hj0 : j = 0 := by simpa [gY] using hj
        subst hj0
        exact ⟨Nat.sub_le t 5, (fixed_adm 5 0 _).2 (by simp only []; omega)⟩
      · simp only [hL, if_true]
        simp only [gY]
        rw [copy_bit]
        show false = filt 20 (stepF u 3) (t - 5)
        rw [filt_z u hu]
  · show decide (u ≤ u - 1) ≠ decide (u ≤ u); simp; omega

/-- **Contrast: the frozen H_PRIM passes the hazard.** In every `Behaves` (w = 0) behaviour of the toy with a
clean input step at `u ≥ 30`, the reader `y` is high at `u + 15` and low at `u + 30`: the XOR's 15 ps hazard
reaches `y`. -/
theorem toy_frozen_glitch (x : Beh) (hb : Behaves p0 toy x) (u : Nat) (hu : 30 ≤ u)
    (hpre : ∀ t, u - 30 ≤ t → t < u → x 0 t = x 0 (u - 1))
    (hpost : ∀ t, u ≤ t → t ≤ u + 30 → x 0 t = x 0 u) (hne : x 0 (u - 1) ≠ x 0 u) :
    x 4 (u + 15) = true ∧ x 4 (u + 30) = false := by
  obtain ⟨c, -, -, hg⟩ := hb
  have hA := copy_fixed (hg gA (by simp [toy]))
  have hB := copy_fixed (hg gB (by simp [toy]))
  have hZ := xor_now (hg gZ (by simp [toy]))
  have hY := copy_fixed (hg gY (by simp [toy]))
  constructor
  · rw [hY _ (by omega), hZ, hA _ (by omega), hB _ (by omega), hpost (u + 15 - 5 - 10) (by omega) (by omega),
      hpre (u + 15 - 5 - 25) (by omega) (by omega)]
    cases h : x 0 u <;> cases h' : x 0 (u - 1) <;> simp_all
  · rw [hY _ (by omega), hZ, hA _ (by omega), hB _ (by omega), hpost (u + 30 - 5 - 10) (by omega) (by omega),
      hpost (u + 30 - 5 - 25) (by omega) (by omega)]
    simp

end Formal.Cells.RuntFilter
