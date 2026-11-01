import Formal.Cells.SpecArbVacuous

/-!
# Formal.Cells.ArbOKRepair — the repaired H_ARB(T) of the Spec, checked on the handover

Shard B, THE goal. Shard A repaired `Formal.Target.Spec.ArbOK` at 08:11 (commit 3d3ebb61) after
B's finding (`SpecArbVacuous`): `ArbNodes` now lists q and EVERY non-feedback input of the
state LUT, and H_ARB(T) asks q to be constant `T` after all of them are.

## Problem, plainly
Does the repaired statement still exclude ordinary arbitrations, and for which `T` is it
non-vacuous?

## Results (against the Spec as it now is)
* `arbOK_admits_handover`: the behaviour that v1 excluded (the q gate's handover, A0 falling
  at `ta`, q flipping at `ta + 10`) satisfies the repaired `ArbOK T` for every `T ≥ 10`
  (10 = the state gate's arc in that example).
* `arbOK_needs_T_ge_arc`: for `T < 10` it does not: an ordinary, race-free q transition
  takes the gate's arc to appear, and `ArbOK T` with `T` below that arc forbids it. So THE
  theorem must take `T` at least the state gate's slowest admissible arc, or it is vacuous
  on every arbitration. (Recorded for shard A: STATUS/Spec should say so.)
* `arbOK_mono`: larger `T` is weaker, as THE goal reads it.

## Not covered
That the repaired H_ARB(T) makes THE theorem true: it does not by itself
(`ArbTSpec.spec_double_ack`); the proof needs the server-path obligation of `ArbT.one_ack`.
-/

namespace Formal.Cells.ArbOKRepair

open Formal.Target Formal.Cells.SpecArbVacuous

theorem arbOK_mono {T T' : Nat} (h : T ≤ T') {A : List ArbNodes} {x : Beh} (hA : ArbOK T A x) :
    ArbOK T' A x := by
  intro a ha t1 t2 hc t ht1 ht2
  have c := hA a ha t1 t2 hc
  rw [c t (by omega) ht2, c (t1 + T') (by omega) (by omega)]

/-- The handover arbiter's nodes in `SpecArbVacuous.hb`: q 2; inputs r1 0, r2 1, rst 3, A0 4. -/
def hbArb : ArbNodes := ⟨2, [0, 1, 3, 4]⟩

/-- **The repaired form admits the handover** (which `ArbOK` excludes), for every `T ≥ 10`. -/
theorem arbOK_admits_handover (ta T : Nat) (hT : 10 ≤ T) : ArbOK T [hbArb] (hb ta) := by
  intro a ha t1 t2 hc t ht1 ht2
  simp only [List.mem_singleton] at ha
  subst ha
  show hb ta 2 t = hb ta 2 (t1 + T)
  simp only [hb, show (2 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 1 by omega, ite_false, ite_true]
  -- A0 constant on [t1, t2]: either the whole interval is before ta, or after
  by_cases hlate : ta ≤ t1
  · simp [show ¬ (t < ta + 10) by omega, show ¬ (t1 + T < ta + 10) by omega]
  · by_cases hearly : t2 < ta
    · simp [show t < ta + 10 by omega, show t1 + T < ta + 10 by omega]
    · exfalso
      have := hc 4 (by simp [hbArb]) ta (by omega) (by omega)
      simp [hb, show ¬ ta < ta by omega, show t1 < ta by omega] at this

/-- **Below the arc it is vacuous on an ordinary transition**: for `T < 10` the handover
behaviour (a GateOK behaviour, `handover_gate_ok`) violates `ArbOK2 T`. -/
theorem arbOK_needs_T_ge_arc (ta T : Nat) (hT : T < 10) :
    GateOK p1 0 gq (hb ta) ∧ ¬ ArbOK T [hbArb] (hb ta) := by
  refine ⟨handover_gate_ok ta, fun h => ?_⟩
  have c := h hbArb (List.mem_singleton_self _) ta (ta + 10) (by
    intro n hn s h1 _
    simp only [hbArb, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl <;> simp [hb, show ¬ s < ta by omega])
  have e2 := c (ta + 10) (by omega) le_rfl
  simp [hb, hbArb, show ta + T < ta + 10 by omega] at e2

end Formal.Cells.ArbOKRepair
