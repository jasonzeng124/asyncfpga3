import Formal.Target.Spec

/-!
# Audit T3: what the FROZEN `ArbOK` (H_ARB(T)) says, exactly

Against `Formal.Target.Spec` at formal 88c74e3c (frozen at 69c49057). No copy of any Spec
definition: `ArbOK`, `ConstOn`, `Beh`, `ArbNodes` are the frozen ones.

`arbOK_iff`: `ArbOK T A x` holds iff, for every listed arbiter, every change of its state
node `q` at a step `s -> s+1` with `s ≥ T` has a change of `r1` or `r2` at some step
`u -> u+1` with `s - T ≤ u ≤ s`. In words: **q may move only within T ps after one of the
two request nodes moved.** Any other input of the state gate (A0, rst, ...) moving q later
than T after the last request edge is forbidden by H_ARB(T) as frozen.
-/

open Formal.Target

namespace Audit.T3

/-- Request edge of arbiter `a` at step `u -> u+1`. -/
def ReqEdge (x : Beh) (a : ArbNodes) (u : Nat) : Prop :=
  x a.r1 (u + 1) ≠ x a.r1 u ∨ x a.r2 (u + 1) ≠ x a.r2 u

/-- q moves only within `T` after a request edge. -/
def QNearReq (T : Nat) (A : List ArbNodes) (x : Beh) : Prop :=
  ∀ a ∈ A, ∀ s, T ≤ s → x a.q (s + 1) ≠ x a.q s → ∃ u, s - T ≤ u ∧ u ≤ s ∧ ReqEdge x a u

theorem constOn_of_steps (y : Sig) (t1 t2 : Nat)
    (h : ∀ u, t1 ≤ u → u < t2 → y (u + 1) = y u) : ConstOn y t1 t2 := by
  intro t ht1 ht2
  induction t, ht1 using Nat.le_induction with
  | base => rfl
  | succ n hn ih => rw [h n hn (by omega), ih (by omega)]

theorem arbOK_iff (T : Nat) (A : List ArbNodes) (x : Beh) :
    ArbOK T A x ↔ QNearReq T A x := by
  constructor
  · intro harb a ha s hs hq
    by_contra hno
    push_neg at hno
    have step : ∀ (r : Nat), (r = a.r1 ∨ r = a.r2) → ∀ u, s - T ≤ u → u < s + 1 → x r (u + 1) = x r u := by
      intro r hr u hu1 hu2
      have := hno u hu1 (by omega)
      unfold ReqEdge at this
      push_neg at this
      rcases hr with rfl | rfl
      · exact this.1
      · exact this.2
    have c1 := constOn_of_steps _ _ _ (step a.r1 (Or.inl rfl))
    have c2 := constOn_of_steps _ _ _ (step a.r2 (Or.inr rfl))
    have hc := harb a ha (s - T) (s + 1) c1 c2
    have e : s - T + T = s := by omega
    rw [e] at hc
    exact hq (hc (s + 1) (by omega) le_rfl)
  · intro hn a ha t1 t2 c1 c2
    apply constOn_of_steps
    intro u hu1 hu2
    by_contra hq
    obtain ⟨w, hw1, hw2, hw⟩ := hn a ha u (by omega) hq
    rcases hw with h | h
    · exact h ((c1 (w + 1) (by omega) (by omega)).trans (c1 w (by omega) (by omega)).symm)
    · exact h ((c2 (w + 1) (by omega) (by omega)).trans (c2 w (by omega) (by omega)).symm)

end Audit.T3

#print axioms Audit.T3.arbOK_iff
