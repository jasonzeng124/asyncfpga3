import Formal.Target.Spec

/-!
# Formal.Target.NetBase — helpers for the generated target netlist (`Formal/Target/Net/`)

`P n i o a b c d` is a 1-input copy gate (a pip or a site hop): INIT `0b10`, input node `i`,
output node `o`, one arc `⟨a, b, c, d⟩` (FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX in ps).
-/

namespace Formal.Target.Decoded
open Formal.Target

/-- A 1-input copy gate (pip or site hop). -/
@[reducible] def P (n : String) (i o a b c d : Nat) : Gate :=
  ⟨n, 1, 2, [i], [⟨a, b, c, d⟩], o⟩

end Formal.Target.Decoded

namespace Formal.Target

/-- Per-gate half of `Net.WF` (decidable, checked chunk by chunk). -/
def Gate.WFn (n : Nat) (g : Gate) : Prop :=
  g.ins.length = g.k ∧ g.arcs.length = g.k ∧ g.out < n ∧ (∀ i ∈ g.ins, i < n) ∧ g.init < 2 ^ 2 ^ g.k ∧
    (∀ e ∈ g.arcs, e.fmin ≤ e.fmax ∧ e.smin ≤ e.smax ∧ e.fmin ≤ e.smin ∧ e.fmax ≤ e.smax)

instance (n : Nat) (g : Gate) : Decidable (g.WFn n) := by unfold Gate.WFn; exact inferInstance

/-- The outputs of `l` are `s, s+1, ..` in order (checked chunk by chunk). -/
def outsOK : List Gate → Nat → Bool
  | [], _ => true
  | g :: l, s => g.out == s && outsOK l (s + 1)

theorem outsOK_append (l1 l2 : List Gate) (s : Nat) :
    outsOK (l1 ++ l2) s = (outsOK l1 s && outsOK l2 (s + l1.length)) := by
  induction l1 generalizing s with
  | nil => simp [outsOK]
  | cons g l ih =>
    simp only [List.cons_append, outsOK, ih, List.length_cons, Bool.and_assoc]
    rw [show s + 1 + l.length = s + (l.length + 1) by omega]

theorem map_out_of_outsOK : ∀ (l : List Gate) (s : Nat), outsOK l s = true →
    l.map Gate.out = List.range' s l.length
  | [], _, _ => rfl
  | g :: l, s, h => by
    simp only [outsOK, Bool.and_eq_true, beq_iff_eq] at h
    simp only [List.map_cons, List.length_cons, List.range'_succ, h.1, map_out_of_outsOK l (s + 1) h.2]

/-- `Net.WF` from the per-gate check and outputs `0, 1, .., m-1` in order (gate `i` drives node `i`). -/
theorem Net.wf_of_outs (N : Net) (h : ∀ g ∈ N.gates, g.WFn N.n) (hr : outsOK N.gates 0 = true) : N.WF := by
  refine ⟨fun g hg => ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h g hg
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  · rw [map_out_of_outsOK _ _ hr]; exact List.nodup_range' (s := 0) (n := N.gates.length)

end Formal.Target
