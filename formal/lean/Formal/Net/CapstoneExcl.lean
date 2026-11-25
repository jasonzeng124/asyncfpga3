import Formal.Net.GcdHwLive

/-!
# Probe C-8l: the token-level half of H_CM_FORCED

At token level, the two (or three) inputs of every control_merge in bdc's gcd_hw graph never
hold tokens at the same time, in any reachable store, under any schedule and arbitration
(`cm_inputs_exclusive`). So the token run never exercises an arbitration choice, and its
label stream is forced by availability: the token-level analogue of 8j's H_EXCL_REQ.

What H_CM_FORCED (`CapstoneCM.amerge_op_forced`) still needs is the CIRCUIT half: that the
circuit offers a header token only when the token run would, i.e. a simulation (O1).

Proof: every control_merge input lies on the control spine (`cm_ins_on_spine`, kernel
check), and the spine carries at most one token in every reachable store (C-8i's
`closed_of_check` + `init_inv`, H_ONE_INVOCATION, proved).
-/

namespace Formal.Net.GcdHw.Gcd
open Formal.Net.Kahn Formal.Net.GcdHw

/-- The input channel of a control_merge label, if the rule is one. -/
def cmIn : Rule → Option Nat
  | .cm i _ _ _ => some i
  | _ => none

theorem cm_ins_on_spine : rules.all (fun r => match cmIn r with
    | some i => decide (i ∈ spine) | none => true) = true := by decide +kernel

/-- Every store reachable from the initial store carries at most one spine token. -/
theorem reach_inv {a b : Nat} : ∀ n s, Run (step G) (init a b) n s → Inv spine s := by
  intro n s h
  have : ∀ s0 n s, Run (step G) s0 n s → Inv spine s0 → Inv spine s := by
    intro s0 n s h
    induction h with
    | refl => exact id
    | cons l hs _ ih => exact fun hi => ih (closedG _ _ _ hi hs)
  exact this _ _ _ h (init_inv a b)

/-- **Token-level exclusivity of control_merge inputs.** In every reachable store, two
distinct control_merge input channels are never both non-empty. -/
theorem cm_inputs_exclusive {a b : Nat} (n : Nat) (s : Store Nat Nat)
    (h : Run (step G) (init a b) n s) (l1 l2 : Nat) (r1 r2 : Rule) (i1 i2 : Nat)
    (h1 : rules[l1]? = some r1) (h2 : rules[l2]? = some r2)
    (e1 : cmIn r1 = some i1) (e2 : cmIn r2 = some i2) (hne : i1 ≠ i2) :
    ¬ (s i1 ≠ [] ∧ s i2 ≠ []) := by
  rintro ⟨n1, n2⟩
  have hs := List.all_eq_true.mp cm_ins_on_spine
  have m1 : i1 ∈ spine := by
    have := hs r1 (List.mem_of_getElem? h1); rw [e1] at this; simpa using this
  have m2 : i2 ∈ spine := by
    have := hs r2 (List.mem_of_getElem? h2); rw [e2] at this; simpa using this
  have hinv := reach_inv n s h
  unfold Inv cnt at hinv
  have l1' : 1 ≤ (s i1).length := by
    cases hc : s i1 with
    | nil => exact absurd hc n1
    | cons _ _ => simp
  have l2' : 1 ≤ (s i2).length := by
    cases hc : s i2 with
    | nil => exact absurd hc n2
    | cons _ _ => simp
  have := two_le_sum (f := fun c => (s c).length) spine_nodup m1 m2 hne l1' l2'
  omega

end Formal.Net.GcdHw.Gcd
