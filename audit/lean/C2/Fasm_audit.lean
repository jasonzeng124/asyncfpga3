import Formal.Net.Fasm.CePair
open Formal.Net.Fasm Formal.Net.Fasm.CePair Formal.Cells Formal.Cells.CElemTiming

#print axioms Formal.Net.Fasm.CePair.next_state_s1
#print axioms Formal.Net.Fasm.CePair.next_state_s4
#print axioms Formal.Net.Fasm.CePair.perm_matters_s1
#print axioms Formal.Net.Fasm.CePair.q1_follow_hold_s1_ps
#print axioms Formal.Net.Fasm.CePair.q1_kleene_s1

/-- Audit: joint non-vacuity of `Behaves` with the claimed numeric bands
(LUT [45,124], every route [213,709]) -- all-false constant traces. -/
theorem audit_behaves_witness :
    Behaves CePairS1.net (fun _ _ => false) (fun _ _ _ => false) (fun _ _ _ => false)
      (fun _ => (45, 124)) (fun _ _ => (213, 709)) where
  H_LUT := by
    intro i L o hL
    intro t ht
    refine ⟨t - 45, by omega, by omega, ?_⟩
    have : i = 0 ∨ i = 1 := by
      rcases i with _ | _ | i
      · exact Or.inl rfl
      · exact Or.inr rfl
      · simp [CePairS1.net] at hL
    rcases this with rfl | rfl <;> simp [CePairS1.net] at hL <;> subst hL <;> cases o <;>
      (dsimp only; decide)
  H_ROUTE := by
    intro i L k s _ _ hc t ht
    refine ⟨t - 213, by omega, by omega, ?_⟩
    cases s with
    | const v => exact absurd rfl (hc v)
    | port _ => rfl
    | lut _ _ => rfl
  H_TIE := by
    intro i L k v hL hk t
    have : i = 0 ∨ i = 1 := by
      rcases i with _ | _ | i
      · exact Or.inl rfl
      · exact Or.inr rfl
      · simp [CePairS1.net] at hL
    rcases this with rfl | rfl <;> simp [CePairS1.net] at hL <;> subst hL <;>
      (rcases k with _ | _ | _ | _ | _ | _ | k <;> simp [CePairS1.lut0, CePairS1.lut1] at hk <;> (try subst hk) <;> rfl)

/-- ... and all hypotheses of `q1_follow_hold_s1_ps` hold jointly on it (v = false). -/
example : ∀ t, 0 + 124 ≤ t → t ≤ 1000 + 45 → (fun (_ : Nat) (_ : LOut) (_ : Nat) => false) 1 .o6 t = false :=
  q1_follow_hold_s1_ps audit_behaves_witness rfl rfl false 0 1000
    (fun _ _ _ => ⟨rfl, rfl, rfl⟩) (fun _ _ _ => rfl) (fun _ _ _ => Or.inl rfl)
