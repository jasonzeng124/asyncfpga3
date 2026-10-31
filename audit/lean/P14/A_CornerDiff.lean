import Formal.Core.Delay.CornerDiff

/-!
P14 audit (A): `CornerDiff.diff_not_imp_scat_strong` (commit a95e4a4e, answer to P13).

* instances at K = 0 and K = 99/100 (the statement is applied, not just compiled);
* the strong statement's per-scale property FAILS for the old (degenerate) witness pair
  (Pa = Pb = 1, da = db = |K|+3): at scale |K|+3 both tails are inside Scat K. So the new
  statement is genuinely stronger than what the old witness gives;
* the strong witness has positive tails (da = e > 0) and passes the rule-E guard.
-/

open Formal.Core.Corner Formal.Core.CornerDiff

namespace AuditP14A

example : ∃ da db : ℝ, 0 < guardLo * 2 - guardHi * 1 ∧ DiffScat 0 1 1 2 da db ∧
    ∀ s' : ℝ, 0 < s' → ¬ (Scat 0 (s' * 1) da ∧ Scat 0 (s' * 2) db) :=
  diff_not_imp_scat_strong 0 le_rfl (by norm_num)

example : ∃ da db : ℝ, 0 < guardLo * 2 - guardHi * 1 ∧ DiffScat 0 1 1 2 da db ∧
    ∀ s' : ℝ, 0 < s' → ¬ (Scat (99/100) (s' * 1) da ∧ Scat (99/100) (s' * 2) db) :=
  diff_not_imp_scat_strong (99/100) (by norm_num) (by norm_num)

/-- The old witness does NOT have the every-scale property (P13's objection, restated). -/
theorem old_witness_not_strong (K : ℝ) (hK : 0 ≤ K) :
    ¬ ∀ s' : ℝ, 0 < s' → ¬ (Scat K (s' * 1) (|K| + 3) ∧ Scat K (s' * 1) (|K| + 3)) := by
  intro h
  have hp : 0 < |K| + 3 := by have := abs_nonneg K; linarith
  apply h (|K| + 3) hp
  have hs : Scat K ((|K| + 3) * 1) (|K| + 3) := by
    unfold Scat; constructor <;> nlinarith
  exact ⟨hs, hs⟩

/-- The new witness's tails, written out (e = (1-K)/(4(1+K))): positive, nominally different. -/
example (K : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) :
    0 < (1 - K) / (4 * (1 + K)) ∧ DiffScat 0 1 1 2 ((1 - K) / (4 * (1 + K))) (1 + (1 - K) / (4 * (1 + K))) := by
  refine ⟨div_pos (by linarith) (by linarith), ?_⟩
  unfold DiffScat; constructor <;> linarith

end AuditP14A

#print axioms Formal.Core.CornerDiff.diff_not_imp_scat_strong
#print axioms AuditP14A.old_witness_not_strong
