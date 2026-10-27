import Formal.Timing.Rules
open Formal.Net Formal.Timing.Rules

#print axioms Formal.Timing.Rules.ruleE_sound
#print axioms Formal.Timing.Rules.race_sound
#print axioms Formal.Timing.Rules.ruleA_band_sound_small
#print axioms Formal.Timing.Rules.ruleA_not_band_sound
#print axioms Formal.Timing.Rules.ruleA_counterexample
#print axioms Formal.Timing.Rules.ruleE_corner_counterexample
#print axioms Formal.Timing.Rules.ruleE_sitepin_fails_all
#print axioms Formal.Timing.Rules.ruleE_sitepin_nonvacuous
#print axioms Formal.Timing.Rules.ruleJ_counterexample
#print axioms Formal.Timing.Rules.prefix_credit_needs_clean_edge

/-- Audit: all hypotheses of `ruleE_sound` hold jointly, with the early side
really moving (so `Bundled` is not vacuous here). -/
example : Bundled (shiftChain [500] step) true (shiftChain [800] step) :=
  ruleE_sound (Dr := [1000]) (Ds := [500]) (er := [(800, 800)]) (es := [(500, 500)]) (c := 0)
    step_window
    (shiftChain_chain _ _ _ (forall2_of_check (by decide)))
    (shiftChain_chain _ _ _ (forall2_of_check (by decide)))
    (forall2_of_check (by decide)) (forall2_of_check (by decide)) (by decide)

example : shiftChain [800] step 801 ≠ shiftChain [800] step 0 := by
  rw [shiftChain_step, shiftChain_step]; decide

/-- Audit: the rule-A/band boundary is 403, not 402: tl = 403 is still sound
(the Lean pair of theorems leaves 403 unstated; the journal says "<= 402"). -/
theorem audit_ruleA_403 {te : Nat} (h : ruleAPass te 403) : 1155 * 403 < 772 * te := by
  unfold ruleAPass at h; simp at h; omega
