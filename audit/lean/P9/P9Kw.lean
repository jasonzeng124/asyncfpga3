import Formal.Cells.KleeneWin
/-! P9 audit, item 4. -/
namespace P9Kw
open Formal.Cells Formal.Cells.KleeneWin
#check @steer_win_exact
#print axioms steer_win_exact
#print axioms join_win_exact
#print axioms muxn_win_exact
#print axioms latch_win_exact
#print axioms cel_edges_iff
#print axioms cel_env_win_iff
#print axioms steer_split_matters
#print axioms steer_witness_W
#print axioms steer_ct_split_x
#print axioms c2_fbwin_hazard

/-- My instance: binary setup equality (800+500 = 1000+300) with split cS0 = 1 (select's
entry window trails by 1): unsafe. With cS0 = 0, aR = 0: safe. -/
theorem mine_unsafe : ¬ SteerW true true 300 300 500 500 1000 3000 0 0 0 0 800 1 2800 0 := by
  rw [steer_win_exact true true 300 300 500 500 1000 3000 0 0 0 0 800 1 2800 0
    (by decide) (by decide) (by decide) (by decide) (by decide)]; decide
theorem mine_safe : SteerW true true 300 300 500 500 1000 3000 0 0 0 0 800 0 2800 0 :=
  (steer_win_exact true true 300 300 500 500 1000 3000 0 0 0 0 800 0 2800 0
    (by decide) (by decide) (by decide) (by decide) (by decide)).2 (by decide)
/-- Mutation: the form without the window terms is NOT exact. -/
theorem mut_drop : ¬ (∀ b v (Rlo Rhi Slo Shi R F aR cR aF cF S0 cS0 S1 aS1 : Int),
    Rlo ≤ Rhi → Slo ≤ Shi → R - aR < F + cF → 0 ≤ aR + cR → 0 ≤ aF + cF →
    (SteerW b v Rlo Rhi Slo Shi R F aR cR aF cF S0 cS0 S1 aS1 ↔
      (S0 + Shi ≤ R + Rlo ∧ F + Rhi ≤ S1 + Slo))) := by
  intro h
  exact mine_unsafe ((h true true 300 300 500 500 1000 3000 0 0 0 0 800 1 2800 0
    (by decide) (by decide) (by decide) (by decide) (by decide)).2 (by decide))
end P9Kw
