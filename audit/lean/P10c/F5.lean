import Formal.Cells.ArbNoWithdraw
/-! P10c item 5: ArbNoWithdraw (2e7221d). -/
#print axioms Formal.Cells.ArbNoWithdraw.gcd_hw_arb_no_withdraw
#print axioms Formal.Cells.ArbNoWithdraw.arb_inputs
#print axioms Formal.Cells.ArbNoWithdraw.link_no_withdraw
#print axioms Formal.Cells.ArbNoWithdraw.link_no_withdraw_nonvacuous
#print axioms Formal.Cells.ArbNoWithdraw.steer_unsel_silent
#print axioms Formal.Cells.ArbNoWithdraw.steer_no_withdraw
#print axioms Formal.Cells.ArbNoWithdraw.steer_withdraws
#print axioms Formal.Cells.ArbNoWithdraw.settled1_of_causal
#print axioms Formal.Cells.ArbNoWithdraw.settled1_nonvacuous
#print axioms Formal.Cells.ArbNoWithdraw.settled_safe
#print axioms Formal.Cells.ArbNoWithdraw.settled_L0_fails
#print axioms Formal.Cells.ArbNoWithdraw.design_gate_held_causal
#print axioms Formal.Cells.ArbNoWithdraw.scn_excludes_caus

namespace P10c5
open Formal.Cells.LibGapSteer Formal.Cells.ArbNoWithdraw
/-- Mutation: the same steer with the select settled 100 ps earlier (700, so the setup
row holds with equality) is silent on the unselected branch at every instant. -/
example : ∀ t, outB false (pulse 1000 2000 ((Rd.const 300).σ t))
    (sAdv true 700 5000 ((Rd.const 600).σ t)) = false :=
  steer_unsel_silent false true (Rd.const 300) (Rd.const 600) 1000 2000 700 5000 (sAdv true 700 5000)
    (sAdv_stable true 700 5000) (by simp [Rd.const]) (by simp [Rd.const]) rfl
end P10c5
