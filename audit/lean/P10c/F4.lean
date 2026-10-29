import Formal.Cells.IpowCellsT
/-! P10c item 4: ContractBridge (909e64f), IpowCellsT (d5b7ef2). -/
open Formal.Cells

#print axioms Formal.Cells.ContractBridge.fbCel_iff_si
#print axioms Formal.Cells.ContractBridge.fbCel_of_ctreeB
#print axioms Formal.Cells.ContractBridge.ctreeB_switching
#print axioms Formal.Cells.ContractBridge.steer_lut_of_pins
#print axioms Formal.Cells.ContractBridge.selPin_ok
#print axioms Formal.Cells.ContractBridge.lumped_of_fifo
#print axioms Formal.Cells.ContractBridge.lumped_needs_fifo
#print axioms Formal.Cells.ContractBridge.arb_excl_not_derivable
#print axioms Formal.Cells.ContractBridge.arb_excl_of_window
#print axioms Formal.Cells.ContractBridge.contract_of_contractB
#print axioms Formal.Cells.ContractBridge.ipow_safe_of_contracts'
#print axioms Formal.Cells.ContractBridge.ipow_contractsB_satisfiable
#print axioms Formal.Cells.ArbPin.su_osc_instance
#print axioms Formal.Cells.IpowCellsT.Gap.gap_exact
#print axioms Formal.Cells.IpowCellsT.Gap.si_not_fbCelT
#print axioms Formal.Cells.IpowCellsT.c2_fbCelT
#print axioms Formal.Cells.IpowCellsT.link_fbCelT
#print axioms Formal.Cells.IpowCellsT.ipow_safe_of_contractsT
#print axioms Formal.Cells.IpowCellsT.ipow_contractsT_satisfiable
#print axioms Formal.Cells.IpowCellsT.c2_fbCelT_witness

namespace P10c4
open Formal.Cells.ArbPin
/-- The H_ARB_EXCL counter-run (requests 100/105) is OUTSIDE B's exclusion window
(both disjuncts of arb_excl_of_window's H_WIN fail), so the two results are consistent. -/
example : ¬ ((105 : Int) + boxS.A2 ≤ 100 + boxS.a1 ∨
    ((100 : Int) + boxS.A1 + boxS.L ≤ 105 + boxS.a2 ∧ True)) := by decide
/-- Mutation: with r2 at 200 (outside the race), every behaviour is exclusive (su_nonvacuous),
so the counter-run genuinely needs the near-simultaneous requests. -/
example : ∀ c : Cell boxS false (up 100) (up 200), Excl c := su_nonvacuous.2.2.2.2.2.1
/-- The timing content of FbCelT is real: at gap 3 a route of delay 4 is rejected. -/
example : ¬ IpowCellsT.FbCelT IpowCells.cgate (IpowCellsT.Gap.p 3) (IpowCellsT.Gap.o 3)
    (IpowCellsT.Gap.route 3 4) :=
  fun h => absurd ((IpowCellsT.Gap.gap_exact 3 4 (by decide)).1.1 h) (by decide)
end P10c4
