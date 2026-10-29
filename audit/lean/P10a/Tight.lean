import Formal.Cells.OnGcdArbKappaTight
open Formal.Cells.OnGcdArbKappaTight
#check @rt1b_safe
#check @rt1b_unsafe
#check @rt1b_gate_unsafe
#print axioms rt1b_safe
#print axioms rt1b_unsafe
#print axioms rt1b_not_allOK
#print axioms kS_kU_inside
#print axioms kex_bracket
#print axioms rt1b_safe_nonvacuous
#print axioms rt1b_gate_safe
#print axioms rt1b_gate_unsafe
#print axioms SU_overlap
#print axioms spread_correlated_safe
#print axioms spread_indep_fails
#print axioms cons_rows_k0
-- auditor: width of the undecided gap is 1/749546000000
example : kU.num = kS.num + 1 ∧ kU.den = kS.den ∧ kS.den = 749546000000 := by decide
-- MUTANT (must FAIL): safe at kU
example : AllOK (litModel kU) P7 Q7 0 0 := rt1b_safe kU (by decide)
-- MUTANT (must FAIL): dU violates by 2 fs
example : pathDelay dU Q7 + 2 = pathDelay dU P7 := by decide
