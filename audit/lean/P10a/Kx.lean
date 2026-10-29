import Formal.Cells.OnNetlistArbKappaExact
open Formal.Cells.OnNetlistArbKappaExact Formal.Cells.ArbA0Fork
#print axioms exact_s1c1_cons
#print axioms Bridge.exact_s1c1_cons
#print axioms bracket_s1c1_cons
#print axioms nonvac_s1c1_cons
#print axioms exact_s1c2_cons
#print axioms Bridge.exact_s1c2_cons
#print axioms bracket_s1c2_cons
#print axioms nonvac_s1c2_cons
#print axioms exact_s2c1_cons
#print axioms Bridge.exact_s2c1_cons
#print axioms bracket_s2c1_cons
#print axioms nonvac_s2c1_cons
#print axioms exact_s2c2_cons
#print axioms Bridge.exact_s2c2_cons
#print axioms bracket_s2c2_cons
#print axioms nonvac_s2c2_cons
#print axioms exact_s3c1_cons
#print axioms Bridge.exact_s3c1_cons
#print axioms bracket_s3c1_cons
#print axioms nonvac_s3c1_cons
#print axioms exact_s3c2_cons
#print axioms Bridge.exact_s3c2_cons
#print axioms bracket_s3c2_cons
#print axioms nonvac_s3c2_cons
#print axioms exact_s4c1_cons
#print axioms Bridge.exact_s4c1_cons
#print axioms bracket_s4c1_cons
#print axioms nonvac_s4c1_cons
#print axioms exact_s4c2_cons
#print axioms Bridge.exact_s4c2_cons
#print axioms bracket_s4c2_cons
#print axioms nonvac_s4c2_cons
#print axioms exact_s1c1_lit
#print axioms Bridge.exact_s1c1_lit
#print axioms bracket_s1c1_lit
#print axioms nonvac_s1c1_lit
#print axioms exact_s1c2_lit
#print axioms Bridge.exact_s1c2_lit
#print axioms bracket_s1c2_lit
#print axioms nonvac_s1c2_lit
#print axioms exact_s2c1_lit
#print axioms Bridge.exact_s2c1_lit
#print axioms bracket_s2c1_lit
#print axioms nonvac_s2c1_lit
#print axioms exact_s2c2_lit
#print axioms Bridge.exact_s2c2_lit
#print axioms bracket_s2c2_lit
#print axioms nonvac_s2c2_lit
#print axioms exact_s3c1_lit
#print axioms Bridge.exact_s3c1_lit
#print axioms bracket_s3c1_lit
#print axioms nonvac_s3c1_lit
#print axioms exact_s3c2_lit
#print axioms Bridge.exact_s3c2_lit
#print axioms bracket_s3c2_lit
#print axioms nonvac_s3c2_lit
#print axioms exact_s4c1_lit
#print axioms Bridge.exact_s4c1_lit
#print axioms bracket_s4c1_lit
#print axioms nonvac_s4c1_lit
#print axioms exact_s4c2_lit
#print axioms Bridge.exact_s4c2_lit
#print axioms bracket_s4c2_lit
#print axioms nonvac_s4c2_lit
#print axioms audit_s1c2_cons_200
#print axioms interior_s1c2_cons
#print axioms safe_antitone
#check @exact_s1c2_cons
#check @Bridge.exact_s1c2_cons
-- auditor: at my 200/1103 point, exact_s1c2_cons gives NOT-all-safe directly
theorem audit_200_not_safe : ¬ (∀ c d, (∀ e, Scat k200 c (A_s1c2_cons e) (d e)) → Safe F2 G2 true (dlOf d)) :=
  fun h => (by decide : ¬ Below_s1c2_cons k200) ((exact_s1c2_cons k200).1 h)
#print axioms audit_200_not_safe
-- auditor: just below the bracket all safe (1806/10000 < kappa_ex ~0.180679)
theorem audit_1806_safe : ∀ c d, (∀ e, Scat ⟨1806, 10000, by decide, by decide⟩ c (A_s1c2_cons e) (d e)) → Safe F2 G2 true (dlOf d) :=
  (exact_s1c2_cons _).2 (by decide)
#print axioms audit_1806_safe
