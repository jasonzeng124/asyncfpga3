import Formal.Cells.ArbPin2
open Formal.Cells.ArbPin Formal.Cells.ArbPin2
namespace Audit.P8.AP
def r5FR : Row := ⟨5, 4, ⟨254, 316, 116, 145, 339, 412, 175, 221, 263, 328, 203, 246, 200, 241⟩, true, false, false, true⟩
theorem r5FR_mem : rows[39]? = some r5FR := by rfl
theorem r5FR_ok : rowOk r5FR = true := by decide
/-- seed 2 merge3.uarb1 FR: a TRANSPORT behaviour of the r2->r1 handover overlaps (for any f ≥ 0). -/
theorem merge3_h21_overlap : ∃ c : Cell r5FR.B false hi1 (dn 0), Transport c ∧ ¬ Excl c :=
  ((rowOk_sound r5FR r5FR_ok).2.2.1 0 (Int.le_refl _)).2 rfl
/-- MUTATION: claiming this row safe (v21 := true) is rejected by the checker. -/
def r5FRmut : Row := { r5FR with v21 := true }
theorem mut_rejected : rowOk r5FRmut = false := by decide
-- the kappa margin k21 = a2 + c5 - B2 = 116 + 203 - 328 = -9
example : k21 r5FR.B = -9 := by decide
end Audit.P8.AP
#print axioms Audit.P8.AP.merge3_h21_overlap
#print axioms Formal.Cells.ArbPin.h12_box_iff
#print axioms Formal.Cells.ArbPin.su_box_iff
#print axioms Formal.Cells.ArbPin.o1_box_iff
#print axioms Formal.Cells.ArbPin.o1_nonvacuous
#print axioms Formal.Cells.ArbPin.su_nonvacuous
#print axioms Formal.Cells.ArbPin2.gcd_rows
#print axioms Formal.Cells.ArbPin2.h21_box_iff
#print axioms Formal.Cells.ArbPin2.dd_box_iff
#print axioms Formal.Cells.ArbPin2.rows_ok
