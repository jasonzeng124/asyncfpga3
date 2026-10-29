import Formal.Cells.ArbBinary
open Formal.Cells Formal.Cells.ArbBinary
theorem st_eq (r1 r2 q rs a : Bool) : o6B ARB_ST [r1, r2, q, rs, a, true] =
    (rs || if a then q else ((r1 && !r2) || (q && !(!r1 && r2)))) := by
  cases r1 <;> cases r2 <;> cases q <;> cases rs <;> cases a <;> rfl
theorem r0_eq (r1 r2 q rs a : Bool) : o5B ARB_ST [r1, r2, q, rs, a, true] = ((r1 && q) || (r2 && !q)) := by
  cases r1 <;> cases r2 <;> cases q <;> cases rs <;> cases a <;> rfl
