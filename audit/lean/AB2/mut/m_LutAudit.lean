import Formal.Core.LutAudit
open Formal.Core.LutAudit Formal.Core.LutCells
-- mutation: one INIT bit of bd_c2 flipped; the proved audit count must no longer hold
def c2mut : LutInst := { bd_c2_u with init := 0xE800E800E800E9 }
theorem m1 : audit c2mut .O = (16, 20, 24, 4) := by decide +kernel
-- mutation: pin map changed (rst moved to a constant); the count must change
def c2mut2 : LutInst := { bd_c2_u with pins := [(.sig "a"), (.sig "b"), (.fb .O), .c0, .c0, .c0] }
theorem m2 : audit c2mut2 .O = (16, 20, 24, 4) := by decide +kernel
