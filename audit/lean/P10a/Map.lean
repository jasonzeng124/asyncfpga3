import Formal.Cells.ResetCapstoneMap
open Formal.Cells.ResetCapstoneMap Formal.Cells.ResetCapstone Formal.Cells.ResetGcd Formal.Net.CapNet.Gcd
#check @MapOK
#check @gcd_hw_safe_after_reset_map
#print axioms names_ok
#print axioms μT_ok
#print axioms μT_wire
#print axioms μW_not_wire
#print axioms gcd_hw_safe_after_reset_map
#print axioms reset_capstone_map_nonvac
#print axioms hot_rows
-- auditor mutation: hot request of channel 0 read from the cold node 1696 => MapOK fails
def μX : ChanMap := ⟨fun c => if c.val = 0 then 1696 else reqL.getD c.val 0, fun c => ackL.getD c.val 0⟩
theorem audit_mut_mapok : ¬ MapOK μX := by
  intro h
  have h1 := ((h ⟨0, by decide⟩).2.2.2.2.1).mpr (by decide)
  exact absurd h1 (by decide)
#print axioms audit_mut_mapok
