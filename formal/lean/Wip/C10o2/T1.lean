import Formal.Timing.ChainSettleExe
open Formal.Net Formal.Timing Formal.Timing.ChainSettleExe
def rr : Row := { arcs := [⟨0,1,1,10⟩, ⟨1,2,1,8⟩, ⟨0,2,3,3⟩], N := 2, z := 2, F := 1, T := 5, taps := [2] }
#eval verdict rr
#eval sets rr.arcs 1 5 2
def r2 : Row := { arcs := [⟨0,1,300,400⟩, ⟨1,2,200,300⟩, ⟨0,2,150,250⟩], N := 2, z := 2, F := 1000, T := 600, taps := [2] }
#eval verdict r2
theorem t1 : verdict rr = ⟨true, true, 1, 4, 9, 2, true, true, false⟩ := by decide
theorem t2 : (verdict r2).bridge = true := by decide
