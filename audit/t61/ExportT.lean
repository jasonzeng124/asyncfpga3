import Formal.Net.Compute.PS.Uaddi0T
import Formal.Net.Compute.PS.Uori2T
import Formal.Net.Compute.PS.Uori3T
import Formal.Net.Compute.PS.Uselect0T
def main : IO Unit := do
  let h ← IO.FS.Handle.mk "/home/user/asyncfpga3/audit/t61/Uaddi0_S.txt" .write
  for n in Formal.Net.Compute.PS.Uaddi0.S do h.putStrLn s!"S {n}"
  IO.println s!"Uaddi0 S {Formal.Net.Compute.PS.Uaddi0.S.length} D {Formal.Net.Compute.PS.Uaddi0T.D}"
  let h ← IO.FS.Handle.mk "/home/user/asyncfpga3/audit/t61/Uori2_S.txt" .write
  for n in Formal.Net.Compute.PS.Uori2.S do h.putStrLn s!"S {n}"
  IO.println s!"Uori2 S {Formal.Net.Compute.PS.Uori2.S.length} D {Formal.Net.Compute.PS.Uori2T.D}"
  let h ← IO.FS.Handle.mk "/home/user/asyncfpga3/audit/t61/Uori3_S.txt" .write
  for n in Formal.Net.Compute.PS.Uori3.S do h.putStrLn s!"S {n}"
  IO.println s!"Uori3 S {Formal.Net.Compute.PS.Uori3.S.length} D {Formal.Net.Compute.PS.Uori3T.D}"
  let h ← IO.FS.Handle.mk "/home/user/asyncfpga3/audit/t61/Uselect0_S.txt" .write
  for n in Formal.Net.Compute.PS.Uselect0.S do h.putStrLn s!"S {n}"
  IO.println s!"Uselect0 S {Formal.Net.Compute.PS.Uselect0.S.length} D {Formal.Net.Compute.PS.Uselect0T.D}"
#eval main
#check @Formal.Net.Compute.PS.Uaddi0T.uaddi0_timed_circ
#check @Formal.Net.Compute.PS.Uori2T.uori2_timed_circ
#check @Formal.Net.Compute.PS.Uori3T.uori3_timed_circ
#check @Formal.Net.Compute.PS.Uselect0T.uselect0_timed_circ
