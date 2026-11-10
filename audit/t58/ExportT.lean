import Formal.Net.Compute.PS.Uselect1T
import Formal.Net.Compute.PS.Ucmpi0T
import Formal.Net.Compute.PS.Ucmpi1T
import Formal.Net.Compute.PS.Ucmpi8T
import Formal.Net.Compute.PS.Ucmpi10T
import Formal.Net.Compute.PS.Uori0T
import Formal.Net.Compute.PS.Uori1T
import Formal.Net.Compute.PS.Uori4T
def main : IO Unit := do
  let h ← IO.FS.Handle.mk "/home/user/asyncfpga3/audit/t58/Ucmpi0_S.txt" .write
  for n in Formal.Net.Compute.PS.Ucmpi0.S do h.putStrLn s!"S {n}"
  IO.println s!"Ucmpi0 S {Formal.Net.Compute.PS.Ucmpi0.S.length} D {Formal.Net.Compute.PS.Ucmpi0T.D}"
  let h ← IO.FS.Handle.mk "/home/user/asyncfpga3/audit/t58/Ucmpi1_S.txt" .write
  for n in Formal.Net.Compute.PS.Ucmpi1.S do h.putStrLn s!"S {n}"
  IO.println s!"Ucmpi1 S {Formal.Net.Compute.PS.Ucmpi1.S.length} D {Formal.Net.Compute.PS.Ucmpi1T.D}"
  let h ← IO.FS.Handle.mk "/home/user/asyncfpga3/audit/t58/Ucmpi8_S.txt" .write
  for n in Formal.Net.Compute.PS.Ucmpi8.S do h.putStrLn s!"S {n}"
  IO.println s!"Ucmpi8 S {Formal.Net.Compute.PS.Ucmpi8.S.length} D {Formal.Net.Compute.PS.Ucmpi8T.D}"
  let h ← IO.FS.Handle.mk "/home/user/asyncfpga3/audit/t58/Ucmpi10_S.txt" .write
  for n in Formal.Net.Compute.PS.Ucmpi10.S do h.putStrLn s!"S {n}"
  IO.println s!"Ucmpi10 S {Formal.Net.Compute.PS.Ucmpi10.S.length} D {Formal.Net.Compute.PS.Ucmpi10T.D}"
  let h ← IO.FS.Handle.mk "/home/user/asyncfpga3/audit/t58/Uori0_S.txt" .write
  for n in Formal.Net.Compute.PS.Uori0.S do h.putStrLn s!"S {n}"
  IO.println s!"Uori0 S {Formal.Net.Compute.PS.Uori0.S.length} D {Formal.Net.Compute.PS.Uori0T.D}"
  let h ← IO.FS.Handle.mk "/home/user/asyncfpga3/audit/t58/Uori1_S.txt" .write
  for n in Formal.Net.Compute.PS.Uori1.S do h.putStrLn s!"S {n}"
  IO.println s!"Uori1 S {Formal.Net.Compute.PS.Uori1.S.length} D {Formal.Net.Compute.PS.Uori1T.D}"
  let h ← IO.FS.Handle.mk "/home/user/asyncfpga3/audit/t58/Uori4_S.txt" .write
  for n in Formal.Net.Compute.PS.Uori4.S do h.putStrLn s!"S {n}"
  IO.println s!"Uori4 S {Formal.Net.Compute.PS.Uori4.S.length} D {Formal.Net.Compute.PS.Uori4T.D}"
#eval main
#print axioms Formal.Net.Compute.PS.Ucmpi0T.ucmpi0_timed
#print axioms Formal.Net.Compute.PS.Ucmpi0T.ucmpi0_timed_circ
#print axioms Formal.Net.Compute.PS.Ucmpi1T.ucmpi1_timed
#print axioms Formal.Net.Compute.PS.Ucmpi1T.ucmpi1_timed_circ
#print axioms Formal.Net.Compute.PS.Ucmpi8T.ucmpi8_timed
#print axioms Formal.Net.Compute.PS.Ucmpi8T.ucmpi8_timed_circ
#print axioms Formal.Net.Compute.PS.Ucmpi10T.ucmpi10_timed
#print axioms Formal.Net.Compute.PS.Ucmpi10T.ucmpi10_timed_circ
#print axioms Formal.Net.Compute.PS.Uori0T.uori0_timed
#print axioms Formal.Net.Compute.PS.Uori0T.uori0_timed_circ
#print axioms Formal.Net.Compute.PS.Uori1T.uori1_timed
#print axioms Formal.Net.Compute.PS.Uori1T.uori1_timed_circ
#print axioms Formal.Net.Compute.PS.Uori4T.uori4_timed
#print axioms Formal.Net.Compute.PS.Uori4T.uori4_timed_circ
#print axioms Formal.Net.Compute.PS.Uselect1T.uselect1_timed_circ
#check @Formal.Net.Compute.PS.Uselect1T.uselect1_timed_circ
