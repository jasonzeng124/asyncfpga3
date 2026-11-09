import Formal.Net.Compute.PS.Uselect1
-- T51: dump the uselect1 cone S and its decoded input/output nodes for an own evaluation of the decoded gates
open Formal.Net.Compute.PS.Uselect1
#check @uselect1_ps
#print axioms uselect1_ps
def main : IO Unit := do
  let h ← IO.FS.Handle.mk "/root/t51/u1_dump.txt" .write
  for n in S do h.putStrLn s!"S {n}"
  for i in List.range 32 do h.putStrLn s!"IO {i} {e0Node i} {e1Node i} {zNode i}"
  IO.println s!"S {S.length}"
#eval main
