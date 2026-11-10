import Formal.Net.Compute.PS.Uori4
-- T58: dump the uori4 cone S and its decoded IO nodes for an own evaluation of the decoded gates
open Formal.Net.Compute.PS.Uori4
#check @uori4_ps
#print axioms uori4_ps
def main : IO Unit := do
  let h ← IO.FS.Handle.mk "/home/user/asyncfpga3/audit/t58/o4_dump.txt" .write
  for n in S do h.putStrLn s!"S {n}"
  for i in List.range 32 do h.putStrLn s!"A {i} {e0Node i} {e1Node i}"
  h.putStrLn s!"C {e2Node 0} {e3Node 0} {zNode 0}"
  IO.println s!"S {S.length}"
#eval main
