import Formal.Net.Compute.PS.Ucmpi3T
-- T57: dump the ucmpi3 cone S and its 1-bit IO nodes, and C's D, for an own longest-path check
open Formal.Net.Compute.PS.Ucmpi3T
def main : IO Unit := do
  let h ← IO.FS.Handle.mk "/home/user/asyncfpga3/audit/t57/c3_dump.txt" .write
  for n in Formal.Net.Compute.PS.Ucmpi3.S do h.putStrLn s!"S {n}"
  h.putStrLn s!"IO 0 {Formal.Net.Compute.PS.Ucmpi3.e0Node 0} {Formal.Net.Compute.PS.Ucmpi3.e1Node 0} {Formal.Net.Compute.PS.Ucmpi3.zNode 0}"
  IO.println s!"S {Formal.Net.Compute.PS.Ucmpi3.S.length} D {D}"
#eval main
