import FormalWit.NM.DB
-- T43: dump the trusted NodeMerge tables of FormalWit.NM.DB as plain text for an independent comparison with prjxray-db
open Formal.Target.NM Formal.Target.NM.Data
partial def NT.toList {α : Type} : NT α → List (Nat × α)
  | .nil => []
  | .leaf j v => [(j, v)]
  | .node _ l r => NT.toList l ++ NT.toList r
def main : IO Unit := do
  let h ← IO.FS.Handle.mk "/root/t43/db_dump.txt" .write
  for t in tyNames.zipIdx do h.putStrLn s!"TY {t.2} {t.1}"
  for (i, t) in NT.toList D.tiles do h.putStrLn s!"TILE {i} {t.name} {t.ty} {t.x} {t.y}"
  for (i, w) in NT.toList D.wires do h.putStrLn s!"WIRE {i} {w}"
  for (i, r) in NT.toList D.rules do
    h.putStrLn s!"RULE {i} {r.t1} {r.t2} {r.dxp} {r.dxn} {r.dyp} {r.dyn}"
    for (k, p) in NT.toList r.pairs do h.putStrLn s!"PAIR {i} {k} {p.1} {p.2}"
#eval main
