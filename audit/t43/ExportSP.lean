import FormalWit.NM.S
import FormalWit.NM.S2
-- T43: dump the site/pin tables (P, Q) and the extra rules of D2 for an independent comparison with prjxray-db
open Formal.Target.NM Formal.Target.NM.Data
partial def NT.toList {α : Type} : NT α → List (Nat × α)
  | .nil => []
  | .leaf j v => [(j, v)]
  | .node _ l r => NT.toList l ++ NT.toList r
def main : IO Unit := do
  let h ← IO.FS.Handle.mk "/root/t43/sp_dump.txt" .write
  for (i, s) in NT.toList P.sites do h.putStrLn s!"SITE {i} {s.name} {s.tile} {s.rank}"
  for (k, t) in NT.toList P.pins do
    for (k2, w) in NT.toList t do h.putStrLn s!"PIN {k} {k2} {w}"
  for (k, t) in NT.toList Q.pins do
    for (k2, w) in NT.toList t do h.putStrLn s!"PIN2 {k} {k2} {w}"
  for (i, w) in NT.toList wiresX do h.putStrLn s!"WIRE {i} {w}"
  for (i, r) in NT.toList rulesX do
    h.putStrLn s!"RULE {i} {r.t1} {r.t2} {r.dxp} {r.dxn} {r.dyp} {r.dyn}"
    for (k, p) in NT.toList r.pairs do h.putStrLn s!"PAIR {i} {k} {p.1} {p.2}"
  h.putStrLn s!"K {K}"
#eval main
