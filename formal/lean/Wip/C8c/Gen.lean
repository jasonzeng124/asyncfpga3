import Formal.Net.Muller
open Formal.Net.Muller
def pack (l : List Nat) : Nat := l.foldr (fun s acc => acc * digit + (s + 1)) 0
def mkCert (m : Mode) (n K : Nat) : List Nat :=
  let L := reachList m n
  (List.range K).map fun j => pack (L.filter (· % K = j))
def emit (name : String) (m : Mode) (n K : Nat) : String :=
  let C := mkCert m n K
  s!"/-- {(reachList m n).length} states, K = {K}. -/\ndef {name} : List Nat := [\n  " ++
    ", ".intercalate (C.map toString) ++ "]\n"
-- #eval (reachList .iso 5).length
-- #eval (reachList .rt 5).length
#eval IO.FS.writeFile "Wip/C8c/certs.txt" (emit "cert_iso4" .iso 4 64 ++ "\n" ++ emit "cert_rt3" .rt 3 64 ++ "\n" ++ emit "cert_rt4" .rt 4 256 ++ "\n" ++ emit "cert_iso5" .iso 5 256)
