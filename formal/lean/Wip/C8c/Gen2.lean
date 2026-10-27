import Formal.Net.Muller
open Formal.Net.Muller
def mkCert (m : Mode) (n K : Nat) : List (List Nat) :=
  let L := reachList m n
  (List.range K).map fun j => L.filter (· % K = j)
def emit (name : String) (m : Mode) (n K : Nat) : String :=
  let C := mkCert m n K
  s!"/-- {(reachList m n).length} reachable states, K = {K} buckets. -/\ndef {name} : List (List Nat) := [\n  " ++
    ",\n  ".intercalate (C.map toString) ++ "]\n"
#eval IO.FS.writeFile "Wip/C8c/certs2.txt" (emit "cert_iso4" .iso 4 64 ++ "\n" ++ emit "cert_rt3" .rt 3 64 ++ "\n" ++ emit "cert_rt4" .rt 4 256 ++ "\n" ++ emit "cert_iso5" .iso 5 256)
