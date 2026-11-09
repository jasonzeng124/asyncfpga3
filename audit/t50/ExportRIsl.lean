import Formal.Net.CViewPS.RIslPS
-- T50: dump C's reset island (members, listed values, rho) and print the main statements' axioms
open Formal.Net.CViewPS Formal.Target
#check @reset_quiet_PS15
#print axioms reset_quiet_PS
#print axioms reset_quiet_PS15
#eval rstPS
def main : IO Unit := do
  let h ← IO.FS.Handle.mk "/root/t50/risl_dump.txt" .write
  let mut n := 0
  for w in List.range 190000 do
    if memR w then
      h.putStrLn s!"{w} {valR w} {rhoR w}"
      n := n + 1
  IO.println s!"members {n}"
#eval main
