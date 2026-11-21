import Formal.Core.XAudit.BandCheck

/-!
KapRes2 driver (Wip, not claimed): run the checked band reader `BandCheck.readBands` on every
band file named on the command line (or listed, one path per line, in `@LIST`).
Prints `OK <path>` or `REJECT <path>: <violations>`; exit code 1 if any file is rejected.

    lean --run Wip/KapRes2/BandCheckRun.lean FILE.json... | @LIST
-/

open Formal.Core.XAudit Formal.Core.XAudit.Parse Formal.Core.XAudit.BandCheck

def main (args : List String) : IO UInt32 := do
  let mut paths : Array String := #[]
  for a in args do
    if a.startsWith "@" then
      for l in (← IO.FS.lines (a.drop 1).toString) do
        if l != "" then paths := paths.push l
    else paths := paths.push a
  let mut nbad := 0
  for p in paths do
    match readBands (← readJson p) with
    | .ok B => IO.println s!"OK {p} ({B.cells.length} cells, {B.arcs.length} arcs)"
    | .error e => nbad := nbad + 1; IO.println s!"REJECT {p}: {e}"
  IO.println s!"[bandcheck] {paths.size} files, {nbad} rejected"
  return (if nbad == 0 then 0 else 1)
