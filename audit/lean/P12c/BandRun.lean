import Formal.Core.XAudit.BandCheck
open Formal.Core.XAudit.Parse Formal.Core.XAudit.BandCheck
def main (args : List String) : IO UInt32 := do
  for p in args do
    match readBands (← readJson p) with
    | .ok B => IO.println s!"OK {p} ({B.cells.length} cells, {B.arcs.length} arcs)"
    | .error e => IO.println s!"REJECT {p}: nviol={(violations (← readJson p)).length} {e.take 300}"
  return 0
