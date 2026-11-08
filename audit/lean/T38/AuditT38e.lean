import Formal.Cells.LatchHoldPinPS
import Formal.Cells.LatchHoldPinPS2
import Formal.Cells.LatchHoldPinPS3
open Formal.Cells in
def allRows := LatchHoldPinPS.rows ++ LatchHoldPinPS2.rows ++ LatchHoldPinPS3.rows
def kmax (r : Formal.Cells.LatchHoldCert.LatchHoldRow) : Float := (r.kA.toFloat - r.kB.toFloat) / (r.kA.toFloat + r.kB.toFloat)
#eval (allRows.map kmax).foldl min 1.0
#eval ((allRows.map fun r => (kmax r, r.l.q)).toArray.qsort (fun (a b : Float × Nat) => a.1 < b.1)).toList.take 6
#eval (allRows.filter fun r => r.l.q == 123323 || r.l.q == 123324).map fun r => (r.l.q, kmax r)
