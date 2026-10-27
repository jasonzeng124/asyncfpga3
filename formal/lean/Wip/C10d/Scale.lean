import Formal.Timing.WinArray
import Formal.Timing.CheckerToy
open Formal.Timing

#eval (List.range 15).map (winArr toyLink)
example : (List.range 15).map (winArr toyLink) = (List.range 15).map (win toyLink) := by decide
example : checkArr toyLink toyReq toyData toySetup = true := by decide

/-- A synthetic ladder: n stages, each with two parallel arcs then merge. -/
def ladder (n : Nat) : Netlist where
  arcs := (List.range n).flatMap fun i =>
    [⟨2*i, 2*i+1, 30, 60⟩, ⟨2*i, 2*i+2, 40, 70⟩, ⟨2*i+1, 2*i+2, 5, 9⟩]

#eval (ladder 300).arcs.length
#eval winArr (ladder 300) 600
#eval win (ladder 300) 600
set_option maxRecDepth 100000 in
theorem t100 : checkArr (ladder 100) 200 [199] 0 = true := by decide +kernel
