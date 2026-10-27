import Formal.Timing.WinArray
open Formal.Timing
def ladder (n : Nat) : Netlist where
  arcs := (List.range n).flatMap fun i =>
    [⟨2*i, 2*i+1, 30, 60⟩, ⟨2*i, 2*i+2, 40, 70⟩, ⟨2*i+1, 2*i+2, 5, 9⟩]
set_option maxRecDepth 100000 in
theorem t : checkArr (ladder 1000) (1000*2) [1000*2-1, 0] 0 = false := by decide +kernel
