import Formal.Cells.LibGapMux
open Formal.Cells.LibGapSteer
example (u : Int) (h1 : 1400 - 100 ≤ u) (h2 : u < 1400) :
    decide ((0 : Int) ≤ (Rd.const 0).σ u ∧ (Rd.const 0).σ u < 2000) = true := by
  simp [Rd.const]
  trace_state
  sorry
