import Formal.Target.PlanRPS
open Formal.Net.CViewPS Formal.Target
#eval (Cp ⟨1, 11/25⟩ * A1 + 87 * (Cp ⟨1, 11/25⟩ * M1) + 1, Cp ⟨8/5, 0⟩ * A1 + 87 * (Cp ⟨8/5,0⟩ * M1) + 1, Cp ⟨1, 0⟩ * A1 + 87 * (Cp ⟨1,0⟩ * M1) + 1)
example : Formal.Timing.SpecSettle.Sane ⟨1, 11/25⟩ := by unfold Formal.Timing.SpecSettle.Sane; norm_num
