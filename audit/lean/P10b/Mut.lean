import Formal.Core.Delay.InvolutionTrace
import Formal.Core.Prims.Muxf

/-! Mutation controls: EVERY theorem here must FAIL to elaborate. -/
namespace Audit.P10b.Mut
open Formal.Core.DelayInvolution Formal.Core.DelayInvolutionTransfer Formal.Core.Prims

/-- M1: a forgetful channel (history reset by the cancellation, T = ∞) gives [7]. -/
theorem m1 : ratPair.channel [0, 1 / 2, 5] = [7] := by
  simp only [InvolutionPair.channel, List.foldl, InvolutionPair.step,
    InvolutionPair.rat_delayAt, ratDelay]
  rw [show ratPair.infUp = (2 : ℝ) from rfl]
  norm_num

/-- M2: the guaranteed F7/F8 glitch width bound raised from 16 to 17 ps (fast). -/
theorem m2 : ∀ st fm, 17 ≤ (selmux st fm).s.lo .fast - (selmux st fm).i0.hi .fast := by
  intro st fm; cases st <;> cases fm <;> decide

end Audit.P10b.Mut
