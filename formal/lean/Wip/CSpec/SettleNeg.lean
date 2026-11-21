import Formal.Timing.SpecSettle
import Mathlib.Tactic.NormNum

/-! Controls for `Formal.Timing.SpecSettle.certOK` (shard C): a one-gate buffer, arc
(fmin, fmax, smin, smax) = (10, 12, 20, 25) ps, g = 1, κ = 0: `dmax = 25`, `dmin = 10`.
The certificate that starts the output's window at 25 is accepted; one tick earlier (24),
a window end past the input's + dmin (111), or the wrong value is rejected. -/

namespace Formal.Timing.SpecSettle.Neg
open Formal.Target Formal.Timing.SpecSettle

def buf : Gate := ⟨"buf", 1, 2, [0], [⟨10, 12, 20, 25⟩], 1⟩
def p1 : DelayPar := ⟨1, 0⟩

def cert (s1 u1 : Nat) (v1 : Bool) : Cert :=
  ⟨fun n => if n = 1 then s1 else 0, fun n => if n = 1 then u1 else 100, fun n => if n = 1 then v1 else true⟩

example : dmax p1 ⟨10, 12, 20, 25⟩ = 25 ∧ dmin p1 ⟨10, 12, 20, 25⟩ = 10 := by
  simp only [dmax, dmin, p1]; norm_num
example : certOK p1 (cert 25 110 true) [0] [buf] = true := by decide +kernel
example : certOK p1 (cert 24 110 true) [0] [buf] = false := by decide +kernel
example : certOK p1 (cert 25 111 true) [0] [buf] = false := by decide +kernel
example : certOK p1 (cert 25 110 false) [0] [buf] = false := by decide +kernel
example : certOK p1 (cert 25 110 true) [] [buf] = false := by decide +kernel

end Formal.Timing.SpecSettle.Neg
