import Formal.Net.KernelCapXorshift
import Formal.Net.KernelCapCollatz
import Formal.Net.XorshiftWit
import Formal.Net.CollatzWit
/-! P11a item 5 (formal 8fea95c, C-8y2): KCap.kernel_circuit_safe; xorshift / collatz specs vs C. -/
open Formal.Net

#print axioms Formal.Net.KCap.kernel_circuit_safe
#print axioms Formal.Net.KCap.XorshiftInst.xorshift_circuit_safe
#print axioms Formal.Net.KCap.XorshiftInst.xorshift_circuit_safe_C
#check @Formal.Net.KCap.XorshiftInst.xorshift_circuit_safe

namespace P11a
-- Reference values: gcc -fwrapv on the research C bodies (audit/lean/P11a/vec.c).
example : XorshiftHw.xsSpec 2463534242 4 = 2008045182 := by decide +kernel
example : XorshiftHw.xsSpec 1 1 = 270369 := by decide +kernel
example : XorshiftHw.xsSpec 4294967295 10 = 1700793103 := by decide +kernel
example : XorshiftHw.xsSpec 123456789 1000 = 352297027 := by decide +kernel
example : XorshiftHw.xsSpec 5 2147483648 = 5 := by decide +kernel          -- rounds = INT_MIN
example : XorshiftHw.xsSpec 3735928559 4294967295 = 3735928559 := by decide +kernel  -- rounds = -1
example : XorshiftHw.xsSpec 7 0 = 7 := by decide +kernel
-- the C transcription (with fuel) agrees too
example : XorshiftHw.xorshiftC 1001 123456789 1000 = some 352297027 := by decide +kernel
-- collatz: C results 1->0, 7->16, 27->111, 97->118, 255->47, 871->178
example : CollatzHw.collatzC 300 1 = some 0 := by decide +kernel
example : CollatzHw.collatzC 300 7 = some 16 := by decide +kernel
example : CollatzHw.collatzC 300 27 = some 111 := by decide +kernel
example : CollatzHw.collatzC 300 97 = some 118 := by decide +kernel
example : CollatzHw.collatzC 300 255 = some 47 := by decide +kernel
example : CollatzHw.collatzC 300 871 = some 178 := by decide +kernel
-- MUTATION: a one-round spec with the right shift 17 changed to 16 differs at the C vector.
def roundM (x : Nat) : Nat :=
  let x1 := GcdHw.Ops.xori 32 x (GcdHw.Ops.shli 32 x 13)
  let x2 := GcdHw.Ops.xori 32 x1 (GcdHw.Ops.shrui 32 x1 16)
  GcdHw.Ops.xori 32 x2 (GcdHw.Ops.shli 32 x2 5)
example : Nat.repeat roundM 4 2463534242 ≠ 2008045182 := by decide +kernel
end P11a
