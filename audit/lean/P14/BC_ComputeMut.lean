import Formal.Net.Compute.GcdBitwise
import Formal.Net.Compute.GcdAdd
import Formal.Net.Compute.GcdEqZero
import Formal.Net.Compute.GcdShrsi0
import Formal.Net.Compute.GcdShrsi3

/-! Auditor P14bc, claim C2 (H_COMPUTE_FN). Not part of the formal tree.
1. Axioms of the headline unit theorems.
2. Mutation: uori0's bit-5 LUT INIT 14 (OR) -> 6 (XOR): the kernel certificate must FAIL.
3. Cross-check of the Lean evaluator against the auditor's Python simulator on fixed vectors,
   including ushrsi0 at shift amounts other than 1 (not covered by the theorem). -/

open Formal.Net.Compute Formal.Net.GcdHw Formal.Gen.Compute.GcdD Formal.Net.Compute.GcdD

#print axioms uori0_fn
#print axioms uori1_fn
#print axioms ucmpi2_fn
#print axioms ucmpi3_fn
#print axioms ucmpi0_fn
#print axioms ucmpi10_fn
#print axioms uaddi0_fn
#print axioms ushrsi0_fn
#print axioms ushrsi3_fn

-- statement shapes (quantifier over every input)
#check @uori0_fn
#check @uaddi0_fn
#check @ucmpi0_fn
#check @ushrsi0_fn

def mutCells : List Cell := Uori0.cells.set 5 (.lut 6 [.inp 0 5, .inp 1 5] 76)

#eval (mutCells.length, Uori0.cells.length)

/-- The mutated netlist does NOT pass the certificate (kernel). -/
theorem uori0_mut_rejected : ¬ BitLocal mutCells Uori0.outs orS orSpec := by decide +kernel

/-- ... and the mutated unit really computes something else at a = b = 2^5. -/
#eval (unitVal mutCells Uori0.outs [32, 32], unitVal Uori0.cells Uori0.outs [32, 32]) -- expect (0, 32)

-- Lean-side evaluation on fixed vectors (compare with BC_netcmp.py / Python values below)
#eval unitVal Uaddi0.cells Uaddi0.outs [0xFFFFFFFF, 1]          -- expect 0
#eval unitVal Uaddi0.cells Uaddi0.outs [0x89ABCDEF, 0x76543210] -- expect 0xFFFFFFFF = 4294967295
#eval unitVal Ushrsi0.cells Ushrsi0.outs [0x80000001, 1]        -- expect 0xC0000000 = 3221225472
#eval unitVal Ushrsi0.cells Ushrsi0.outs [0x80000001, 4]        -- shift 4 (outside theorem): expect 0xF8000000 = 4160749568
#eval unitVal Ushrsi0.cells Ushrsi0.outs [0x7FFFFFF0, 3]        -- expect 0x0FFFFFFE = 268435454
#eval (Ops.shrsi 32 0x80000001 4, Ops.shrsi 32 0x7FFFFFF0 3)
#eval unitVal Ucmpi0.cells Ucmpi0.outs [0]                      -- expect 1
#eval unitVal Ucmpi0.cells Ucmpi0.outs [0x00010000]             -- expect 0
