import Formal.Net.Compute.GcdBitwise
import Formal.Net.Compute.GcdAdd
/-! Negative controls for H_COMPUTE_FN (silent = every control holds): a one-bit INIT mutation
in a generated unit makes its certificate FALSE (kernel-decided), so the checks can fail. -/
open Formal.Net.Compute Formal.Net.Compute.GcdD Formal.Gen.Compute.GcdD

/-- uori0 with bit 3's OR LUT (INIT 14) turned into AND (INIT 8). -/
def uori0Mut : List Cell := Uori0.cells.map fun c => match c with
  | .lut 14 [.inp 0 3, .inp 1 3] o => .lut 8 [.inp 0 3, .inp 1 3] o
  | c => c

set_option maxRecDepth 100000 in
example : ¬ BitLocal uori0Mut Uori0.outs orS orSpec := by decide +kernel

/-- uaddi0 with bit 5's XOR LUT (INIT 6) turned into XNOR (INIT 9). -/
def uaddi0Mut : List Cell := Uaddi0.cells.map fun c => match c with
  | .lut 6 [.inp 0 5, .inp 1 5] o => .lut 9 [.inp 0 5, .inp 1 5] o
  | c => c

def AddBitMut (i : Nat) : Prop := SliceOK uaddi0Mut addCuts (i / 4) (outNet Uaddi0.outs i)
    (fun l => (sumL l).testBit (i % 4))

instance (i : Nat) : Decidable (AddBitMut i) := by unfold AddBitMut; exact inferInstance

set_option maxRecDepth 100000 in
example : ¬ AddBitMut 5 := by decide +kernel
