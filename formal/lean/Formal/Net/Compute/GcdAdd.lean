import Formal.Net.Compute.Adder
import Formal.Gen.Compute.GcdD.Uaddi0

/-!
# H_COMPUTE_FN for gcd_hw's adder `uaddi0`

Problem statement. The combinational cone of `z_data` of gcd_hw's `bdc_fused_uaddi0` (bdc
Verilog `z = e0 + e1`, 32 bits; in gcd_hw `e1` is the constant-1 token of `k + 1`), as yosys
synthesized it (8 CARRY4 + 32 LUT2, `Formal.Gen.Compute.GcdD.Uaddi0`), computes
`Ops.addi 32 a b = (a + b) mod 2^32` for EVERY `a, b` (`uaddi0_fn`), not only `b = 1`.

Proof: `AddOK` with the eight CARRY4 carry-outs as cut points, checked by kernel `decide`
(32 output-bit and 7 carry checks of at most 512 assignments each), then `add_sound`.

Assumed / not covered: LUT, CARRY4 Boolean semantics (shard A's models; CARRY4 `c0 = CI |
CYINIT`); that this is the placed netlist (11f/11g); timing (H_COMPUTE_DELAY); glitches.
-/

namespace Formal.Net.Compute.GcdD
open Formal.Net.Compute Formal.Net.GcdHw Formal.Gen.Compute.GcdD

def addCuts : List Nat := [138, 142, 146, 150, 154, 158, 162, 166]

/-- Output bit `i` of uaddi0 (one kernel check per bit: a single `decide` over all 32 bits
needs ~13 GB). -/

abbrev AddBit (i : Nat) : Prop := Uaddi0.outs.getD i .c0 = .net (outNet Uaddi0.outs i) ∧
    SliceOK Uaddi0.cells addCuts (i / 4) (outNet Uaddi0.outs i) (fun l => (sumL l).testBit (i % 4))

abbrev AddCar (j : Nat) : Prop :=
    SliceOK Uaddi0.cells addCuts j (addCuts.getD j 0) (fun l => decide (16 ≤ sumL l))

set_option maxRecDepth 100000 in
theorem uaddi0_b0 : AddBit 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b1 : AddBit 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b2 : AddBit 2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b3 : AddBit 3 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b4 : AddBit 4 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b5 : AddBit 5 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b6 : AddBit 6 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b7 : AddBit 7 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b8 : AddBit 8 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b9 : AddBit 9 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b10 : AddBit 10 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b11 : AddBit 11 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b12 : AddBit 12 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b13 : AddBit 13 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b14 : AddBit 14 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b15 : AddBit 15 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b16 : AddBit 16 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b17 : AddBit 17 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b18 : AddBit 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b19 : AddBit 19 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b20 : AddBit 20 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b21 : AddBit 21 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b22 : AddBit 22 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b23 : AddBit 23 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b24 : AddBit 24 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b25 : AddBit 25 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b26 : AddBit 26 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b27 : AddBit 27 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b28 : AddBit 28 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b29 : AddBit 29 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b30 : AddBit 30 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_b31 : AddBit 31 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_c0 : AddCar 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_c1 : AddCar 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_c2 : AddCar 2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_c3 : AddCar 3 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_c4 : AddCar 4 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_c5 : AddCar 5 := by decide +kernel

set_option maxRecDepth 100000 in
theorem uaddi0_c6 : AddCar 6 := by decide +kernel

theorem uaddi0_bits : ∀ i, i < 32 → AddBit i
  | 0, _ => uaddi0_b0
  | 1, _ => uaddi0_b1
  | 2, _ => uaddi0_b2
  | 3, _ => uaddi0_b3
  | 4, _ => uaddi0_b4
  | 5, _ => uaddi0_b5
  | 6, _ => uaddi0_b6
  | 7, _ => uaddi0_b7
  | 8, _ => uaddi0_b8
  | 9, _ => uaddi0_b9
  | 10, _ => uaddi0_b10
  | 11, _ => uaddi0_b11
  | 12, _ => uaddi0_b12
  | 13, _ => uaddi0_b13
  | 14, _ => uaddi0_b14
  | 15, _ => uaddi0_b15
  | 16, _ => uaddi0_b16
  | 17, _ => uaddi0_b17
  | 18, _ => uaddi0_b18
  | 19, _ => uaddi0_b19
  | 20, _ => uaddi0_b20
  | 21, _ => uaddi0_b21
  | 22, _ => uaddi0_b22
  | 23, _ => uaddi0_b23
  | 24, _ => uaddi0_b24
  | 25, _ => uaddi0_b25
  | 26, _ => uaddi0_b26
  | 27, _ => uaddi0_b27
  | 28, _ => uaddi0_b28
  | 29, _ => uaddi0_b29
  | 30, _ => uaddi0_b30
  | 31, _ => uaddi0_b31
  | _ + 32, h => absurd h (by omega)

theorem uaddi0_carries : ∀ j, j < 7 → AddCar j
  | 0, _ => uaddi0_c0
  | 1, _ => uaddi0_c1
  | 2, _ => uaddi0_c2
  | 3, _ => uaddi0_c3
  | 4, _ => uaddi0_c4
  | 5, _ => uaddi0_c5
  | 6, _ => uaddi0_c6
  | _ + 7, h => absurd h (by omega)

theorem uaddi0_cert : AddOK Uaddi0.cells Uaddi0.outs addCuts :=
  ⟨rfl, Uaddi0.nodup, uaddi0_bits, uaddi0_carries⟩

/-- **uaddi0 computes `e0 + e1` (mod 2^32)** for every pair of inputs. -/
theorem uaddi0_fn (a b : Nat) : unitVal Uaddi0.cells Uaddi0.outs [a, b] = Ops.addi 32 a b :=
  add_sound uaddi0_cert a b

end Formal.Net.Compute.GcdD
