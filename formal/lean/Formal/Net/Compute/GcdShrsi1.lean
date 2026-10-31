import Formal.Net.Compute.Shift
import Formal.Gen.Compute.GcdD.Ushrsi1

/-!
# H_COMPUTE_FN for gcd_hw's arithmetic shift `ushrsi1`, with the shift amount gcd_hw uses

Problem statement. This `bdc_fused_*` unit (bdc Verilog `z = $signed(e0) >>> e1`, a general
32-bit barrel shifter in the yosys netlist) computes `Ops.shrsi 32 a 1` for EVERY `a` when its
port `e1` carries 1, the only value it carries in gcd_hw (the Ops join is
`.bin .shrsi 32 (.var 0) (.lit 1)`; `e1` is fed by a constant-1 token).

Proof: `ShrOK`: each output bit's cone, with port 1 fixed to 1 and constants folded through the
LUT cofactors and MUXF selects (`Fold.lean`), depends on at most two input bits, and is checked
over them; one kernel check per bit (all 32 in one `decide` take ~7 GB). Then `shr1_sound`.

NOT shown: other shift amounts (unused by gcd_hw); that the constant token on `e1` is 1 (the
constant source's cell model, part of H_CELLS); LUT/MUXF semantics are shard A's models; timing;
glitches.
-/

namespace Formal.Net.Compute.GcdD
open Formal.Net.Compute Formal.Net.GcdHw Formal.Gen.Compute.GcdD

abbrev Shr1Bit (i : Nat) : Prop :=
  LocalOKF [] (coneW Ushrsi1.cells (Ushrsi1.outs.getD i .c0)) (Ushrsi1.outs.getD i .c0) (shrS i) fixOne
      (fun l => l.getD 0 false) ∧
    (afOf fixOne [] (coneW Ushrsi1.cells (Ushrsi1.outs.getD i .c0)) (Ushrsi1.outs.getD i .c0)).supp.all
      (fun l => decide (l ∈ shrS i)) = true

set_option maxRecDepth 100000 in
theorem ushrsi1_b0 : Shr1Bit 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b1 : Shr1Bit 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b2 : Shr1Bit 2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b3 : Shr1Bit 3 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b4 : Shr1Bit 4 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b5 : Shr1Bit 5 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b6 : Shr1Bit 6 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b7 : Shr1Bit 7 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b8 : Shr1Bit 8 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b9 : Shr1Bit 9 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b10 : Shr1Bit 10 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b11 : Shr1Bit 11 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b12 : Shr1Bit 12 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b13 : Shr1Bit 13 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b14 : Shr1Bit 14 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b15 : Shr1Bit 15 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b16 : Shr1Bit 16 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b17 : Shr1Bit 17 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b18 : Shr1Bit 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b19 : Shr1Bit 19 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b20 : Shr1Bit 20 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b21 : Shr1Bit 21 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b22 : Shr1Bit 22 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b23 : Shr1Bit 23 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b24 : Shr1Bit 24 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b25 : Shr1Bit 25 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b26 : Shr1Bit 26 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b27 : Shr1Bit 27 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b28 : Shr1Bit 28 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b29 : Shr1Bit 29 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b30 : Shr1Bit 30 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi1_b31 : Shr1Bit 31 := by decide +kernel

theorem ushrsi1_bits : ∀ i, i < 32 → Shr1Bit i
  | 0, _ => ushrsi1_b0
  | 1, _ => ushrsi1_b1
  | 2, _ => ushrsi1_b2
  | 3, _ => ushrsi1_b3
  | 4, _ => ushrsi1_b4
  | 5, _ => ushrsi1_b5
  | 6, _ => ushrsi1_b6
  | 7, _ => ushrsi1_b7
  | 8, _ => ushrsi1_b8
  | 9, _ => ushrsi1_b9
  | 10, _ => ushrsi1_b10
  | 11, _ => ushrsi1_b11
  | 12, _ => ushrsi1_b12
  | 13, _ => ushrsi1_b13
  | 14, _ => ushrsi1_b14
  | 15, _ => ushrsi1_b15
  | 16, _ => ushrsi1_b16
  | 17, _ => ushrsi1_b17
  | 18, _ => ushrsi1_b18
  | 19, _ => ushrsi1_b19
  | 20, _ => ushrsi1_b20
  | 21, _ => ushrsi1_b21
  | 22, _ => ushrsi1_b22
  | 23, _ => ushrsi1_b23
  | 24, _ => ushrsi1_b24
  | 25, _ => ushrsi1_b25
  | 26, _ => ushrsi1_b26
  | 27, _ => ushrsi1_b27
  | 28, _ => ushrsi1_b28
  | 29, _ => ushrsi1_b29
  | 30, _ => ushrsi1_b30
  | 31, _ => ushrsi1_b31
  | _ + 32, h => absurd h (by omega)

theorem ushrsi1_cert : ShrOK Ushrsi1.cells Ushrsi1.outs := ⟨rfl, ushrsi1_bits⟩

/-- **ushrsi1 computes `$signed(e0) >>> 1`** for every `e0` (with `e1 = 1`). -/
theorem ushrsi1_fn (a : Nat) : unitVal Ushrsi1.cells Ushrsi1.outs [a, 1] = Ops.shrsi 32 a 1 :=
  shr1_sound ushrsi1_cert a

end Formal.Net.Compute.GcdD
