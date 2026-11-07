import Formal.Net.Compute.Shift
import Formal.Gen.Compute.GcdD.Ushrsi3

/-!
# H_COMPUTE_FN for gcd_hw's arithmetic shift `ushrsi3`, with the shift amount gcd_hw uses

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

abbrev Shr3Bit (i : Nat) : Prop :=
  LocalOKF [] (coneW Ushrsi3.cells (Ushrsi3.outs.getD i .c0)) (Ushrsi3.outs.getD i .c0) (shrS i) fixOne
      (fun l => l.getD 0 false) ∧
    (afOf fixOne [] (coneW Ushrsi3.cells (Ushrsi3.outs.getD i .c0)) (Ushrsi3.outs.getD i .c0)).supp.all
      (fun l => decide (l ∈ shrS i)) = true

set_option maxRecDepth 100000 in
theorem ushrsi3_b0 : Shr3Bit 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b1 : Shr3Bit 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b2 : Shr3Bit 2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b3 : Shr3Bit 3 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b4 : Shr3Bit 4 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b5 : Shr3Bit 5 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b6 : Shr3Bit 6 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b7 : Shr3Bit 7 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b8 : Shr3Bit 8 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b9 : Shr3Bit 9 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b10 : Shr3Bit 10 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b11 : Shr3Bit 11 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b12 : Shr3Bit 12 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b13 : Shr3Bit 13 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b14 : Shr3Bit 14 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b15 : Shr3Bit 15 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b16 : Shr3Bit 16 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b17 : Shr3Bit 17 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b18 : Shr3Bit 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b19 : Shr3Bit 19 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b20 : Shr3Bit 20 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b21 : Shr3Bit 21 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b22 : Shr3Bit 22 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b23 : Shr3Bit 23 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b24 : Shr3Bit 24 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b25 : Shr3Bit 25 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b26 : Shr3Bit 26 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b27 : Shr3Bit 27 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b28 : Shr3Bit 28 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b29 : Shr3Bit 29 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b30 : Shr3Bit 30 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi3_b31 : Shr3Bit 31 := by decide +kernel

theorem ushrsi3_bits : ∀ i, i < 32 → Shr3Bit i
  | 0, _ => ushrsi3_b0
  | 1, _ => ushrsi3_b1
  | 2, _ => ushrsi3_b2
  | 3, _ => ushrsi3_b3
  | 4, _ => ushrsi3_b4
  | 5, _ => ushrsi3_b5
  | 6, _ => ushrsi3_b6
  | 7, _ => ushrsi3_b7
  | 8, _ => ushrsi3_b8
  | 9, _ => ushrsi3_b9
  | 10, _ => ushrsi3_b10
  | 11, _ => ushrsi3_b11
  | 12, _ => ushrsi3_b12
  | 13, _ => ushrsi3_b13
  | 14, _ => ushrsi3_b14
  | 15, _ => ushrsi3_b15
  | 16, _ => ushrsi3_b16
  | 17, _ => ushrsi3_b17
  | 18, _ => ushrsi3_b18
  | 19, _ => ushrsi3_b19
  | 20, _ => ushrsi3_b20
  | 21, _ => ushrsi3_b21
  | 22, _ => ushrsi3_b22
  | 23, _ => ushrsi3_b23
  | 24, _ => ushrsi3_b24
  | 25, _ => ushrsi3_b25
  | 26, _ => ushrsi3_b26
  | 27, _ => ushrsi3_b27
  | 28, _ => ushrsi3_b28
  | 29, _ => ushrsi3_b29
  | 30, _ => ushrsi3_b30
  | 31, _ => ushrsi3_b31
  | _ + 32, h => absurd h (by omega)

theorem ushrsi3_cert : ShrOK Ushrsi3.cells Ushrsi3.outs := ⟨rfl, ushrsi3_bits⟩

/-- **ushrsi3 computes `$signed(e0) >>> 1`** for every `e0` (with `e1 = 1`). -/
theorem ushrsi3_fn (a : Nat) : unitVal Ushrsi3.cells Ushrsi3.outs [a, 1] = Ops.shrsi 32 a 1 :=
  shr1_sound ushrsi3_cert a

end Formal.Net.Compute.GcdD
