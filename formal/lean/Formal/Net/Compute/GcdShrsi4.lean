import Formal.Net.Compute.Shift
import Formal.Gen.Compute.GcdD.Ushrsi4

/-!
# H_COMPUTE_FN for gcd_hw's arithmetic shift `ushrsi4`, with the shift amount gcd_hw uses

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

abbrev Shr4Bit (i : Nat) : Prop :=
  LocalOKF [] (coneW Ushrsi4.cells (Ushrsi4.outs.getD i .c0)) (Ushrsi4.outs.getD i .c0) (shrS i) fixOne
      (fun l => l.getD 0 false) ∧
    (afOf fixOne [] (coneW Ushrsi4.cells (Ushrsi4.outs.getD i .c0)) (Ushrsi4.outs.getD i .c0)).supp.all
      (fun l => decide (l ∈ shrS i)) = true

set_option maxRecDepth 100000 in
theorem ushrsi4_b0 : Shr4Bit 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b1 : Shr4Bit 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b2 : Shr4Bit 2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b3 : Shr4Bit 3 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b4 : Shr4Bit 4 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b5 : Shr4Bit 5 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b6 : Shr4Bit 6 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b7 : Shr4Bit 7 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b8 : Shr4Bit 8 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b9 : Shr4Bit 9 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b10 : Shr4Bit 10 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b11 : Shr4Bit 11 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b12 : Shr4Bit 12 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b13 : Shr4Bit 13 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b14 : Shr4Bit 14 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b15 : Shr4Bit 15 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b16 : Shr4Bit 16 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b17 : Shr4Bit 17 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b18 : Shr4Bit 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b19 : Shr4Bit 19 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b20 : Shr4Bit 20 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b21 : Shr4Bit 21 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b22 : Shr4Bit 22 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b23 : Shr4Bit 23 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b24 : Shr4Bit 24 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b25 : Shr4Bit 25 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b26 : Shr4Bit 26 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b27 : Shr4Bit 27 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b28 : Shr4Bit 28 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b29 : Shr4Bit 29 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b30 : Shr4Bit 30 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi4_b31 : Shr4Bit 31 := by decide +kernel

theorem ushrsi4_bits : ∀ i, i < 32 → Shr4Bit i
  | 0, _ => ushrsi4_b0
  | 1, _ => ushrsi4_b1
  | 2, _ => ushrsi4_b2
  | 3, _ => ushrsi4_b3
  | 4, _ => ushrsi4_b4
  | 5, _ => ushrsi4_b5
  | 6, _ => ushrsi4_b6
  | 7, _ => ushrsi4_b7
  | 8, _ => ushrsi4_b8
  | 9, _ => ushrsi4_b9
  | 10, _ => ushrsi4_b10
  | 11, _ => ushrsi4_b11
  | 12, _ => ushrsi4_b12
  | 13, _ => ushrsi4_b13
  | 14, _ => ushrsi4_b14
  | 15, _ => ushrsi4_b15
  | 16, _ => ushrsi4_b16
  | 17, _ => ushrsi4_b17
  | 18, _ => ushrsi4_b18
  | 19, _ => ushrsi4_b19
  | 20, _ => ushrsi4_b20
  | 21, _ => ushrsi4_b21
  | 22, _ => ushrsi4_b22
  | 23, _ => ushrsi4_b23
  | 24, _ => ushrsi4_b24
  | 25, _ => ushrsi4_b25
  | 26, _ => ushrsi4_b26
  | 27, _ => ushrsi4_b27
  | 28, _ => ushrsi4_b28
  | 29, _ => ushrsi4_b29
  | 30, _ => ushrsi4_b30
  | 31, _ => ushrsi4_b31
  | _ + 32, h => absurd h (by omega)

theorem ushrsi4_cert : ShrOK Ushrsi4.cells Ushrsi4.outs := ⟨rfl, ushrsi4_bits⟩

/-- **ushrsi4 computes `$signed(e0) >>> 1`** for every `e0` (with `e1 = 1`). -/
theorem ushrsi4_fn (a : Nat) : unitVal Ushrsi4.cells Ushrsi4.outs [a, 1] = Ops.shrsi 32 a 1 :=
  shr1_sound ushrsi4_cert a

end Formal.Net.Compute.GcdD
