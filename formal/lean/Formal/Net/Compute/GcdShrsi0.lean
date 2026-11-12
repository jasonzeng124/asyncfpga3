import Formal.Net.Compute.Shift
import Formal.Gen.Compute.GcdD.Ushrsi0

/-!
# H_COMPUTE_FN for gcd_hw's arithmetic shift `ushrsi0`, with the shift amount gcd_hw uses

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

abbrev Shr0Bit (i : Nat) : Prop :=
  LocalOKF [] (coneW Ushrsi0.cells (Ushrsi0.outs.getD i .c0)) (Ushrsi0.outs.getD i .c0) (shrS i) fixOne
      (fun l => l.getD 0 false) ∧
    (afOf fixOne [] (coneW Ushrsi0.cells (Ushrsi0.outs.getD i .c0)) (Ushrsi0.outs.getD i .c0)).supp.all
      (fun l => decide (l ∈ shrS i)) = true

set_option maxRecDepth 100000 in
theorem ushrsi0_b0 : Shr0Bit 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b1 : Shr0Bit 1 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b2 : Shr0Bit 2 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b3 : Shr0Bit 3 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b4 : Shr0Bit 4 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b5 : Shr0Bit 5 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b6 : Shr0Bit 6 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b7 : Shr0Bit 7 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b8 : Shr0Bit 8 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b9 : Shr0Bit 9 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b10 : Shr0Bit 10 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b11 : Shr0Bit 11 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b12 : Shr0Bit 12 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b13 : Shr0Bit 13 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b14 : Shr0Bit 14 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b15 : Shr0Bit 15 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b16 : Shr0Bit 16 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b17 : Shr0Bit 17 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b18 : Shr0Bit 18 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b19 : Shr0Bit 19 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b20 : Shr0Bit 20 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b21 : Shr0Bit 21 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b22 : Shr0Bit 22 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b23 : Shr0Bit 23 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b24 : Shr0Bit 24 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b25 : Shr0Bit 25 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b26 : Shr0Bit 26 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b27 : Shr0Bit 27 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b28 : Shr0Bit 28 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b29 : Shr0Bit 29 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b30 : Shr0Bit 30 := by decide +kernel

set_option maxRecDepth 100000 in
theorem ushrsi0_b31 : Shr0Bit 31 := by decide +kernel

theorem ushrsi0_bits : ∀ i, i < 32 → Shr0Bit i
  | 0, _ => ushrsi0_b0
  | 1, _ => ushrsi0_b1
  | 2, _ => ushrsi0_b2
  | 3, _ => ushrsi0_b3
  | 4, _ => ushrsi0_b4
  | 5, _ => ushrsi0_b5
  | 6, _ => ushrsi0_b6
  | 7, _ => ushrsi0_b7
  | 8, _ => ushrsi0_b8
  | 9, _ => ushrsi0_b9
  | 10, _ => ushrsi0_b10
  | 11, _ => ushrsi0_b11
  | 12, _ => ushrsi0_b12
  | 13, _ => ushrsi0_b13
  | 14, _ => ushrsi0_b14
  | 15, _ => ushrsi0_b15
  | 16, _ => ushrsi0_b16
  | 17, _ => ushrsi0_b17
  | 18, _ => ushrsi0_b18
  | 19, _ => ushrsi0_b19
  | 20, _ => ushrsi0_b20
  | 21, _ => ushrsi0_b21
  | 22, _ => ushrsi0_b22
  | 23, _ => ushrsi0_b23
  | 24, _ => ushrsi0_b24
  | 25, _ => ushrsi0_b25
  | 26, _ => ushrsi0_b26
  | 27, _ => ushrsi0_b27
  | 28, _ => ushrsi0_b28
  | 29, _ => ushrsi0_b29
  | 30, _ => ushrsi0_b30
  | 31, _ => ushrsi0_b31
  | _ + 32, h => absurd h (by omega)

theorem ushrsi0_cert : ShrOK Ushrsi0.cells Ushrsi0.outs := ⟨rfl, ushrsi0_bits⟩

/-- **ushrsi0 computes `$signed(e0) >>> 1`** for every `e0` (with `e1 = 1`). -/
theorem ushrsi0_fn (a : Nat) : unitVal Ushrsi0.cells Ushrsi0.outs [a, 1] = Ops.shrsi 32 a 1 :=
  shr1_sound ushrsi0_cert a

end Formal.Net.Compute.GcdD
