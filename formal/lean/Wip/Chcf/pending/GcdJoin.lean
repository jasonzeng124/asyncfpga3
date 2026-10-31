import Formal.Net.CapstoneNetChk
import Formal.Net.Compute.GcdBitwise
import Formal.Net.Compute.GcdEqZero
import Formal.Net.Compute.GcdAdd
import Formal.Net.Compute.GcdShrsi0
import Formal.Net.Compute.GcdShrsi1
import Formal.Net.Compute.GcdShrsi2
import Formal.Net.Compute.GcdShrsi3
import Formal.Net.Compute.GcdShrsi4
import Formal.Net.Compute.GcdUori2
import Formal.Net.Compute.GcdUori3
import Formal.Net.Compute.GcdUori4
import Formal.Net.Compute.GcdUselect0
import Formal.Net.Compute.GcdUselect1Fn
import Formal.Net.Compute.GcdShli0

/-!
# H_COMPUTE_FN in the capstone's own terms: every gcd_hw join function is a synthesized unit's

Problem statement. The capstone's 465-channel gcd_hw network (`Formal.Net.CapNet.Gcd.ops`, from
bdc's own graph) has 20 `join` operators; each carries its data function `jg e js` (the fused
MLIR region, constants folded, as `Formal.Net.CapNet.jg`). For each of them, this file proves that
`jg e js` equals the function of the yosys-synthesized `bdc_fused_*` unit that computes that
operation, on the unit's ports as bdc wires them (constant operands as constant port values; a
1-bit port as the low bit, `trunci 1`), for every input value (within the stated ranges: 32-bit
token values for `uselect0`, shift amount `< 32` for `ushli0`).

What this does NOT show: WHICH physical unit implements which join (the RTL-net to Ops-channel
map, H_MAP, is not in Lean; units are paired by operation, and identical operations have
identical netlists here); that the constant ports carry those constants (the constant sources'
cell models); timing; that tokens are 32-bit (the range hypotheses).
-/

namespace Formal.Net.Compute.GcdJoin
open Formal.Net Formal.Net.Compute Formal.Net.GcdHw Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Gen.Compute.GcdD Formal.Net.Compute.GcdD

/-- The data function of operator `p` if it is a join. -/
def jgAt (p : Nat) : List Nat → Nat :=
  match ops.getD p (K.sink 0) with
  | .join _ _ e js _ => jg e js
  | _ => fun _ => 0

theorem j2 (v : Nat) : jgAt 2 [v] = unitVal Ucmpi0.cells Ucmpi0.outs [v] := by
  rw [ucmpi0_fn]; rfl
theorem j13 (v : Nat) : jgAt 13 [v] = unitVal Ucmpi1.cells Ucmpi1.outs [v] := by
  rw [ucmpi1_fn]; rfl
theorem j104 (v : Nat) : jgAt 104 [v] = unitVal Ucmpi8.cells Ucmpi8.outs [v] := by
  rw [ucmpi8_fn]; rfl
theorem j118 (v : Nat) : jgAt 118 [v] = unitVal Ucmpi10.cells Ucmpi10.outs [v] := by
  rw [ucmpi10_fn]; rfl
theorem j26 (v w : Nat) : jgAt 26 [v, w] = unitVal Uori0.cells Uori0.outs [v, w] := by
  rw [uori0_fn]; rfl
theorem j46 (v w : Nat) : jgAt 46 [v, w] = unitVal Uori1.cells Uori1.outs [v, w] := by
  rw [uori1_fn]; rfl
theorem j27 (v w : Nat) : jgAt 27 [v, w] = unitVal Ucmpi2.cells Ucmpi2.outs [Ops.trunci 1 v, 0] := by
  rw [ucmpi2_fn]; rfl
theorem j47 (v : Nat) : jgAt 47 [v] = unitVal Ucmpi3.cells Ucmpi3.outs [Ops.trunci 1 v, 1] := by
  rw [ucmpi3_fn]; rfl
theorem j41 (v : Nat) : jgAt 41 [v] = unitVal Ushrsi0.cells Ushrsi0.outs [v, 1] := by
  rw [ushrsi0_fn]; rfl
theorem j43 (v : Nat) : jgAt 43 [v] = unitVal Ushrsi1.cells Ushrsi1.outs [v, 1] := by
  rw [ushrsi1_fn]; rfl
theorem j68 (v : Nat) : jgAt 68 [v] = unitVal Ushrsi2.cells Ushrsi2.outs [v, 1] := by
  rw [ushrsi2_fn]; rfl
theorem j89 (v : Nat) : jgAt 89 [v] = unitVal Ushrsi3.cells Ushrsi3.outs [v, 1] := by
  rw [ushrsi3_fn]; rfl
theorem j144 (v : Nat) : jgAt 144 [v] = unitVal Ushrsi4.cells Ushrsi4.outs [v, 1] := by
  rw [ushrsi4_fn]; rfl
theorem j45 (v : Nat) : jgAt 45 [v] = unitVal Uaddi0.cells Uaddi0.outs [v, 1] := by
  rw [uaddi0_fn]; rfl
theorem j66 (v w : Nat) :
    jgAt 66 [v, w] = unitVal Uori2.cells Uori2.outs [v, 1, Ops.trunci 1 w, 1] := by
  rw [uori2_fn]; rfl
theorem j87 (v w : Nat) :
    jgAt 87 [v, w] = unitVal Uori3.cells Uori3.outs [v, 1, Ops.trunci 1 w, 1] := by
  rw [uori3_fn]; rfl
theorem j142 (v w : Nat) :
    jgAt 142 [v, w] = unitVal Uori4.cells Uori4.outs [v, 1, Ops.trunci 1 w, 1] := by
  rw [uori4_fn]; rfl
theorem j135 (v w : Nat) : jgAt 135 [v, w] = unitVal Uselect1.cells Uselect1.outs [v, w] := by
  rw [uselect1_fn]; rfl
theorem j117 (v w : Nat) (hv : v < 2 ^ 32) (hw : w < 2 ^ 32) :
    jgAt 117 [v, w] = unitVal Uselect0.cells Uselect0.outs [v, w] := by
  rw [uselect0_fn]
  show Ops.select (Ops.cmpi .slt 32 v w) v w = _
  simp only [Ops.select, Ops.cmpi, Ops.b2n]
  by_cases h : Ops.flip 32 v < Ops.flip 32 w <;> simp [h, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hw]
theorem j162 (v w : Nat) (hw : w < 32) :
    jgAt 162 [v, w] = unitVal Ushli0.cells Ushli0.outs [v, w] := by
  rw [ushli0_fn v w hw]; rfl

/-- The 20 joins of gcd_hw, exactly. -/
theorem joins_listed : ((List.range ops.length).filter fun p =>
    match ops.getD p (K.sink 0) with | .join .. => true | _ => false) =
    [2, 13, 26, 27, 41, 43, 45, 46, 47, 66, 68, 87, 89, 104, 117, 118, 135, 142, 144, 162] := by
  decide

end Formal.Net.Compute.GcdJoin
