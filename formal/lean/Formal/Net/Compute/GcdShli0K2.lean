import Formal.Net.Compute.Shift
import Formal.Gen.Compute.GcdD.Ushli0

/-!
# H_COMPUTE_FN for gcd_hw's `ushli0`, shift amounts 16..23

Certificates `FixShOK` for `bdc_fused_ushli0` (bdc Verilog `z = e0 << e1`, a 412-cell barrel
shifter) with port `e1` fixed to each `k` in this range: each output bit's folded cone is checked
over its folded support (one kernel check per bit). Assembled in `GcdShli0.lean`.
-/

namespace Formal.Net.Compute.GcdD
open Formal.Net.Compute Formal.Net.GcdHw Formal.Gen.Compute.GcdD

abbrev ShlBit2 (k i : Nat) : Prop :=
  let w := Ushli0.outs.getD i .c0
  let S := dedup (afOf (fixK k) [] (coneW Ushli0.cells w) w).supp
  LocalOKF [] (coneW Ushli0.cells w) w S (fixK k)
      (fun l => match shlSrc k i with
        | some j => l.getD (S.idxOf (.inp 0 j)) false
        | none => false) ∧
    S.all (fun l => (fixK k l).isNone) = true ∧
    (match shlSrc k i with
     | some j => decide (Leaf.inp 0 j ∈ S)
     | none => true) = true

set_option maxRecDepth 100000 in
theorem shl_k16_b0 : ShlBit2 16 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b1 : ShlBit2 16 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b2 : ShlBit2 16 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b3 : ShlBit2 16 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b4 : ShlBit2 16 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b5 : ShlBit2 16 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b6 : ShlBit2 16 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b7 : ShlBit2 16 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b8 : ShlBit2 16 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b9 : ShlBit2 16 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b10 : ShlBit2 16 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b11 : ShlBit2 16 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b12 : ShlBit2 16 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b13 : ShlBit2 16 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b14 : ShlBit2 16 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b15 : ShlBit2 16 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b16 : ShlBit2 16 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b17 : ShlBit2 16 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b18 : ShlBit2 16 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b19 : ShlBit2 16 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b20 : ShlBit2 16 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b21 : ShlBit2 16 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b22 : ShlBit2 16 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b23 : ShlBit2 16 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b24 : ShlBit2 16 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b25 : ShlBit2 16 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b26 : ShlBit2 16 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b27 : ShlBit2 16 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b28 : ShlBit2 16 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b29 : ShlBit2 16 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b30 : ShlBit2 16 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k16_b31 : ShlBit2 16 31 := by decide +kernel

theorem ushli0_cert16 : FixShOK Ushli0.cells Ushli0.outs 16 (shlSrc 16) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k16_b0
  | 1, _ => exact shl_k16_b1
  | 2, _ => exact shl_k16_b2
  | 3, _ => exact shl_k16_b3
  | 4, _ => exact shl_k16_b4
  | 5, _ => exact shl_k16_b5
  | 6, _ => exact shl_k16_b6
  | 7, _ => exact shl_k16_b7
  | 8, _ => exact shl_k16_b8
  | 9, _ => exact shl_k16_b9
  | 10, _ => exact shl_k16_b10
  | 11, _ => exact shl_k16_b11
  | 12, _ => exact shl_k16_b12
  | 13, _ => exact shl_k16_b13
  | 14, _ => exact shl_k16_b14
  | 15, _ => exact shl_k16_b15
  | 16, _ => exact shl_k16_b16
  | 17, _ => exact shl_k16_b17
  | 18, _ => exact shl_k16_b18
  | 19, _ => exact shl_k16_b19
  | 20, _ => exact shl_k16_b20
  | 21, _ => exact shl_k16_b21
  | 22, _ => exact shl_k16_b22
  | 23, _ => exact shl_k16_b23
  | 24, _ => exact shl_k16_b24
  | 25, _ => exact shl_k16_b25
  | 26, _ => exact shl_k16_b26
  | 27, _ => exact shl_k16_b27
  | 28, _ => exact shl_k16_b28
  | 29, _ => exact shl_k16_b29
  | 30, _ => exact shl_k16_b30
  | 31, _ => exact shl_k16_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k17_b0 : ShlBit2 17 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b1 : ShlBit2 17 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b2 : ShlBit2 17 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b3 : ShlBit2 17 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b4 : ShlBit2 17 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b5 : ShlBit2 17 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b6 : ShlBit2 17 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b7 : ShlBit2 17 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b8 : ShlBit2 17 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b9 : ShlBit2 17 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b10 : ShlBit2 17 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b11 : ShlBit2 17 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b12 : ShlBit2 17 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b13 : ShlBit2 17 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b14 : ShlBit2 17 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b15 : ShlBit2 17 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b16 : ShlBit2 17 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b17 : ShlBit2 17 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b18 : ShlBit2 17 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b19 : ShlBit2 17 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b20 : ShlBit2 17 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b21 : ShlBit2 17 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b22 : ShlBit2 17 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b23 : ShlBit2 17 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b24 : ShlBit2 17 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b25 : ShlBit2 17 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b26 : ShlBit2 17 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b27 : ShlBit2 17 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b28 : ShlBit2 17 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b29 : ShlBit2 17 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b30 : ShlBit2 17 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k17_b31 : ShlBit2 17 31 := by decide +kernel

theorem ushli0_cert17 : FixShOK Ushli0.cells Ushli0.outs 17 (shlSrc 17) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k17_b0
  | 1, _ => exact shl_k17_b1
  | 2, _ => exact shl_k17_b2
  | 3, _ => exact shl_k17_b3
  | 4, _ => exact shl_k17_b4
  | 5, _ => exact shl_k17_b5
  | 6, _ => exact shl_k17_b6
  | 7, _ => exact shl_k17_b7
  | 8, _ => exact shl_k17_b8
  | 9, _ => exact shl_k17_b9
  | 10, _ => exact shl_k17_b10
  | 11, _ => exact shl_k17_b11
  | 12, _ => exact shl_k17_b12
  | 13, _ => exact shl_k17_b13
  | 14, _ => exact shl_k17_b14
  | 15, _ => exact shl_k17_b15
  | 16, _ => exact shl_k17_b16
  | 17, _ => exact shl_k17_b17
  | 18, _ => exact shl_k17_b18
  | 19, _ => exact shl_k17_b19
  | 20, _ => exact shl_k17_b20
  | 21, _ => exact shl_k17_b21
  | 22, _ => exact shl_k17_b22
  | 23, _ => exact shl_k17_b23
  | 24, _ => exact shl_k17_b24
  | 25, _ => exact shl_k17_b25
  | 26, _ => exact shl_k17_b26
  | 27, _ => exact shl_k17_b27
  | 28, _ => exact shl_k17_b28
  | 29, _ => exact shl_k17_b29
  | 30, _ => exact shl_k17_b30
  | 31, _ => exact shl_k17_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k18_b0 : ShlBit2 18 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b1 : ShlBit2 18 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b2 : ShlBit2 18 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b3 : ShlBit2 18 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b4 : ShlBit2 18 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b5 : ShlBit2 18 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b6 : ShlBit2 18 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b7 : ShlBit2 18 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b8 : ShlBit2 18 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b9 : ShlBit2 18 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b10 : ShlBit2 18 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b11 : ShlBit2 18 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b12 : ShlBit2 18 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b13 : ShlBit2 18 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b14 : ShlBit2 18 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b15 : ShlBit2 18 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b16 : ShlBit2 18 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b17 : ShlBit2 18 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b18 : ShlBit2 18 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b19 : ShlBit2 18 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b20 : ShlBit2 18 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b21 : ShlBit2 18 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b22 : ShlBit2 18 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b23 : ShlBit2 18 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b24 : ShlBit2 18 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b25 : ShlBit2 18 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b26 : ShlBit2 18 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b27 : ShlBit2 18 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b28 : ShlBit2 18 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b29 : ShlBit2 18 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b30 : ShlBit2 18 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k18_b31 : ShlBit2 18 31 := by decide +kernel

theorem ushli0_cert18 : FixShOK Ushli0.cells Ushli0.outs 18 (shlSrc 18) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k18_b0
  | 1, _ => exact shl_k18_b1
  | 2, _ => exact shl_k18_b2
  | 3, _ => exact shl_k18_b3
  | 4, _ => exact shl_k18_b4
  | 5, _ => exact shl_k18_b5
  | 6, _ => exact shl_k18_b6
  | 7, _ => exact shl_k18_b7
  | 8, _ => exact shl_k18_b8
  | 9, _ => exact shl_k18_b9
  | 10, _ => exact shl_k18_b10
  | 11, _ => exact shl_k18_b11
  | 12, _ => exact shl_k18_b12
  | 13, _ => exact shl_k18_b13
  | 14, _ => exact shl_k18_b14
  | 15, _ => exact shl_k18_b15
  | 16, _ => exact shl_k18_b16
  | 17, _ => exact shl_k18_b17
  | 18, _ => exact shl_k18_b18
  | 19, _ => exact shl_k18_b19
  | 20, _ => exact shl_k18_b20
  | 21, _ => exact shl_k18_b21
  | 22, _ => exact shl_k18_b22
  | 23, _ => exact shl_k18_b23
  | 24, _ => exact shl_k18_b24
  | 25, _ => exact shl_k18_b25
  | 26, _ => exact shl_k18_b26
  | 27, _ => exact shl_k18_b27
  | 28, _ => exact shl_k18_b28
  | 29, _ => exact shl_k18_b29
  | 30, _ => exact shl_k18_b30
  | 31, _ => exact shl_k18_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k19_b0 : ShlBit2 19 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b1 : ShlBit2 19 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b2 : ShlBit2 19 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b3 : ShlBit2 19 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b4 : ShlBit2 19 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b5 : ShlBit2 19 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b6 : ShlBit2 19 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b7 : ShlBit2 19 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b8 : ShlBit2 19 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b9 : ShlBit2 19 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b10 : ShlBit2 19 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b11 : ShlBit2 19 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b12 : ShlBit2 19 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b13 : ShlBit2 19 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b14 : ShlBit2 19 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b15 : ShlBit2 19 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b16 : ShlBit2 19 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b17 : ShlBit2 19 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b18 : ShlBit2 19 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b19 : ShlBit2 19 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b20 : ShlBit2 19 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b21 : ShlBit2 19 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b22 : ShlBit2 19 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b23 : ShlBit2 19 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b24 : ShlBit2 19 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b25 : ShlBit2 19 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b26 : ShlBit2 19 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b27 : ShlBit2 19 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b28 : ShlBit2 19 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b29 : ShlBit2 19 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b30 : ShlBit2 19 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k19_b31 : ShlBit2 19 31 := by decide +kernel

theorem ushli0_cert19 : FixShOK Ushli0.cells Ushli0.outs 19 (shlSrc 19) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k19_b0
  | 1, _ => exact shl_k19_b1
  | 2, _ => exact shl_k19_b2
  | 3, _ => exact shl_k19_b3
  | 4, _ => exact shl_k19_b4
  | 5, _ => exact shl_k19_b5
  | 6, _ => exact shl_k19_b6
  | 7, _ => exact shl_k19_b7
  | 8, _ => exact shl_k19_b8
  | 9, _ => exact shl_k19_b9
  | 10, _ => exact shl_k19_b10
  | 11, _ => exact shl_k19_b11
  | 12, _ => exact shl_k19_b12
  | 13, _ => exact shl_k19_b13
  | 14, _ => exact shl_k19_b14
  | 15, _ => exact shl_k19_b15
  | 16, _ => exact shl_k19_b16
  | 17, _ => exact shl_k19_b17
  | 18, _ => exact shl_k19_b18
  | 19, _ => exact shl_k19_b19
  | 20, _ => exact shl_k19_b20
  | 21, _ => exact shl_k19_b21
  | 22, _ => exact shl_k19_b22
  | 23, _ => exact shl_k19_b23
  | 24, _ => exact shl_k19_b24
  | 25, _ => exact shl_k19_b25
  | 26, _ => exact shl_k19_b26
  | 27, _ => exact shl_k19_b27
  | 28, _ => exact shl_k19_b28
  | 29, _ => exact shl_k19_b29
  | 30, _ => exact shl_k19_b30
  | 31, _ => exact shl_k19_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k20_b0 : ShlBit2 20 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b1 : ShlBit2 20 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b2 : ShlBit2 20 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b3 : ShlBit2 20 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b4 : ShlBit2 20 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b5 : ShlBit2 20 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b6 : ShlBit2 20 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b7 : ShlBit2 20 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b8 : ShlBit2 20 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b9 : ShlBit2 20 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b10 : ShlBit2 20 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b11 : ShlBit2 20 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b12 : ShlBit2 20 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b13 : ShlBit2 20 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b14 : ShlBit2 20 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b15 : ShlBit2 20 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b16 : ShlBit2 20 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b17 : ShlBit2 20 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b18 : ShlBit2 20 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b19 : ShlBit2 20 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b20 : ShlBit2 20 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b21 : ShlBit2 20 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b22 : ShlBit2 20 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b23 : ShlBit2 20 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b24 : ShlBit2 20 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b25 : ShlBit2 20 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b26 : ShlBit2 20 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b27 : ShlBit2 20 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b28 : ShlBit2 20 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b29 : ShlBit2 20 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b30 : ShlBit2 20 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k20_b31 : ShlBit2 20 31 := by decide +kernel

theorem ushli0_cert20 : FixShOK Ushli0.cells Ushli0.outs 20 (shlSrc 20) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k20_b0
  | 1, _ => exact shl_k20_b1
  | 2, _ => exact shl_k20_b2
  | 3, _ => exact shl_k20_b3
  | 4, _ => exact shl_k20_b4
  | 5, _ => exact shl_k20_b5
  | 6, _ => exact shl_k20_b6
  | 7, _ => exact shl_k20_b7
  | 8, _ => exact shl_k20_b8
  | 9, _ => exact shl_k20_b9
  | 10, _ => exact shl_k20_b10
  | 11, _ => exact shl_k20_b11
  | 12, _ => exact shl_k20_b12
  | 13, _ => exact shl_k20_b13
  | 14, _ => exact shl_k20_b14
  | 15, _ => exact shl_k20_b15
  | 16, _ => exact shl_k20_b16
  | 17, _ => exact shl_k20_b17
  | 18, _ => exact shl_k20_b18
  | 19, _ => exact shl_k20_b19
  | 20, _ => exact shl_k20_b20
  | 21, _ => exact shl_k20_b21
  | 22, _ => exact shl_k20_b22
  | 23, _ => exact shl_k20_b23
  | 24, _ => exact shl_k20_b24
  | 25, _ => exact shl_k20_b25
  | 26, _ => exact shl_k20_b26
  | 27, _ => exact shl_k20_b27
  | 28, _ => exact shl_k20_b28
  | 29, _ => exact shl_k20_b29
  | 30, _ => exact shl_k20_b30
  | 31, _ => exact shl_k20_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k21_b0 : ShlBit2 21 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b1 : ShlBit2 21 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b2 : ShlBit2 21 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b3 : ShlBit2 21 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b4 : ShlBit2 21 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b5 : ShlBit2 21 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b6 : ShlBit2 21 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b7 : ShlBit2 21 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b8 : ShlBit2 21 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b9 : ShlBit2 21 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b10 : ShlBit2 21 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b11 : ShlBit2 21 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b12 : ShlBit2 21 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b13 : ShlBit2 21 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b14 : ShlBit2 21 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b15 : ShlBit2 21 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b16 : ShlBit2 21 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b17 : ShlBit2 21 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b18 : ShlBit2 21 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b19 : ShlBit2 21 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b20 : ShlBit2 21 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b21 : ShlBit2 21 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b22 : ShlBit2 21 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b23 : ShlBit2 21 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b24 : ShlBit2 21 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b25 : ShlBit2 21 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b26 : ShlBit2 21 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b27 : ShlBit2 21 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b28 : ShlBit2 21 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b29 : ShlBit2 21 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b30 : ShlBit2 21 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k21_b31 : ShlBit2 21 31 := by decide +kernel

theorem ushli0_cert21 : FixShOK Ushli0.cells Ushli0.outs 21 (shlSrc 21) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k21_b0
  | 1, _ => exact shl_k21_b1
  | 2, _ => exact shl_k21_b2
  | 3, _ => exact shl_k21_b3
  | 4, _ => exact shl_k21_b4
  | 5, _ => exact shl_k21_b5
  | 6, _ => exact shl_k21_b6
  | 7, _ => exact shl_k21_b7
  | 8, _ => exact shl_k21_b8
  | 9, _ => exact shl_k21_b9
  | 10, _ => exact shl_k21_b10
  | 11, _ => exact shl_k21_b11
  | 12, _ => exact shl_k21_b12
  | 13, _ => exact shl_k21_b13
  | 14, _ => exact shl_k21_b14
  | 15, _ => exact shl_k21_b15
  | 16, _ => exact shl_k21_b16
  | 17, _ => exact shl_k21_b17
  | 18, _ => exact shl_k21_b18
  | 19, _ => exact shl_k21_b19
  | 20, _ => exact shl_k21_b20
  | 21, _ => exact shl_k21_b21
  | 22, _ => exact shl_k21_b22
  | 23, _ => exact shl_k21_b23
  | 24, _ => exact shl_k21_b24
  | 25, _ => exact shl_k21_b25
  | 26, _ => exact shl_k21_b26
  | 27, _ => exact shl_k21_b27
  | 28, _ => exact shl_k21_b28
  | 29, _ => exact shl_k21_b29
  | 30, _ => exact shl_k21_b30
  | 31, _ => exact shl_k21_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k22_b0 : ShlBit2 22 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b1 : ShlBit2 22 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b2 : ShlBit2 22 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b3 : ShlBit2 22 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b4 : ShlBit2 22 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b5 : ShlBit2 22 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b6 : ShlBit2 22 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b7 : ShlBit2 22 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b8 : ShlBit2 22 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b9 : ShlBit2 22 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b10 : ShlBit2 22 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b11 : ShlBit2 22 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b12 : ShlBit2 22 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b13 : ShlBit2 22 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b14 : ShlBit2 22 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b15 : ShlBit2 22 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b16 : ShlBit2 22 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b17 : ShlBit2 22 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b18 : ShlBit2 22 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b19 : ShlBit2 22 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b20 : ShlBit2 22 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b21 : ShlBit2 22 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b22 : ShlBit2 22 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b23 : ShlBit2 22 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b24 : ShlBit2 22 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b25 : ShlBit2 22 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b26 : ShlBit2 22 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b27 : ShlBit2 22 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b28 : ShlBit2 22 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b29 : ShlBit2 22 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b30 : ShlBit2 22 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k22_b31 : ShlBit2 22 31 := by decide +kernel

theorem ushli0_cert22 : FixShOK Ushli0.cells Ushli0.outs 22 (shlSrc 22) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k22_b0
  | 1, _ => exact shl_k22_b1
  | 2, _ => exact shl_k22_b2
  | 3, _ => exact shl_k22_b3
  | 4, _ => exact shl_k22_b4
  | 5, _ => exact shl_k22_b5
  | 6, _ => exact shl_k22_b6
  | 7, _ => exact shl_k22_b7
  | 8, _ => exact shl_k22_b8
  | 9, _ => exact shl_k22_b9
  | 10, _ => exact shl_k22_b10
  | 11, _ => exact shl_k22_b11
  | 12, _ => exact shl_k22_b12
  | 13, _ => exact shl_k22_b13
  | 14, _ => exact shl_k22_b14
  | 15, _ => exact shl_k22_b15
  | 16, _ => exact shl_k22_b16
  | 17, _ => exact shl_k22_b17
  | 18, _ => exact shl_k22_b18
  | 19, _ => exact shl_k22_b19
  | 20, _ => exact shl_k22_b20
  | 21, _ => exact shl_k22_b21
  | 22, _ => exact shl_k22_b22
  | 23, _ => exact shl_k22_b23
  | 24, _ => exact shl_k22_b24
  | 25, _ => exact shl_k22_b25
  | 26, _ => exact shl_k22_b26
  | 27, _ => exact shl_k22_b27
  | 28, _ => exact shl_k22_b28
  | 29, _ => exact shl_k22_b29
  | 30, _ => exact shl_k22_b30
  | 31, _ => exact shl_k22_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k23_b0 : ShlBit2 23 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b1 : ShlBit2 23 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b2 : ShlBit2 23 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b3 : ShlBit2 23 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b4 : ShlBit2 23 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b5 : ShlBit2 23 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b6 : ShlBit2 23 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b7 : ShlBit2 23 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b8 : ShlBit2 23 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b9 : ShlBit2 23 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b10 : ShlBit2 23 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b11 : ShlBit2 23 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b12 : ShlBit2 23 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b13 : ShlBit2 23 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b14 : ShlBit2 23 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b15 : ShlBit2 23 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b16 : ShlBit2 23 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b17 : ShlBit2 23 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b18 : ShlBit2 23 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b19 : ShlBit2 23 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b20 : ShlBit2 23 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b21 : ShlBit2 23 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b22 : ShlBit2 23 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b23 : ShlBit2 23 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b24 : ShlBit2 23 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b25 : ShlBit2 23 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b26 : ShlBit2 23 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b27 : ShlBit2 23 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b28 : ShlBit2 23 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b29 : ShlBit2 23 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b30 : ShlBit2 23 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k23_b31 : ShlBit2 23 31 := by decide +kernel

theorem ushli0_cert23 : FixShOK Ushli0.cells Ushli0.outs 23 (shlSrc 23) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k23_b0
  | 1, _ => exact shl_k23_b1
  | 2, _ => exact shl_k23_b2
  | 3, _ => exact shl_k23_b3
  | 4, _ => exact shl_k23_b4
  | 5, _ => exact shl_k23_b5
  | 6, _ => exact shl_k23_b6
  | 7, _ => exact shl_k23_b7
  | 8, _ => exact shl_k23_b8
  | 9, _ => exact shl_k23_b9
  | 10, _ => exact shl_k23_b10
  | 11, _ => exact shl_k23_b11
  | 12, _ => exact shl_k23_b12
  | 13, _ => exact shl_k23_b13
  | 14, _ => exact shl_k23_b14
  | 15, _ => exact shl_k23_b15
  | 16, _ => exact shl_k23_b16
  | 17, _ => exact shl_k23_b17
  | 18, _ => exact shl_k23_b18
  | 19, _ => exact shl_k23_b19
  | 20, _ => exact shl_k23_b20
  | 21, _ => exact shl_k23_b21
  | 22, _ => exact shl_k23_b22
  | 23, _ => exact shl_k23_b23
  | 24, _ => exact shl_k23_b24
  | 25, _ => exact shl_k23_b25
  | 26, _ => exact shl_k23_b26
  | 27, _ => exact shl_k23_b27
  | 28, _ => exact shl_k23_b28
  | 29, _ => exact shl_k23_b29
  | 30, _ => exact shl_k23_b30
  | 31, _ => exact shl_k23_b31
  | _ + 32, h => exact absurd h (by omega)

end Formal.Net.Compute.GcdD
