import Formal.Net.Compute.Shift
import Formal.Gen.Compute.GcdD.Ushli0

/-!
# H_COMPUTE_FN for gcd_hw's `ushli0`, shift amounts 24..31

Certificates `FixShOK` for `bdc_fused_ushli0` (bdc Verilog `z = e0 << e1`, a 412-cell barrel
shifter) with port `e1` fixed to each `k` in this range: each output bit's folded cone is checked
over its folded support (one kernel check per bit). Assembled in `GcdShli0.lean`.
-/

namespace Formal.Net.Compute.GcdD
open Formal.Net.Compute Formal.Net.GcdHw Formal.Gen.Compute.GcdD

abbrev ShlBit3 (k i : Nat) : Prop :=
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
theorem shl_k24_b0 : ShlBit3 24 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b1 : ShlBit3 24 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b2 : ShlBit3 24 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b3 : ShlBit3 24 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b4 : ShlBit3 24 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b5 : ShlBit3 24 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b6 : ShlBit3 24 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b7 : ShlBit3 24 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b8 : ShlBit3 24 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b9 : ShlBit3 24 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b10 : ShlBit3 24 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b11 : ShlBit3 24 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b12 : ShlBit3 24 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b13 : ShlBit3 24 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b14 : ShlBit3 24 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b15 : ShlBit3 24 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b16 : ShlBit3 24 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b17 : ShlBit3 24 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b18 : ShlBit3 24 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b19 : ShlBit3 24 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b20 : ShlBit3 24 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b21 : ShlBit3 24 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b22 : ShlBit3 24 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b23 : ShlBit3 24 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b24 : ShlBit3 24 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b25 : ShlBit3 24 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b26 : ShlBit3 24 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b27 : ShlBit3 24 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b28 : ShlBit3 24 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b29 : ShlBit3 24 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b30 : ShlBit3 24 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k24_b31 : ShlBit3 24 31 := by decide +kernel

theorem ushli0_cert24 : FixShOK Ushli0.cells Ushli0.outs 24 (shlSrc 24) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k24_b0
  | 1, _ => exact shl_k24_b1
  | 2, _ => exact shl_k24_b2
  | 3, _ => exact shl_k24_b3
  | 4, _ => exact shl_k24_b4
  | 5, _ => exact shl_k24_b5
  | 6, _ => exact shl_k24_b6
  | 7, _ => exact shl_k24_b7
  | 8, _ => exact shl_k24_b8
  | 9, _ => exact shl_k24_b9
  | 10, _ => exact shl_k24_b10
  | 11, _ => exact shl_k24_b11
  | 12, _ => exact shl_k24_b12
  | 13, _ => exact shl_k24_b13
  | 14, _ => exact shl_k24_b14
  | 15, _ => exact shl_k24_b15
  | 16, _ => exact shl_k24_b16
  | 17, _ => exact shl_k24_b17
  | 18, _ => exact shl_k24_b18
  | 19, _ => exact shl_k24_b19
  | 20, _ => exact shl_k24_b20
  | 21, _ => exact shl_k24_b21
  | 22, _ => exact shl_k24_b22
  | 23, _ => exact shl_k24_b23
  | 24, _ => exact shl_k24_b24
  | 25, _ => exact shl_k24_b25
  | 26, _ => exact shl_k24_b26
  | 27, _ => exact shl_k24_b27
  | 28, _ => exact shl_k24_b28
  | 29, _ => exact shl_k24_b29
  | 30, _ => exact shl_k24_b30
  | 31, _ => exact shl_k24_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k25_b0 : ShlBit3 25 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b1 : ShlBit3 25 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b2 : ShlBit3 25 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b3 : ShlBit3 25 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b4 : ShlBit3 25 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b5 : ShlBit3 25 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b6 : ShlBit3 25 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b7 : ShlBit3 25 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b8 : ShlBit3 25 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b9 : ShlBit3 25 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b10 : ShlBit3 25 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b11 : ShlBit3 25 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b12 : ShlBit3 25 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b13 : ShlBit3 25 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b14 : ShlBit3 25 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b15 : ShlBit3 25 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b16 : ShlBit3 25 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b17 : ShlBit3 25 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b18 : ShlBit3 25 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b19 : ShlBit3 25 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b20 : ShlBit3 25 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b21 : ShlBit3 25 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b22 : ShlBit3 25 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b23 : ShlBit3 25 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b24 : ShlBit3 25 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b25 : ShlBit3 25 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b26 : ShlBit3 25 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b27 : ShlBit3 25 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b28 : ShlBit3 25 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b29 : ShlBit3 25 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b30 : ShlBit3 25 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k25_b31 : ShlBit3 25 31 := by decide +kernel

theorem ushli0_cert25 : FixShOK Ushli0.cells Ushli0.outs 25 (shlSrc 25) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k25_b0
  | 1, _ => exact shl_k25_b1
  | 2, _ => exact shl_k25_b2
  | 3, _ => exact shl_k25_b3
  | 4, _ => exact shl_k25_b4
  | 5, _ => exact shl_k25_b5
  | 6, _ => exact shl_k25_b6
  | 7, _ => exact shl_k25_b7
  | 8, _ => exact shl_k25_b8
  | 9, _ => exact shl_k25_b9
  | 10, _ => exact shl_k25_b10
  | 11, _ => exact shl_k25_b11
  | 12, _ => exact shl_k25_b12
  | 13, _ => exact shl_k25_b13
  | 14, _ => exact shl_k25_b14
  | 15, _ => exact shl_k25_b15
  | 16, _ => exact shl_k25_b16
  | 17, _ => exact shl_k25_b17
  | 18, _ => exact shl_k25_b18
  | 19, _ => exact shl_k25_b19
  | 20, _ => exact shl_k25_b20
  | 21, _ => exact shl_k25_b21
  | 22, _ => exact shl_k25_b22
  | 23, _ => exact shl_k25_b23
  | 24, _ => exact shl_k25_b24
  | 25, _ => exact shl_k25_b25
  | 26, _ => exact shl_k25_b26
  | 27, _ => exact shl_k25_b27
  | 28, _ => exact shl_k25_b28
  | 29, _ => exact shl_k25_b29
  | 30, _ => exact shl_k25_b30
  | 31, _ => exact shl_k25_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k26_b0 : ShlBit3 26 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b1 : ShlBit3 26 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b2 : ShlBit3 26 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b3 : ShlBit3 26 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b4 : ShlBit3 26 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b5 : ShlBit3 26 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b6 : ShlBit3 26 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b7 : ShlBit3 26 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b8 : ShlBit3 26 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b9 : ShlBit3 26 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b10 : ShlBit3 26 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b11 : ShlBit3 26 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b12 : ShlBit3 26 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b13 : ShlBit3 26 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b14 : ShlBit3 26 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b15 : ShlBit3 26 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b16 : ShlBit3 26 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b17 : ShlBit3 26 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b18 : ShlBit3 26 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b19 : ShlBit3 26 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b20 : ShlBit3 26 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b21 : ShlBit3 26 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b22 : ShlBit3 26 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b23 : ShlBit3 26 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b24 : ShlBit3 26 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b25 : ShlBit3 26 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b26 : ShlBit3 26 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b27 : ShlBit3 26 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b28 : ShlBit3 26 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b29 : ShlBit3 26 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b30 : ShlBit3 26 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k26_b31 : ShlBit3 26 31 := by decide +kernel

theorem ushli0_cert26 : FixShOK Ushli0.cells Ushli0.outs 26 (shlSrc 26) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k26_b0
  | 1, _ => exact shl_k26_b1
  | 2, _ => exact shl_k26_b2
  | 3, _ => exact shl_k26_b3
  | 4, _ => exact shl_k26_b4
  | 5, _ => exact shl_k26_b5
  | 6, _ => exact shl_k26_b6
  | 7, _ => exact shl_k26_b7
  | 8, _ => exact shl_k26_b8
  | 9, _ => exact shl_k26_b9
  | 10, _ => exact shl_k26_b10
  | 11, _ => exact shl_k26_b11
  | 12, _ => exact shl_k26_b12
  | 13, _ => exact shl_k26_b13
  | 14, _ => exact shl_k26_b14
  | 15, _ => exact shl_k26_b15
  | 16, _ => exact shl_k26_b16
  | 17, _ => exact shl_k26_b17
  | 18, _ => exact shl_k26_b18
  | 19, _ => exact shl_k26_b19
  | 20, _ => exact shl_k26_b20
  | 21, _ => exact shl_k26_b21
  | 22, _ => exact shl_k26_b22
  | 23, _ => exact shl_k26_b23
  | 24, _ => exact shl_k26_b24
  | 25, _ => exact shl_k26_b25
  | 26, _ => exact shl_k26_b26
  | 27, _ => exact shl_k26_b27
  | 28, _ => exact shl_k26_b28
  | 29, _ => exact shl_k26_b29
  | 30, _ => exact shl_k26_b30
  | 31, _ => exact shl_k26_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k27_b0 : ShlBit3 27 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b1 : ShlBit3 27 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b2 : ShlBit3 27 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b3 : ShlBit3 27 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b4 : ShlBit3 27 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b5 : ShlBit3 27 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b6 : ShlBit3 27 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b7 : ShlBit3 27 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b8 : ShlBit3 27 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b9 : ShlBit3 27 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b10 : ShlBit3 27 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b11 : ShlBit3 27 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b12 : ShlBit3 27 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b13 : ShlBit3 27 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b14 : ShlBit3 27 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b15 : ShlBit3 27 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b16 : ShlBit3 27 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b17 : ShlBit3 27 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b18 : ShlBit3 27 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b19 : ShlBit3 27 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b20 : ShlBit3 27 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b21 : ShlBit3 27 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b22 : ShlBit3 27 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b23 : ShlBit3 27 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b24 : ShlBit3 27 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b25 : ShlBit3 27 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b26 : ShlBit3 27 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b27 : ShlBit3 27 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b28 : ShlBit3 27 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b29 : ShlBit3 27 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b30 : ShlBit3 27 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k27_b31 : ShlBit3 27 31 := by decide +kernel

theorem ushli0_cert27 : FixShOK Ushli0.cells Ushli0.outs 27 (shlSrc 27) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k27_b0
  | 1, _ => exact shl_k27_b1
  | 2, _ => exact shl_k27_b2
  | 3, _ => exact shl_k27_b3
  | 4, _ => exact shl_k27_b4
  | 5, _ => exact shl_k27_b5
  | 6, _ => exact shl_k27_b6
  | 7, _ => exact shl_k27_b7
  | 8, _ => exact shl_k27_b8
  | 9, _ => exact shl_k27_b9
  | 10, _ => exact shl_k27_b10
  | 11, _ => exact shl_k27_b11
  | 12, _ => exact shl_k27_b12
  | 13, _ => exact shl_k27_b13
  | 14, _ => exact shl_k27_b14
  | 15, _ => exact shl_k27_b15
  | 16, _ => exact shl_k27_b16
  | 17, _ => exact shl_k27_b17
  | 18, _ => exact shl_k27_b18
  | 19, _ => exact shl_k27_b19
  | 20, _ => exact shl_k27_b20
  | 21, _ => exact shl_k27_b21
  | 22, _ => exact shl_k27_b22
  | 23, _ => exact shl_k27_b23
  | 24, _ => exact shl_k27_b24
  | 25, _ => exact shl_k27_b25
  | 26, _ => exact shl_k27_b26
  | 27, _ => exact shl_k27_b27
  | 28, _ => exact shl_k27_b28
  | 29, _ => exact shl_k27_b29
  | 30, _ => exact shl_k27_b30
  | 31, _ => exact shl_k27_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k28_b0 : ShlBit3 28 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b1 : ShlBit3 28 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b2 : ShlBit3 28 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b3 : ShlBit3 28 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b4 : ShlBit3 28 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b5 : ShlBit3 28 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b6 : ShlBit3 28 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b7 : ShlBit3 28 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b8 : ShlBit3 28 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b9 : ShlBit3 28 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b10 : ShlBit3 28 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b11 : ShlBit3 28 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b12 : ShlBit3 28 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b13 : ShlBit3 28 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b14 : ShlBit3 28 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b15 : ShlBit3 28 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b16 : ShlBit3 28 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b17 : ShlBit3 28 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b18 : ShlBit3 28 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b19 : ShlBit3 28 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b20 : ShlBit3 28 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b21 : ShlBit3 28 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b22 : ShlBit3 28 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b23 : ShlBit3 28 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b24 : ShlBit3 28 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b25 : ShlBit3 28 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b26 : ShlBit3 28 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b27 : ShlBit3 28 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b28 : ShlBit3 28 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b29 : ShlBit3 28 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b30 : ShlBit3 28 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k28_b31 : ShlBit3 28 31 := by decide +kernel

theorem ushli0_cert28 : FixShOK Ushli0.cells Ushli0.outs 28 (shlSrc 28) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k28_b0
  | 1, _ => exact shl_k28_b1
  | 2, _ => exact shl_k28_b2
  | 3, _ => exact shl_k28_b3
  | 4, _ => exact shl_k28_b4
  | 5, _ => exact shl_k28_b5
  | 6, _ => exact shl_k28_b6
  | 7, _ => exact shl_k28_b7
  | 8, _ => exact shl_k28_b8
  | 9, _ => exact shl_k28_b9
  | 10, _ => exact shl_k28_b10
  | 11, _ => exact shl_k28_b11
  | 12, _ => exact shl_k28_b12
  | 13, _ => exact shl_k28_b13
  | 14, _ => exact shl_k28_b14
  | 15, _ => exact shl_k28_b15
  | 16, _ => exact shl_k28_b16
  | 17, _ => exact shl_k28_b17
  | 18, _ => exact shl_k28_b18
  | 19, _ => exact shl_k28_b19
  | 20, _ => exact shl_k28_b20
  | 21, _ => exact shl_k28_b21
  | 22, _ => exact shl_k28_b22
  | 23, _ => exact shl_k28_b23
  | 24, _ => exact shl_k28_b24
  | 25, _ => exact shl_k28_b25
  | 26, _ => exact shl_k28_b26
  | 27, _ => exact shl_k28_b27
  | 28, _ => exact shl_k28_b28
  | 29, _ => exact shl_k28_b29
  | 30, _ => exact shl_k28_b30
  | 31, _ => exact shl_k28_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k29_b0 : ShlBit3 29 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b1 : ShlBit3 29 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b2 : ShlBit3 29 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b3 : ShlBit3 29 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b4 : ShlBit3 29 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b5 : ShlBit3 29 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b6 : ShlBit3 29 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b7 : ShlBit3 29 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b8 : ShlBit3 29 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b9 : ShlBit3 29 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b10 : ShlBit3 29 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b11 : ShlBit3 29 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b12 : ShlBit3 29 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b13 : ShlBit3 29 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b14 : ShlBit3 29 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b15 : ShlBit3 29 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b16 : ShlBit3 29 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b17 : ShlBit3 29 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b18 : ShlBit3 29 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b19 : ShlBit3 29 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b20 : ShlBit3 29 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b21 : ShlBit3 29 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b22 : ShlBit3 29 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b23 : ShlBit3 29 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b24 : ShlBit3 29 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b25 : ShlBit3 29 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b26 : ShlBit3 29 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b27 : ShlBit3 29 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b28 : ShlBit3 29 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b29 : ShlBit3 29 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b30 : ShlBit3 29 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k29_b31 : ShlBit3 29 31 := by decide +kernel

theorem ushli0_cert29 : FixShOK Ushli0.cells Ushli0.outs 29 (shlSrc 29) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k29_b0
  | 1, _ => exact shl_k29_b1
  | 2, _ => exact shl_k29_b2
  | 3, _ => exact shl_k29_b3
  | 4, _ => exact shl_k29_b4
  | 5, _ => exact shl_k29_b5
  | 6, _ => exact shl_k29_b6
  | 7, _ => exact shl_k29_b7
  | 8, _ => exact shl_k29_b8
  | 9, _ => exact shl_k29_b9
  | 10, _ => exact shl_k29_b10
  | 11, _ => exact shl_k29_b11
  | 12, _ => exact shl_k29_b12
  | 13, _ => exact shl_k29_b13
  | 14, _ => exact shl_k29_b14
  | 15, _ => exact shl_k29_b15
  | 16, _ => exact shl_k29_b16
  | 17, _ => exact shl_k29_b17
  | 18, _ => exact shl_k29_b18
  | 19, _ => exact shl_k29_b19
  | 20, _ => exact shl_k29_b20
  | 21, _ => exact shl_k29_b21
  | 22, _ => exact shl_k29_b22
  | 23, _ => exact shl_k29_b23
  | 24, _ => exact shl_k29_b24
  | 25, _ => exact shl_k29_b25
  | 26, _ => exact shl_k29_b26
  | 27, _ => exact shl_k29_b27
  | 28, _ => exact shl_k29_b28
  | 29, _ => exact shl_k29_b29
  | 30, _ => exact shl_k29_b30
  | 31, _ => exact shl_k29_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k30_b0 : ShlBit3 30 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b1 : ShlBit3 30 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b2 : ShlBit3 30 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b3 : ShlBit3 30 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b4 : ShlBit3 30 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b5 : ShlBit3 30 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b6 : ShlBit3 30 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b7 : ShlBit3 30 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b8 : ShlBit3 30 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b9 : ShlBit3 30 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b10 : ShlBit3 30 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b11 : ShlBit3 30 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b12 : ShlBit3 30 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b13 : ShlBit3 30 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b14 : ShlBit3 30 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b15 : ShlBit3 30 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b16 : ShlBit3 30 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b17 : ShlBit3 30 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b18 : ShlBit3 30 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b19 : ShlBit3 30 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b20 : ShlBit3 30 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b21 : ShlBit3 30 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b22 : ShlBit3 30 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b23 : ShlBit3 30 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b24 : ShlBit3 30 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b25 : ShlBit3 30 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b26 : ShlBit3 30 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b27 : ShlBit3 30 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b28 : ShlBit3 30 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b29 : ShlBit3 30 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b30 : ShlBit3 30 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k30_b31 : ShlBit3 30 31 := by decide +kernel

theorem ushli0_cert30 : FixShOK Ushli0.cells Ushli0.outs 30 (shlSrc 30) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k30_b0
  | 1, _ => exact shl_k30_b1
  | 2, _ => exact shl_k30_b2
  | 3, _ => exact shl_k30_b3
  | 4, _ => exact shl_k30_b4
  | 5, _ => exact shl_k30_b5
  | 6, _ => exact shl_k30_b6
  | 7, _ => exact shl_k30_b7
  | 8, _ => exact shl_k30_b8
  | 9, _ => exact shl_k30_b9
  | 10, _ => exact shl_k30_b10
  | 11, _ => exact shl_k30_b11
  | 12, _ => exact shl_k30_b12
  | 13, _ => exact shl_k30_b13
  | 14, _ => exact shl_k30_b14
  | 15, _ => exact shl_k30_b15
  | 16, _ => exact shl_k30_b16
  | 17, _ => exact shl_k30_b17
  | 18, _ => exact shl_k30_b18
  | 19, _ => exact shl_k30_b19
  | 20, _ => exact shl_k30_b20
  | 21, _ => exact shl_k30_b21
  | 22, _ => exact shl_k30_b22
  | 23, _ => exact shl_k30_b23
  | 24, _ => exact shl_k30_b24
  | 25, _ => exact shl_k30_b25
  | 26, _ => exact shl_k30_b26
  | 27, _ => exact shl_k30_b27
  | 28, _ => exact shl_k30_b28
  | 29, _ => exact shl_k30_b29
  | 30, _ => exact shl_k30_b30
  | 31, _ => exact shl_k30_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k31_b0 : ShlBit3 31 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b1 : ShlBit3 31 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b2 : ShlBit3 31 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b3 : ShlBit3 31 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b4 : ShlBit3 31 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b5 : ShlBit3 31 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b6 : ShlBit3 31 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b7 : ShlBit3 31 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b8 : ShlBit3 31 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b9 : ShlBit3 31 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b10 : ShlBit3 31 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b11 : ShlBit3 31 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b12 : ShlBit3 31 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b13 : ShlBit3 31 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b14 : ShlBit3 31 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b15 : ShlBit3 31 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b16 : ShlBit3 31 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b17 : ShlBit3 31 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b18 : ShlBit3 31 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b19 : ShlBit3 31 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b20 : ShlBit3 31 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b21 : ShlBit3 31 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b22 : ShlBit3 31 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b23 : ShlBit3 31 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b24 : ShlBit3 31 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b25 : ShlBit3 31 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b26 : ShlBit3 31 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b27 : ShlBit3 31 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b28 : ShlBit3 31 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b29 : ShlBit3 31 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b30 : ShlBit3 31 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k31_b31 : ShlBit3 31 31 := by decide +kernel

theorem ushli0_cert31 : FixShOK Ushli0.cells Ushli0.outs 31 (shlSrc 31) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k31_b0
  | 1, _ => exact shl_k31_b1
  | 2, _ => exact shl_k31_b2
  | 3, _ => exact shl_k31_b3
  | 4, _ => exact shl_k31_b4
  | 5, _ => exact shl_k31_b5
  | 6, _ => exact shl_k31_b6
  | 7, _ => exact shl_k31_b7
  | 8, _ => exact shl_k31_b8
  | 9, _ => exact shl_k31_b9
  | 10, _ => exact shl_k31_b10
  | 11, _ => exact shl_k31_b11
  | 12, _ => exact shl_k31_b12
  | 13, _ => exact shl_k31_b13
  | 14, _ => exact shl_k31_b14
  | 15, _ => exact shl_k31_b15
  | 16, _ => exact shl_k31_b16
  | 17, _ => exact shl_k31_b17
  | 18, _ => exact shl_k31_b18
  | 19, _ => exact shl_k31_b19
  | 20, _ => exact shl_k31_b20
  | 21, _ => exact shl_k31_b21
  | 22, _ => exact shl_k31_b22
  | 23, _ => exact shl_k31_b23
  | 24, _ => exact shl_k31_b24
  | 25, _ => exact shl_k31_b25
  | 26, _ => exact shl_k31_b26
  | 27, _ => exact shl_k31_b27
  | 28, _ => exact shl_k31_b28
  | 29, _ => exact shl_k31_b29
  | 30, _ => exact shl_k31_b30
  | 31, _ => exact shl_k31_b31
  | _ + 32, h => exact absurd h (by omega)

end Formal.Net.Compute.GcdD
