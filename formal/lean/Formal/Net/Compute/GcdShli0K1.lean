import Formal.Net.Compute.Shift
import Formal.Gen.Compute.GcdD.Ushli0

/-!
# H_COMPUTE_FN for gcd_hw's `ushli0`, shift amounts 8..15

Certificates `FixShOK` for `bdc_fused_ushli0` (bdc Verilog `z = e0 << e1`, a 412-cell barrel
shifter) with port `e1` fixed to each `k` in this range: each output bit's folded cone is checked
over its folded support (one kernel check per bit). Assembled in `GcdShli0.lean`.
-/

namespace Formal.Net.Compute.GcdD
open Formal.Net.Compute Formal.Net.GcdHw Formal.Gen.Compute.GcdD

abbrev ShlBit1 (k i : Nat) : Prop :=
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
theorem shl_k8_b0 : ShlBit1 8 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b1 : ShlBit1 8 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b2 : ShlBit1 8 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b3 : ShlBit1 8 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b4 : ShlBit1 8 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b5 : ShlBit1 8 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b6 : ShlBit1 8 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b7 : ShlBit1 8 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b8 : ShlBit1 8 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b9 : ShlBit1 8 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b10 : ShlBit1 8 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b11 : ShlBit1 8 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b12 : ShlBit1 8 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b13 : ShlBit1 8 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b14 : ShlBit1 8 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b15 : ShlBit1 8 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b16 : ShlBit1 8 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b17 : ShlBit1 8 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b18 : ShlBit1 8 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b19 : ShlBit1 8 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b20 : ShlBit1 8 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b21 : ShlBit1 8 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b22 : ShlBit1 8 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b23 : ShlBit1 8 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b24 : ShlBit1 8 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b25 : ShlBit1 8 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b26 : ShlBit1 8 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b27 : ShlBit1 8 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b28 : ShlBit1 8 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b29 : ShlBit1 8 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b30 : ShlBit1 8 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k8_b31 : ShlBit1 8 31 := by decide +kernel

theorem ushli0_cert8 : FixShOK Ushli0.cells Ushli0.outs 8 (shlSrc 8) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k8_b0
  | 1, _ => exact shl_k8_b1
  | 2, _ => exact shl_k8_b2
  | 3, _ => exact shl_k8_b3
  | 4, _ => exact shl_k8_b4
  | 5, _ => exact shl_k8_b5
  | 6, _ => exact shl_k8_b6
  | 7, _ => exact shl_k8_b7
  | 8, _ => exact shl_k8_b8
  | 9, _ => exact shl_k8_b9
  | 10, _ => exact shl_k8_b10
  | 11, _ => exact shl_k8_b11
  | 12, _ => exact shl_k8_b12
  | 13, _ => exact shl_k8_b13
  | 14, _ => exact shl_k8_b14
  | 15, _ => exact shl_k8_b15
  | 16, _ => exact shl_k8_b16
  | 17, _ => exact shl_k8_b17
  | 18, _ => exact shl_k8_b18
  | 19, _ => exact shl_k8_b19
  | 20, _ => exact shl_k8_b20
  | 21, _ => exact shl_k8_b21
  | 22, _ => exact shl_k8_b22
  | 23, _ => exact shl_k8_b23
  | 24, _ => exact shl_k8_b24
  | 25, _ => exact shl_k8_b25
  | 26, _ => exact shl_k8_b26
  | 27, _ => exact shl_k8_b27
  | 28, _ => exact shl_k8_b28
  | 29, _ => exact shl_k8_b29
  | 30, _ => exact shl_k8_b30
  | 31, _ => exact shl_k8_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k9_b0 : ShlBit1 9 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b1 : ShlBit1 9 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b2 : ShlBit1 9 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b3 : ShlBit1 9 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b4 : ShlBit1 9 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b5 : ShlBit1 9 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b6 : ShlBit1 9 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b7 : ShlBit1 9 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b8 : ShlBit1 9 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b9 : ShlBit1 9 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b10 : ShlBit1 9 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b11 : ShlBit1 9 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b12 : ShlBit1 9 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b13 : ShlBit1 9 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b14 : ShlBit1 9 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b15 : ShlBit1 9 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b16 : ShlBit1 9 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b17 : ShlBit1 9 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b18 : ShlBit1 9 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b19 : ShlBit1 9 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b20 : ShlBit1 9 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b21 : ShlBit1 9 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b22 : ShlBit1 9 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b23 : ShlBit1 9 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b24 : ShlBit1 9 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b25 : ShlBit1 9 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b26 : ShlBit1 9 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b27 : ShlBit1 9 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b28 : ShlBit1 9 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b29 : ShlBit1 9 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b30 : ShlBit1 9 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k9_b31 : ShlBit1 9 31 := by decide +kernel

theorem ushli0_cert9 : FixShOK Ushli0.cells Ushli0.outs 9 (shlSrc 9) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k9_b0
  | 1, _ => exact shl_k9_b1
  | 2, _ => exact shl_k9_b2
  | 3, _ => exact shl_k9_b3
  | 4, _ => exact shl_k9_b4
  | 5, _ => exact shl_k9_b5
  | 6, _ => exact shl_k9_b6
  | 7, _ => exact shl_k9_b7
  | 8, _ => exact shl_k9_b8
  | 9, _ => exact shl_k9_b9
  | 10, _ => exact shl_k9_b10
  | 11, _ => exact shl_k9_b11
  | 12, _ => exact shl_k9_b12
  | 13, _ => exact shl_k9_b13
  | 14, _ => exact shl_k9_b14
  | 15, _ => exact shl_k9_b15
  | 16, _ => exact shl_k9_b16
  | 17, _ => exact shl_k9_b17
  | 18, _ => exact shl_k9_b18
  | 19, _ => exact shl_k9_b19
  | 20, _ => exact shl_k9_b20
  | 21, _ => exact shl_k9_b21
  | 22, _ => exact shl_k9_b22
  | 23, _ => exact shl_k9_b23
  | 24, _ => exact shl_k9_b24
  | 25, _ => exact shl_k9_b25
  | 26, _ => exact shl_k9_b26
  | 27, _ => exact shl_k9_b27
  | 28, _ => exact shl_k9_b28
  | 29, _ => exact shl_k9_b29
  | 30, _ => exact shl_k9_b30
  | 31, _ => exact shl_k9_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k10_b0 : ShlBit1 10 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b1 : ShlBit1 10 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b2 : ShlBit1 10 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b3 : ShlBit1 10 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b4 : ShlBit1 10 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b5 : ShlBit1 10 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b6 : ShlBit1 10 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b7 : ShlBit1 10 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b8 : ShlBit1 10 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b9 : ShlBit1 10 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b10 : ShlBit1 10 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b11 : ShlBit1 10 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b12 : ShlBit1 10 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b13 : ShlBit1 10 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b14 : ShlBit1 10 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b15 : ShlBit1 10 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b16 : ShlBit1 10 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b17 : ShlBit1 10 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b18 : ShlBit1 10 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b19 : ShlBit1 10 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b20 : ShlBit1 10 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b21 : ShlBit1 10 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b22 : ShlBit1 10 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b23 : ShlBit1 10 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b24 : ShlBit1 10 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b25 : ShlBit1 10 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b26 : ShlBit1 10 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b27 : ShlBit1 10 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b28 : ShlBit1 10 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b29 : ShlBit1 10 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b30 : ShlBit1 10 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k10_b31 : ShlBit1 10 31 := by decide +kernel

theorem ushli0_cert10 : FixShOK Ushli0.cells Ushli0.outs 10 (shlSrc 10) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k10_b0
  | 1, _ => exact shl_k10_b1
  | 2, _ => exact shl_k10_b2
  | 3, _ => exact shl_k10_b3
  | 4, _ => exact shl_k10_b4
  | 5, _ => exact shl_k10_b5
  | 6, _ => exact shl_k10_b6
  | 7, _ => exact shl_k10_b7
  | 8, _ => exact shl_k10_b8
  | 9, _ => exact shl_k10_b9
  | 10, _ => exact shl_k10_b10
  | 11, _ => exact shl_k10_b11
  | 12, _ => exact shl_k10_b12
  | 13, _ => exact shl_k10_b13
  | 14, _ => exact shl_k10_b14
  | 15, _ => exact shl_k10_b15
  | 16, _ => exact shl_k10_b16
  | 17, _ => exact shl_k10_b17
  | 18, _ => exact shl_k10_b18
  | 19, _ => exact shl_k10_b19
  | 20, _ => exact shl_k10_b20
  | 21, _ => exact shl_k10_b21
  | 22, _ => exact shl_k10_b22
  | 23, _ => exact shl_k10_b23
  | 24, _ => exact shl_k10_b24
  | 25, _ => exact shl_k10_b25
  | 26, _ => exact shl_k10_b26
  | 27, _ => exact shl_k10_b27
  | 28, _ => exact shl_k10_b28
  | 29, _ => exact shl_k10_b29
  | 30, _ => exact shl_k10_b30
  | 31, _ => exact shl_k10_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k11_b0 : ShlBit1 11 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b1 : ShlBit1 11 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b2 : ShlBit1 11 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b3 : ShlBit1 11 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b4 : ShlBit1 11 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b5 : ShlBit1 11 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b6 : ShlBit1 11 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b7 : ShlBit1 11 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b8 : ShlBit1 11 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b9 : ShlBit1 11 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b10 : ShlBit1 11 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b11 : ShlBit1 11 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b12 : ShlBit1 11 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b13 : ShlBit1 11 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b14 : ShlBit1 11 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b15 : ShlBit1 11 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b16 : ShlBit1 11 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b17 : ShlBit1 11 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b18 : ShlBit1 11 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b19 : ShlBit1 11 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b20 : ShlBit1 11 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b21 : ShlBit1 11 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b22 : ShlBit1 11 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b23 : ShlBit1 11 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b24 : ShlBit1 11 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b25 : ShlBit1 11 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b26 : ShlBit1 11 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b27 : ShlBit1 11 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b28 : ShlBit1 11 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b29 : ShlBit1 11 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b30 : ShlBit1 11 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k11_b31 : ShlBit1 11 31 := by decide +kernel

theorem ushli0_cert11 : FixShOK Ushli0.cells Ushli0.outs 11 (shlSrc 11) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k11_b0
  | 1, _ => exact shl_k11_b1
  | 2, _ => exact shl_k11_b2
  | 3, _ => exact shl_k11_b3
  | 4, _ => exact shl_k11_b4
  | 5, _ => exact shl_k11_b5
  | 6, _ => exact shl_k11_b6
  | 7, _ => exact shl_k11_b7
  | 8, _ => exact shl_k11_b8
  | 9, _ => exact shl_k11_b9
  | 10, _ => exact shl_k11_b10
  | 11, _ => exact shl_k11_b11
  | 12, _ => exact shl_k11_b12
  | 13, _ => exact shl_k11_b13
  | 14, _ => exact shl_k11_b14
  | 15, _ => exact shl_k11_b15
  | 16, _ => exact shl_k11_b16
  | 17, _ => exact shl_k11_b17
  | 18, _ => exact shl_k11_b18
  | 19, _ => exact shl_k11_b19
  | 20, _ => exact shl_k11_b20
  | 21, _ => exact shl_k11_b21
  | 22, _ => exact shl_k11_b22
  | 23, _ => exact shl_k11_b23
  | 24, _ => exact shl_k11_b24
  | 25, _ => exact shl_k11_b25
  | 26, _ => exact shl_k11_b26
  | 27, _ => exact shl_k11_b27
  | 28, _ => exact shl_k11_b28
  | 29, _ => exact shl_k11_b29
  | 30, _ => exact shl_k11_b30
  | 31, _ => exact shl_k11_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k12_b0 : ShlBit1 12 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b1 : ShlBit1 12 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b2 : ShlBit1 12 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b3 : ShlBit1 12 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b4 : ShlBit1 12 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b5 : ShlBit1 12 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b6 : ShlBit1 12 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b7 : ShlBit1 12 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b8 : ShlBit1 12 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b9 : ShlBit1 12 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b10 : ShlBit1 12 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b11 : ShlBit1 12 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b12 : ShlBit1 12 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b13 : ShlBit1 12 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b14 : ShlBit1 12 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b15 : ShlBit1 12 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b16 : ShlBit1 12 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b17 : ShlBit1 12 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b18 : ShlBit1 12 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b19 : ShlBit1 12 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b20 : ShlBit1 12 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b21 : ShlBit1 12 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b22 : ShlBit1 12 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b23 : ShlBit1 12 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b24 : ShlBit1 12 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b25 : ShlBit1 12 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b26 : ShlBit1 12 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b27 : ShlBit1 12 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b28 : ShlBit1 12 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b29 : ShlBit1 12 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b30 : ShlBit1 12 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k12_b31 : ShlBit1 12 31 := by decide +kernel

theorem ushli0_cert12 : FixShOK Ushli0.cells Ushli0.outs 12 (shlSrc 12) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k12_b0
  | 1, _ => exact shl_k12_b1
  | 2, _ => exact shl_k12_b2
  | 3, _ => exact shl_k12_b3
  | 4, _ => exact shl_k12_b4
  | 5, _ => exact shl_k12_b5
  | 6, _ => exact shl_k12_b6
  | 7, _ => exact shl_k12_b7
  | 8, _ => exact shl_k12_b8
  | 9, _ => exact shl_k12_b9
  | 10, _ => exact shl_k12_b10
  | 11, _ => exact shl_k12_b11
  | 12, _ => exact shl_k12_b12
  | 13, _ => exact shl_k12_b13
  | 14, _ => exact shl_k12_b14
  | 15, _ => exact shl_k12_b15
  | 16, _ => exact shl_k12_b16
  | 17, _ => exact shl_k12_b17
  | 18, _ => exact shl_k12_b18
  | 19, _ => exact shl_k12_b19
  | 20, _ => exact shl_k12_b20
  | 21, _ => exact shl_k12_b21
  | 22, _ => exact shl_k12_b22
  | 23, _ => exact shl_k12_b23
  | 24, _ => exact shl_k12_b24
  | 25, _ => exact shl_k12_b25
  | 26, _ => exact shl_k12_b26
  | 27, _ => exact shl_k12_b27
  | 28, _ => exact shl_k12_b28
  | 29, _ => exact shl_k12_b29
  | 30, _ => exact shl_k12_b30
  | 31, _ => exact shl_k12_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k13_b0 : ShlBit1 13 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b1 : ShlBit1 13 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b2 : ShlBit1 13 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b3 : ShlBit1 13 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b4 : ShlBit1 13 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b5 : ShlBit1 13 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b6 : ShlBit1 13 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b7 : ShlBit1 13 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b8 : ShlBit1 13 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b9 : ShlBit1 13 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b10 : ShlBit1 13 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b11 : ShlBit1 13 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b12 : ShlBit1 13 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b13 : ShlBit1 13 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b14 : ShlBit1 13 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b15 : ShlBit1 13 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b16 : ShlBit1 13 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b17 : ShlBit1 13 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b18 : ShlBit1 13 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b19 : ShlBit1 13 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b20 : ShlBit1 13 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b21 : ShlBit1 13 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b22 : ShlBit1 13 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b23 : ShlBit1 13 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b24 : ShlBit1 13 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b25 : ShlBit1 13 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b26 : ShlBit1 13 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b27 : ShlBit1 13 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b28 : ShlBit1 13 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b29 : ShlBit1 13 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b30 : ShlBit1 13 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k13_b31 : ShlBit1 13 31 := by decide +kernel

theorem ushli0_cert13 : FixShOK Ushli0.cells Ushli0.outs 13 (shlSrc 13) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k13_b0
  | 1, _ => exact shl_k13_b1
  | 2, _ => exact shl_k13_b2
  | 3, _ => exact shl_k13_b3
  | 4, _ => exact shl_k13_b4
  | 5, _ => exact shl_k13_b5
  | 6, _ => exact shl_k13_b6
  | 7, _ => exact shl_k13_b7
  | 8, _ => exact shl_k13_b8
  | 9, _ => exact shl_k13_b9
  | 10, _ => exact shl_k13_b10
  | 11, _ => exact shl_k13_b11
  | 12, _ => exact shl_k13_b12
  | 13, _ => exact shl_k13_b13
  | 14, _ => exact shl_k13_b14
  | 15, _ => exact shl_k13_b15
  | 16, _ => exact shl_k13_b16
  | 17, _ => exact shl_k13_b17
  | 18, _ => exact shl_k13_b18
  | 19, _ => exact shl_k13_b19
  | 20, _ => exact shl_k13_b20
  | 21, _ => exact shl_k13_b21
  | 22, _ => exact shl_k13_b22
  | 23, _ => exact shl_k13_b23
  | 24, _ => exact shl_k13_b24
  | 25, _ => exact shl_k13_b25
  | 26, _ => exact shl_k13_b26
  | 27, _ => exact shl_k13_b27
  | 28, _ => exact shl_k13_b28
  | 29, _ => exact shl_k13_b29
  | 30, _ => exact shl_k13_b30
  | 31, _ => exact shl_k13_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k14_b0 : ShlBit1 14 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b1 : ShlBit1 14 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b2 : ShlBit1 14 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b3 : ShlBit1 14 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b4 : ShlBit1 14 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b5 : ShlBit1 14 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b6 : ShlBit1 14 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b7 : ShlBit1 14 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b8 : ShlBit1 14 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b9 : ShlBit1 14 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b10 : ShlBit1 14 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b11 : ShlBit1 14 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b12 : ShlBit1 14 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b13 : ShlBit1 14 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b14 : ShlBit1 14 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b15 : ShlBit1 14 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b16 : ShlBit1 14 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b17 : ShlBit1 14 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b18 : ShlBit1 14 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b19 : ShlBit1 14 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b20 : ShlBit1 14 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b21 : ShlBit1 14 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b22 : ShlBit1 14 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b23 : ShlBit1 14 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b24 : ShlBit1 14 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b25 : ShlBit1 14 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b26 : ShlBit1 14 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b27 : ShlBit1 14 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b28 : ShlBit1 14 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b29 : ShlBit1 14 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b30 : ShlBit1 14 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k14_b31 : ShlBit1 14 31 := by decide +kernel

theorem ushli0_cert14 : FixShOK Ushli0.cells Ushli0.outs 14 (shlSrc 14) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k14_b0
  | 1, _ => exact shl_k14_b1
  | 2, _ => exact shl_k14_b2
  | 3, _ => exact shl_k14_b3
  | 4, _ => exact shl_k14_b4
  | 5, _ => exact shl_k14_b5
  | 6, _ => exact shl_k14_b6
  | 7, _ => exact shl_k14_b7
  | 8, _ => exact shl_k14_b8
  | 9, _ => exact shl_k14_b9
  | 10, _ => exact shl_k14_b10
  | 11, _ => exact shl_k14_b11
  | 12, _ => exact shl_k14_b12
  | 13, _ => exact shl_k14_b13
  | 14, _ => exact shl_k14_b14
  | 15, _ => exact shl_k14_b15
  | 16, _ => exact shl_k14_b16
  | 17, _ => exact shl_k14_b17
  | 18, _ => exact shl_k14_b18
  | 19, _ => exact shl_k14_b19
  | 20, _ => exact shl_k14_b20
  | 21, _ => exact shl_k14_b21
  | 22, _ => exact shl_k14_b22
  | 23, _ => exact shl_k14_b23
  | 24, _ => exact shl_k14_b24
  | 25, _ => exact shl_k14_b25
  | 26, _ => exact shl_k14_b26
  | 27, _ => exact shl_k14_b27
  | 28, _ => exact shl_k14_b28
  | 29, _ => exact shl_k14_b29
  | 30, _ => exact shl_k14_b30
  | 31, _ => exact shl_k14_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k15_b0 : ShlBit1 15 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b1 : ShlBit1 15 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b2 : ShlBit1 15 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b3 : ShlBit1 15 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b4 : ShlBit1 15 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b5 : ShlBit1 15 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b6 : ShlBit1 15 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b7 : ShlBit1 15 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b8 : ShlBit1 15 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b9 : ShlBit1 15 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b10 : ShlBit1 15 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b11 : ShlBit1 15 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b12 : ShlBit1 15 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b13 : ShlBit1 15 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b14 : ShlBit1 15 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b15 : ShlBit1 15 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b16 : ShlBit1 15 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b17 : ShlBit1 15 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b18 : ShlBit1 15 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b19 : ShlBit1 15 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b20 : ShlBit1 15 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b21 : ShlBit1 15 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b22 : ShlBit1 15 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b23 : ShlBit1 15 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b24 : ShlBit1 15 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b25 : ShlBit1 15 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b26 : ShlBit1 15 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b27 : ShlBit1 15 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b28 : ShlBit1 15 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b29 : ShlBit1 15 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b30 : ShlBit1 15 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k15_b31 : ShlBit1 15 31 := by decide +kernel

theorem ushli0_cert15 : FixShOK Ushli0.cells Ushli0.outs 15 (shlSrc 15) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k15_b0
  | 1, _ => exact shl_k15_b1
  | 2, _ => exact shl_k15_b2
  | 3, _ => exact shl_k15_b3
  | 4, _ => exact shl_k15_b4
  | 5, _ => exact shl_k15_b5
  | 6, _ => exact shl_k15_b6
  | 7, _ => exact shl_k15_b7
  | 8, _ => exact shl_k15_b8
  | 9, _ => exact shl_k15_b9
  | 10, _ => exact shl_k15_b10
  | 11, _ => exact shl_k15_b11
  | 12, _ => exact shl_k15_b12
  | 13, _ => exact shl_k15_b13
  | 14, _ => exact shl_k15_b14
  | 15, _ => exact shl_k15_b15
  | 16, _ => exact shl_k15_b16
  | 17, _ => exact shl_k15_b17
  | 18, _ => exact shl_k15_b18
  | 19, _ => exact shl_k15_b19
  | 20, _ => exact shl_k15_b20
  | 21, _ => exact shl_k15_b21
  | 22, _ => exact shl_k15_b22
  | 23, _ => exact shl_k15_b23
  | 24, _ => exact shl_k15_b24
  | 25, _ => exact shl_k15_b25
  | 26, _ => exact shl_k15_b26
  | 27, _ => exact shl_k15_b27
  | 28, _ => exact shl_k15_b28
  | 29, _ => exact shl_k15_b29
  | 30, _ => exact shl_k15_b30
  | 31, _ => exact shl_k15_b31
  | _ + 32, h => exact absurd h (by omega)

end Formal.Net.Compute.GcdD
