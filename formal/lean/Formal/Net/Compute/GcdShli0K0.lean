import Formal.Net.Compute.Shift
import Formal.Gen.Compute.GcdD.Ushli0

/-!
# H_COMPUTE_FN for gcd_hw's `ushli0`, shift amounts 0..7

Certificates `FixShOK` for `bdc_fused_ushli0` (bdc Verilog `z = e0 << e1`, a 412-cell barrel
shifter) with port `e1` fixed to each `k` in this range: each output bit's folded cone is checked
over its folded support (one kernel check per bit). Assembled in `GcdShli0.lean`.
-/

namespace Formal.Net.Compute.GcdD
open Formal.Net.Compute Formal.Net.GcdHw Formal.Gen.Compute.GcdD

abbrev ShlBit0 (k i : Nat) : Prop :=
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
theorem shl_k0_b0 : ShlBit0 0 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b1 : ShlBit0 0 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b2 : ShlBit0 0 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b3 : ShlBit0 0 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b4 : ShlBit0 0 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b5 : ShlBit0 0 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b6 : ShlBit0 0 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b7 : ShlBit0 0 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b8 : ShlBit0 0 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b9 : ShlBit0 0 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b10 : ShlBit0 0 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b11 : ShlBit0 0 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b12 : ShlBit0 0 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b13 : ShlBit0 0 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b14 : ShlBit0 0 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b15 : ShlBit0 0 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b16 : ShlBit0 0 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b17 : ShlBit0 0 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b18 : ShlBit0 0 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b19 : ShlBit0 0 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b20 : ShlBit0 0 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b21 : ShlBit0 0 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b22 : ShlBit0 0 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b23 : ShlBit0 0 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b24 : ShlBit0 0 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b25 : ShlBit0 0 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b26 : ShlBit0 0 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b27 : ShlBit0 0 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b28 : ShlBit0 0 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b29 : ShlBit0 0 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b30 : ShlBit0 0 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k0_b31 : ShlBit0 0 31 := by decide +kernel

theorem ushli0_cert0 : FixShOK Ushli0.cells Ushli0.outs 0 (shlSrc 0) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k0_b0
  | 1, _ => exact shl_k0_b1
  | 2, _ => exact shl_k0_b2
  | 3, _ => exact shl_k0_b3
  | 4, _ => exact shl_k0_b4
  | 5, _ => exact shl_k0_b5
  | 6, _ => exact shl_k0_b6
  | 7, _ => exact shl_k0_b7
  | 8, _ => exact shl_k0_b8
  | 9, _ => exact shl_k0_b9
  | 10, _ => exact shl_k0_b10
  | 11, _ => exact shl_k0_b11
  | 12, _ => exact shl_k0_b12
  | 13, _ => exact shl_k0_b13
  | 14, _ => exact shl_k0_b14
  | 15, _ => exact shl_k0_b15
  | 16, _ => exact shl_k0_b16
  | 17, _ => exact shl_k0_b17
  | 18, _ => exact shl_k0_b18
  | 19, _ => exact shl_k0_b19
  | 20, _ => exact shl_k0_b20
  | 21, _ => exact shl_k0_b21
  | 22, _ => exact shl_k0_b22
  | 23, _ => exact shl_k0_b23
  | 24, _ => exact shl_k0_b24
  | 25, _ => exact shl_k0_b25
  | 26, _ => exact shl_k0_b26
  | 27, _ => exact shl_k0_b27
  | 28, _ => exact shl_k0_b28
  | 29, _ => exact shl_k0_b29
  | 30, _ => exact shl_k0_b30
  | 31, _ => exact shl_k0_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k1_b0 : ShlBit0 1 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b1 : ShlBit0 1 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b2 : ShlBit0 1 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b3 : ShlBit0 1 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b4 : ShlBit0 1 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b5 : ShlBit0 1 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b6 : ShlBit0 1 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b7 : ShlBit0 1 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b8 : ShlBit0 1 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b9 : ShlBit0 1 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b10 : ShlBit0 1 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b11 : ShlBit0 1 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b12 : ShlBit0 1 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b13 : ShlBit0 1 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b14 : ShlBit0 1 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b15 : ShlBit0 1 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b16 : ShlBit0 1 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b17 : ShlBit0 1 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b18 : ShlBit0 1 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b19 : ShlBit0 1 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b20 : ShlBit0 1 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b21 : ShlBit0 1 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b22 : ShlBit0 1 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b23 : ShlBit0 1 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b24 : ShlBit0 1 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b25 : ShlBit0 1 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b26 : ShlBit0 1 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b27 : ShlBit0 1 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b28 : ShlBit0 1 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b29 : ShlBit0 1 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b30 : ShlBit0 1 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k1_b31 : ShlBit0 1 31 := by decide +kernel

theorem ushli0_cert1 : FixShOK Ushli0.cells Ushli0.outs 1 (shlSrc 1) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k1_b0
  | 1, _ => exact shl_k1_b1
  | 2, _ => exact shl_k1_b2
  | 3, _ => exact shl_k1_b3
  | 4, _ => exact shl_k1_b4
  | 5, _ => exact shl_k1_b5
  | 6, _ => exact shl_k1_b6
  | 7, _ => exact shl_k1_b7
  | 8, _ => exact shl_k1_b8
  | 9, _ => exact shl_k1_b9
  | 10, _ => exact shl_k1_b10
  | 11, _ => exact shl_k1_b11
  | 12, _ => exact shl_k1_b12
  | 13, _ => exact shl_k1_b13
  | 14, _ => exact shl_k1_b14
  | 15, _ => exact shl_k1_b15
  | 16, _ => exact shl_k1_b16
  | 17, _ => exact shl_k1_b17
  | 18, _ => exact shl_k1_b18
  | 19, _ => exact shl_k1_b19
  | 20, _ => exact shl_k1_b20
  | 21, _ => exact shl_k1_b21
  | 22, _ => exact shl_k1_b22
  | 23, _ => exact shl_k1_b23
  | 24, _ => exact shl_k1_b24
  | 25, _ => exact shl_k1_b25
  | 26, _ => exact shl_k1_b26
  | 27, _ => exact shl_k1_b27
  | 28, _ => exact shl_k1_b28
  | 29, _ => exact shl_k1_b29
  | 30, _ => exact shl_k1_b30
  | 31, _ => exact shl_k1_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k2_b0 : ShlBit0 2 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b1 : ShlBit0 2 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b2 : ShlBit0 2 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b3 : ShlBit0 2 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b4 : ShlBit0 2 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b5 : ShlBit0 2 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b6 : ShlBit0 2 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b7 : ShlBit0 2 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b8 : ShlBit0 2 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b9 : ShlBit0 2 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b10 : ShlBit0 2 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b11 : ShlBit0 2 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b12 : ShlBit0 2 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b13 : ShlBit0 2 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b14 : ShlBit0 2 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b15 : ShlBit0 2 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b16 : ShlBit0 2 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b17 : ShlBit0 2 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b18 : ShlBit0 2 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b19 : ShlBit0 2 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b20 : ShlBit0 2 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b21 : ShlBit0 2 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b22 : ShlBit0 2 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b23 : ShlBit0 2 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b24 : ShlBit0 2 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b25 : ShlBit0 2 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b26 : ShlBit0 2 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b27 : ShlBit0 2 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b28 : ShlBit0 2 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b29 : ShlBit0 2 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b30 : ShlBit0 2 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k2_b31 : ShlBit0 2 31 := by decide +kernel

theorem ushli0_cert2 : FixShOK Ushli0.cells Ushli0.outs 2 (shlSrc 2) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k2_b0
  | 1, _ => exact shl_k2_b1
  | 2, _ => exact shl_k2_b2
  | 3, _ => exact shl_k2_b3
  | 4, _ => exact shl_k2_b4
  | 5, _ => exact shl_k2_b5
  | 6, _ => exact shl_k2_b6
  | 7, _ => exact shl_k2_b7
  | 8, _ => exact shl_k2_b8
  | 9, _ => exact shl_k2_b9
  | 10, _ => exact shl_k2_b10
  | 11, _ => exact shl_k2_b11
  | 12, _ => exact shl_k2_b12
  | 13, _ => exact shl_k2_b13
  | 14, _ => exact shl_k2_b14
  | 15, _ => exact shl_k2_b15
  | 16, _ => exact shl_k2_b16
  | 17, _ => exact shl_k2_b17
  | 18, _ => exact shl_k2_b18
  | 19, _ => exact shl_k2_b19
  | 20, _ => exact shl_k2_b20
  | 21, _ => exact shl_k2_b21
  | 22, _ => exact shl_k2_b22
  | 23, _ => exact shl_k2_b23
  | 24, _ => exact shl_k2_b24
  | 25, _ => exact shl_k2_b25
  | 26, _ => exact shl_k2_b26
  | 27, _ => exact shl_k2_b27
  | 28, _ => exact shl_k2_b28
  | 29, _ => exact shl_k2_b29
  | 30, _ => exact shl_k2_b30
  | 31, _ => exact shl_k2_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k3_b0 : ShlBit0 3 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b1 : ShlBit0 3 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b2 : ShlBit0 3 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b3 : ShlBit0 3 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b4 : ShlBit0 3 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b5 : ShlBit0 3 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b6 : ShlBit0 3 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b7 : ShlBit0 3 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b8 : ShlBit0 3 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b9 : ShlBit0 3 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b10 : ShlBit0 3 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b11 : ShlBit0 3 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b12 : ShlBit0 3 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b13 : ShlBit0 3 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b14 : ShlBit0 3 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b15 : ShlBit0 3 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b16 : ShlBit0 3 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b17 : ShlBit0 3 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b18 : ShlBit0 3 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b19 : ShlBit0 3 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b20 : ShlBit0 3 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b21 : ShlBit0 3 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b22 : ShlBit0 3 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b23 : ShlBit0 3 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b24 : ShlBit0 3 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b25 : ShlBit0 3 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b26 : ShlBit0 3 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b27 : ShlBit0 3 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b28 : ShlBit0 3 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b29 : ShlBit0 3 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b30 : ShlBit0 3 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k3_b31 : ShlBit0 3 31 := by decide +kernel

theorem ushli0_cert3 : FixShOK Ushli0.cells Ushli0.outs 3 (shlSrc 3) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k3_b0
  | 1, _ => exact shl_k3_b1
  | 2, _ => exact shl_k3_b2
  | 3, _ => exact shl_k3_b3
  | 4, _ => exact shl_k3_b4
  | 5, _ => exact shl_k3_b5
  | 6, _ => exact shl_k3_b6
  | 7, _ => exact shl_k3_b7
  | 8, _ => exact shl_k3_b8
  | 9, _ => exact shl_k3_b9
  | 10, _ => exact shl_k3_b10
  | 11, _ => exact shl_k3_b11
  | 12, _ => exact shl_k3_b12
  | 13, _ => exact shl_k3_b13
  | 14, _ => exact shl_k3_b14
  | 15, _ => exact shl_k3_b15
  | 16, _ => exact shl_k3_b16
  | 17, _ => exact shl_k3_b17
  | 18, _ => exact shl_k3_b18
  | 19, _ => exact shl_k3_b19
  | 20, _ => exact shl_k3_b20
  | 21, _ => exact shl_k3_b21
  | 22, _ => exact shl_k3_b22
  | 23, _ => exact shl_k3_b23
  | 24, _ => exact shl_k3_b24
  | 25, _ => exact shl_k3_b25
  | 26, _ => exact shl_k3_b26
  | 27, _ => exact shl_k3_b27
  | 28, _ => exact shl_k3_b28
  | 29, _ => exact shl_k3_b29
  | 30, _ => exact shl_k3_b30
  | 31, _ => exact shl_k3_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k4_b0 : ShlBit0 4 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b1 : ShlBit0 4 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b2 : ShlBit0 4 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b3 : ShlBit0 4 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b4 : ShlBit0 4 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b5 : ShlBit0 4 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b6 : ShlBit0 4 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b7 : ShlBit0 4 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b8 : ShlBit0 4 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b9 : ShlBit0 4 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b10 : ShlBit0 4 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b11 : ShlBit0 4 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b12 : ShlBit0 4 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b13 : ShlBit0 4 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b14 : ShlBit0 4 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b15 : ShlBit0 4 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b16 : ShlBit0 4 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b17 : ShlBit0 4 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b18 : ShlBit0 4 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b19 : ShlBit0 4 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b20 : ShlBit0 4 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b21 : ShlBit0 4 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b22 : ShlBit0 4 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b23 : ShlBit0 4 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b24 : ShlBit0 4 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b25 : ShlBit0 4 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b26 : ShlBit0 4 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b27 : ShlBit0 4 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b28 : ShlBit0 4 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b29 : ShlBit0 4 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b30 : ShlBit0 4 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k4_b31 : ShlBit0 4 31 := by decide +kernel

theorem ushli0_cert4 : FixShOK Ushli0.cells Ushli0.outs 4 (shlSrc 4) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k4_b0
  | 1, _ => exact shl_k4_b1
  | 2, _ => exact shl_k4_b2
  | 3, _ => exact shl_k4_b3
  | 4, _ => exact shl_k4_b4
  | 5, _ => exact shl_k4_b5
  | 6, _ => exact shl_k4_b6
  | 7, _ => exact shl_k4_b7
  | 8, _ => exact shl_k4_b8
  | 9, _ => exact shl_k4_b9
  | 10, _ => exact shl_k4_b10
  | 11, _ => exact shl_k4_b11
  | 12, _ => exact shl_k4_b12
  | 13, _ => exact shl_k4_b13
  | 14, _ => exact shl_k4_b14
  | 15, _ => exact shl_k4_b15
  | 16, _ => exact shl_k4_b16
  | 17, _ => exact shl_k4_b17
  | 18, _ => exact shl_k4_b18
  | 19, _ => exact shl_k4_b19
  | 20, _ => exact shl_k4_b20
  | 21, _ => exact shl_k4_b21
  | 22, _ => exact shl_k4_b22
  | 23, _ => exact shl_k4_b23
  | 24, _ => exact shl_k4_b24
  | 25, _ => exact shl_k4_b25
  | 26, _ => exact shl_k4_b26
  | 27, _ => exact shl_k4_b27
  | 28, _ => exact shl_k4_b28
  | 29, _ => exact shl_k4_b29
  | 30, _ => exact shl_k4_b30
  | 31, _ => exact shl_k4_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k5_b0 : ShlBit0 5 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b1 : ShlBit0 5 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b2 : ShlBit0 5 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b3 : ShlBit0 5 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b4 : ShlBit0 5 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b5 : ShlBit0 5 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b6 : ShlBit0 5 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b7 : ShlBit0 5 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b8 : ShlBit0 5 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b9 : ShlBit0 5 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b10 : ShlBit0 5 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b11 : ShlBit0 5 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b12 : ShlBit0 5 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b13 : ShlBit0 5 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b14 : ShlBit0 5 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b15 : ShlBit0 5 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b16 : ShlBit0 5 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b17 : ShlBit0 5 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b18 : ShlBit0 5 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b19 : ShlBit0 5 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b20 : ShlBit0 5 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b21 : ShlBit0 5 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b22 : ShlBit0 5 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b23 : ShlBit0 5 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b24 : ShlBit0 5 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b25 : ShlBit0 5 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b26 : ShlBit0 5 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b27 : ShlBit0 5 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b28 : ShlBit0 5 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b29 : ShlBit0 5 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b30 : ShlBit0 5 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k5_b31 : ShlBit0 5 31 := by decide +kernel

theorem ushli0_cert5 : FixShOK Ushli0.cells Ushli0.outs 5 (shlSrc 5) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k5_b0
  | 1, _ => exact shl_k5_b1
  | 2, _ => exact shl_k5_b2
  | 3, _ => exact shl_k5_b3
  | 4, _ => exact shl_k5_b4
  | 5, _ => exact shl_k5_b5
  | 6, _ => exact shl_k5_b6
  | 7, _ => exact shl_k5_b7
  | 8, _ => exact shl_k5_b8
  | 9, _ => exact shl_k5_b9
  | 10, _ => exact shl_k5_b10
  | 11, _ => exact shl_k5_b11
  | 12, _ => exact shl_k5_b12
  | 13, _ => exact shl_k5_b13
  | 14, _ => exact shl_k5_b14
  | 15, _ => exact shl_k5_b15
  | 16, _ => exact shl_k5_b16
  | 17, _ => exact shl_k5_b17
  | 18, _ => exact shl_k5_b18
  | 19, _ => exact shl_k5_b19
  | 20, _ => exact shl_k5_b20
  | 21, _ => exact shl_k5_b21
  | 22, _ => exact shl_k5_b22
  | 23, _ => exact shl_k5_b23
  | 24, _ => exact shl_k5_b24
  | 25, _ => exact shl_k5_b25
  | 26, _ => exact shl_k5_b26
  | 27, _ => exact shl_k5_b27
  | 28, _ => exact shl_k5_b28
  | 29, _ => exact shl_k5_b29
  | 30, _ => exact shl_k5_b30
  | 31, _ => exact shl_k5_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k6_b0 : ShlBit0 6 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b1 : ShlBit0 6 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b2 : ShlBit0 6 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b3 : ShlBit0 6 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b4 : ShlBit0 6 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b5 : ShlBit0 6 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b6 : ShlBit0 6 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b7 : ShlBit0 6 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b8 : ShlBit0 6 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b9 : ShlBit0 6 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b10 : ShlBit0 6 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b11 : ShlBit0 6 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b12 : ShlBit0 6 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b13 : ShlBit0 6 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b14 : ShlBit0 6 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b15 : ShlBit0 6 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b16 : ShlBit0 6 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b17 : ShlBit0 6 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b18 : ShlBit0 6 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b19 : ShlBit0 6 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b20 : ShlBit0 6 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b21 : ShlBit0 6 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b22 : ShlBit0 6 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b23 : ShlBit0 6 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b24 : ShlBit0 6 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b25 : ShlBit0 6 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b26 : ShlBit0 6 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b27 : ShlBit0 6 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b28 : ShlBit0 6 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b29 : ShlBit0 6 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b30 : ShlBit0 6 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k6_b31 : ShlBit0 6 31 := by decide +kernel

theorem ushli0_cert6 : FixShOK Ushli0.cells Ushli0.outs 6 (shlSrc 6) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k6_b0
  | 1, _ => exact shl_k6_b1
  | 2, _ => exact shl_k6_b2
  | 3, _ => exact shl_k6_b3
  | 4, _ => exact shl_k6_b4
  | 5, _ => exact shl_k6_b5
  | 6, _ => exact shl_k6_b6
  | 7, _ => exact shl_k6_b7
  | 8, _ => exact shl_k6_b8
  | 9, _ => exact shl_k6_b9
  | 10, _ => exact shl_k6_b10
  | 11, _ => exact shl_k6_b11
  | 12, _ => exact shl_k6_b12
  | 13, _ => exact shl_k6_b13
  | 14, _ => exact shl_k6_b14
  | 15, _ => exact shl_k6_b15
  | 16, _ => exact shl_k6_b16
  | 17, _ => exact shl_k6_b17
  | 18, _ => exact shl_k6_b18
  | 19, _ => exact shl_k6_b19
  | 20, _ => exact shl_k6_b20
  | 21, _ => exact shl_k6_b21
  | 22, _ => exact shl_k6_b22
  | 23, _ => exact shl_k6_b23
  | 24, _ => exact shl_k6_b24
  | 25, _ => exact shl_k6_b25
  | 26, _ => exact shl_k6_b26
  | 27, _ => exact shl_k6_b27
  | 28, _ => exact shl_k6_b28
  | 29, _ => exact shl_k6_b29
  | 30, _ => exact shl_k6_b30
  | 31, _ => exact shl_k6_b31
  | _ + 32, h => exact absurd h (by omega)

set_option maxRecDepth 100000 in
theorem shl_k7_b0 : ShlBit0 7 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b1 : ShlBit0 7 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b2 : ShlBit0 7 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b3 : ShlBit0 7 3 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b4 : ShlBit0 7 4 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b5 : ShlBit0 7 5 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b6 : ShlBit0 7 6 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b7 : ShlBit0 7 7 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b8 : ShlBit0 7 8 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b9 : ShlBit0 7 9 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b10 : ShlBit0 7 10 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b11 : ShlBit0 7 11 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b12 : ShlBit0 7 12 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b13 : ShlBit0 7 13 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b14 : ShlBit0 7 14 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b15 : ShlBit0 7 15 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b16 : ShlBit0 7 16 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b17 : ShlBit0 7 17 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b18 : ShlBit0 7 18 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b19 : ShlBit0 7 19 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b20 : ShlBit0 7 20 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b21 : ShlBit0 7 21 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b22 : ShlBit0 7 22 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b23 : ShlBit0 7 23 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b24 : ShlBit0 7 24 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b25 : ShlBit0 7 25 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b26 : ShlBit0 7 26 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b27 : ShlBit0 7 27 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b28 : ShlBit0 7 28 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b29 : ShlBit0 7 29 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b30 : ShlBit0 7 30 := by decide +kernel
set_option maxRecDepth 100000 in
theorem shl_k7_b31 : ShlBit0 7 31 := by decide +kernel

theorem ushli0_cert7 : FixShOK Ushli0.cells Ushli0.outs 7 (shlSrc 7) := by
  refine ⟨rfl, fun i hi => ?_⟩
  match i, hi with
  | 0, _ => exact shl_k7_b0
  | 1, _ => exact shl_k7_b1
  | 2, _ => exact shl_k7_b2
  | 3, _ => exact shl_k7_b3
  | 4, _ => exact shl_k7_b4
  | 5, _ => exact shl_k7_b5
  | 6, _ => exact shl_k7_b6
  | 7, _ => exact shl_k7_b7
  | 8, _ => exact shl_k7_b8
  | 9, _ => exact shl_k7_b9
  | 10, _ => exact shl_k7_b10
  | 11, _ => exact shl_k7_b11
  | 12, _ => exact shl_k7_b12
  | 13, _ => exact shl_k7_b13
  | 14, _ => exact shl_k7_b14
  | 15, _ => exact shl_k7_b15
  | 16, _ => exact shl_k7_b16
  | 17, _ => exact shl_k7_b17
  | 18, _ => exact shl_k7_b18
  | 19, _ => exact shl_k7_b19
  | 20, _ => exact shl_k7_b20
  | 21, _ => exact shl_k7_b21
  | 22, _ => exact shl_k7_b22
  | 23, _ => exact shl_k7_b23
  | 24, _ => exact shl_k7_b24
  | 25, _ => exact shl_k7_b25
  | 26, _ => exact shl_k7_b26
  | 27, _ => exact shl_k7_b27
  | 28, _ => exact shl_k7_b28
  | 29, _ => exact shl_k7_b29
  | 30, _ => exact shl_k7_b30
  | 31, _ => exact shl_k7_b31
  | _ + 32, h => exact absurd h (by omega)

end Formal.Net.Compute.GcdD
