import Formal.Cells.BWitNDefs

/-!
# Probe Bwit (shard B): kernel checks of the driver-bound network on `chB`

`decide +kernel` on every channel (`wireChk`: wires of the bound drivers, sortedness) and
every operator (`opChkB`: links, fork / join C-elements, steer branches and OR, each against
its checker on `chB`'s event lists, with node edge times). Core Lean only.
-/

namespace Formal.Cells.BWit
open Formal.Net.CapNet Formal.Net.CapNet.Gcd

set_option maxRecDepth 100000

theorem bw_c1 : (List.range' 0 240).all wireChk = true := by decide +kernel
theorem bw_c2 : (List.range' 240 225).all wireChk = true := by decide +kernel
/-! Operator checks in chunks of 15 (a 60-operator chunk peaked at 7.1 GB RSS, 20 at 3.8 GB). -/
theorem bop_k0 : (List.range' 0 15).all opChkB = true := by decide +kernel
theorem bop_k1 : (List.range' 15 15).all opChkB = true := by decide +kernel
theorem bop_k2 : (List.range' 30 15).all opChkB = true := by decide +kernel
theorem bop_k3 : (List.range' 45 15).all opChkB = true := by decide +kernel
theorem bop_k4 : (List.range' 60 15).all opChkB = true := by decide +kernel
theorem bop_k5 : (List.range' 75 15).all opChkB = true := by decide +kernel
theorem bop_k6 : (List.range' 90 15).all opChkB = true := by decide +kernel
theorem bop_k7 : (List.range' 105 15).all opChkB = true := by decide +kernel
theorem bop_k8 : (List.range' 120 15).all opChkB = true := by decide +kernel
theorem bop_k9 : (List.range' 135 15).all opChkB = true := by decide +kernel
theorem bop_k10 : (List.range' 150 15).all opChkB = true := by decide +kernel
theorem bop_k11 : (List.range' 165 15).all opChkB = true := by decide +kernel
theorem bop_k12 : (List.range' 180 15).all opChkB = true := by decide +kernel
theorem bop_k13 : (List.range' 195 15).all opChkB = true := by decide +kernel
theorem bop_k14 : (List.range' 210 15).all opChkB = true := by decide +kernel
theorem bop_k15 : (List.range' 225 15).all opChkB = true := by decide +kernel
theorem bop_k16 : (List.range' 240 15).all opChkB = true := by decide +kernel
theorem bop_k17 : (List.range' 255 15).all opChkB = true := by decide +kernel
theorem bop_k18 : (List.range' 270 15).all opChkB = true := by decide +kernel
theorem bop_k19 : (List.range' 285 15).all opChkB = true := by decide +kernel
theorem bop_k20 : (List.range' 300 15).all opChkB = true := by decide +kernel
theorem bop_k21 : (List.range' 315 15).all opChkB = true := by decide +kernel
theorem bop_k22 : (List.range' 330 15).all opChkB = true := by decide +kernel
theorem bop_k23 : (List.range' 345 15).all opChkB = true := by decide +kernel
theorem bop_k24 : (List.range' 360 7).all opChkB = true := by decide +kernel

theorem range'_all' {f : Nat → Bool} {a n : Nat} (h : (List.range' a n).all f = true) :
    ∀ m, a ≤ m → m < a + n → f m = true :=
  fun m h1 h2 => List.all_eq_true.1 h m (List.mem_range'_1.2 ⟨h1, h2⟩)

theorem bop_all (o : Fin NO) : opChkB o.val = true := by
  have := o.isLt
  have hNO : NO = 367 := rfl
  have key : ∀ k, k < 25 → ∀ m, 15 * k ≤ m → m < 15 * k + 15 → m < 367 → opChkB m = true := by
    intro k hk
    match k, hk with
    | 0, _ => exact fun m h1 h2 h3 => range'_all' bop_k0 m (by omega) (by omega)
    | 1, _ => exact fun m h1 h2 h3 => range'_all' bop_k1 m (by omega) (by omega)
    | 2, _ => exact fun m h1 h2 h3 => range'_all' bop_k2 m (by omega) (by omega)
    | 3, _ => exact fun m h1 h2 h3 => range'_all' bop_k3 m (by omega) (by omega)
    | 4, _ => exact fun m h1 h2 h3 => range'_all' bop_k4 m (by omega) (by omega)
    | 5, _ => exact fun m h1 h2 h3 => range'_all' bop_k5 m (by omega) (by omega)
    | 6, _ => exact fun m h1 h2 h3 => range'_all' bop_k6 m (by omega) (by omega)
    | 7, _ => exact fun m h1 h2 h3 => range'_all' bop_k7 m (by omega) (by omega)
    | 8, _ => exact fun m h1 h2 h3 => range'_all' bop_k8 m (by omega) (by omega)
    | 9, _ => exact fun m h1 h2 h3 => range'_all' bop_k9 m (by omega) (by omega)
    | 10, _ => exact fun m h1 h2 h3 => range'_all' bop_k10 m (by omega) (by omega)
    | 11, _ => exact fun m h1 h2 h3 => range'_all' bop_k11 m (by omega) (by omega)
    | 12, _ => exact fun m h1 h2 h3 => range'_all' bop_k12 m (by omega) (by omega)
    | 13, _ => exact fun m h1 h2 h3 => range'_all' bop_k13 m (by omega) (by omega)
    | 14, _ => exact fun m h1 h2 h3 => range'_all' bop_k14 m (by omega) (by omega)
    | 15, _ => exact fun m h1 h2 h3 => range'_all' bop_k15 m (by omega) (by omega)
    | 16, _ => exact fun m h1 h2 h3 => range'_all' bop_k16 m (by omega) (by omega)
    | 17, _ => exact fun m h1 h2 h3 => range'_all' bop_k17 m (by omega) (by omega)
    | 18, _ => exact fun m h1 h2 h3 => range'_all' bop_k18 m (by omega) (by omega)
    | 19, _ => exact fun m h1 h2 h3 => range'_all' bop_k19 m (by omega) (by omega)
    | 20, _ => exact fun m h1 h2 h3 => range'_all' bop_k20 m (by omega) (by omega)
    | 21, _ => exact fun m h1 h2 h3 => range'_all' bop_k21 m (by omega) (by omega)
    | 22, _ => exact fun m h1 h2 h3 => range'_all' bop_k22 m (by omega) (by omega)
    | 23, _ => exact fun m h1 h2 h3 => range'_all' bop_k23 m (by omega) (by omega)
    | 24, _ => exact fun m h1 h2 h3 => range'_all' bop_k24 m (by omega) (by omega)
    | k + 25, hk => exact absurd hk (by omega)
  exact key (o.val / 15) (by omega) o.val (Nat.mul_div_le o.val 15) (by omega) (by omega)

theorem bw_all (c : Fin NC) : wireChk c.val = true := by
  have := c.isLt
  have hNC : NC = 465 := rfl
  rcases Nat.lt_or_ge c.val 240 with h | h
  · exact range'_all' bw_c1 _ (by omega) (by omega)
  · exact range'_all' bw_c2 _ (by omega) (by omega)

end Formal.Cells.BWit
