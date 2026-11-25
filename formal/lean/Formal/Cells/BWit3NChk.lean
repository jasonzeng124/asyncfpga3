import Formal.Cells.BWit3NDefs
import Formal.Cells.BWit2NChk  -- build order only: the kernel-check modules must not build in parallel (memory)

/-!
# Probe Bwit3 (shard B): kernel checks of the arbiter-extended driver-bound network

`decide +kernel` on every channel (`wireChk`: wires of the bound drivers, sortedness) and
every operator (`opChkB`: links, fork / join C-elements, steer branches and OR, each against
its checker on `chB`'s event lists, with node edge times; every bd_mux: both joins, both acknowledges, the OR, both buffers; every bd_arbiter: q, R0, g1, g2 by `combB`, ua1/ua2 by `maB` with the winner table, one theorem per arbiter). Core Lean only.
-/

namespace Formal.Cells.BWit3
open Formal.Net.CapNet Formal.Net.CapNet.Gcd

set_option maxRecDepth 100000

theorem bw_c1 : (List.range' 0 240).all wireChk = true := by decide +kernel
theorem bw_c2 : (List.range' 240 225).all wireChk = true := by decide +kernel
/-! Operator checks in chunks of 15 (a 60-operator chunk peaked at 7.1 GB RSS, 20 at 3.8 GB). -/
theorem bop_k0 : (List.range' 0 15).all opChkN = true := by decide +kernel
theorem bop_k1 : (List.range' 15 15).all opChkN = true := by decide +kernel
theorem bop_k2 : (List.range' 30 15).all opChkN = true := by decide +kernel
theorem bop_k3 : (List.range' 45 15).all opChkN = true := by decide +kernel
theorem bop_k4 : (List.range' 60 15).all opChkN = true := by decide +kernel
theorem bop_k5 : (List.range' 75 15).all opChkN = true := by decide +kernel
theorem bop_k6 : (List.range' 90 15).all opChkN = true := by decide +kernel
theorem bop_k7 : (List.range' 105 15).all opChkN = true := by decide +kernel
theorem bop_k8 : (List.range' 120 15).all opChkN = true := by decide +kernel
theorem bop_k9 : (List.range' 135 15).all opChkN = true := by decide +kernel
theorem bop_k10 : (List.range' 150 15).all opChkN = true := by decide +kernel
theorem bop_k11 : (List.range' 165 15).all opChkN = true := by decide +kernel
theorem bop_k12 : (List.range' 180 15).all opChkN = true := by decide +kernel
theorem bop_k13 : (List.range' 195 15).all opChkN = true := by decide +kernel
theorem bop_k14 : (List.range' 210 15).all opChkN = true := by decide +kernel
theorem bop_k15 : (List.range' 225 15).all opChkN = true := by decide +kernel
theorem bop_k16 : (List.range' 240 15).all opChkN = true := by decide +kernel
theorem bop_k17 : (List.range' 255 15).all opChkN = true := by decide +kernel
theorem bop_k18 : (List.range' 270 15).all opChkN = true := by decide +kernel
theorem bop_k19 : (List.range' 285 15).all opChkN = true := by decide +kernel
theorem bop_k20 : (List.range' 300 15).all opChkN = true := by decide +kernel
theorem bop_k21 : (List.range' 315 15).all opChkN = true := by decide +kernel
theorem bop_k22 : (List.range' 330 15).all opChkN = true := by decide +kernel
theorem bop_k23 : (List.range' 345 15).all opChkN = true := by decide +kernel
theorem bop_k24 : (List.range' 360 7).all opChkN = true := by decide +kernel

theorem range'_all' {f : Nat → Bool} {a n : Nat} (h : (List.range' a n).all f = true) :
    ∀ m, a ≤ m → m < a + n → f m = true :=
  fun m h1 h2 => List.all_eq_true.1 h m (List.mem_range'_1.2 ⟨h1, h2⟩)

theorem bopN_all (o : Fin NO) : opChkN o.val = true := by
  have := o.isLt
  have hNO : NO = 367 := rfl
  have key : ∀ k, k < 25 → ∀ m, 15 * k ≤ m → m < 15 * k + 15 → m < 367 → opChkN m = true := by
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

theorem barb_rest : (List.range NO).all (fun n => arbList.contains n || arbChkN n) = true := by
  decide +kernel

/-! One theorem per arbiter (kernel memory is released between declarations). -/
theorem barb_167 : arbChkN 167 = true := by decide +kernel
theorem barb_169 : arbChkN 169 = true := by decide +kernel
theorem barb_171 : arbChkN 171 = true := by decide +kernel
theorem barb_174 : arbChkN 174 = true := by decide +kernel
theorem barb_178 : arbChkN 178 = true := by decide +kernel
theorem barb_180 : arbChkN 180 = true := by decide +kernel
theorem barb_182 : arbChkN 182 = true := by decide +kernel
theorem barb_184 : arbChkN 184 = true := by decide +kernel
theorem barb_185 : arbChkN 185 = true := by decide +kernel

theorem barb_list : ∀ n ∈ arbList, arbChkN n = true := by
  intro n hn
  simp only [arbList, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact barb_167
  · exact barb_169
  · exact barb_171
  · exact barb_174
  · exact barb_178
  · exact barb_180
  · exact barb_182
  · exact barb_184
  · exact barb_185

theorem barb_all (o : Fin NO) : arbChk o = true := by
  have e : arbChk o = arbChkN o.val := by unfold arbChkN; rw [dif_pos o.isLt]
  rw [e]
  have h1 := List.all_eq_true.1 barb_rest o.val (List.mem_range.2 o.isLt)
  by_cases hm : arbList.contains o.val = true
  · exact barb_list _ (List.contains_iff_mem.1 hm)
  · simp only [hm, Bool.false_or] at h1; exact h1

theorem bw_all (c : Fin NC) : wireChk c.val = true := by
  have := c.isLt
  have hNC : NC = 465 := rfl
  rcases Nat.lt_or_ge c.val 240 with h | h
  · exact range'_all' bw_c1 _ (by omega) (by omega)
  · exact range'_all' bw_c2 _ (by omega) (by omega)

end Formal.Cells.BWit3
