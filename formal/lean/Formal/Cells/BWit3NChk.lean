import Formal.Cells.BWit3NDefs

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
theorem bop_c1 : (List.range' 0 60).all opChkN = true := by decide +kernel
theorem bop_c2 : (List.range' 60 60).all opChkN = true := by decide +kernel
theorem bop_c3 : (List.range' 120 60).all opChkN = true := by decide +kernel
theorem bop_c4 : (List.range' 180 60).all opChkN = true := by decide +kernel
theorem bop_c5 : (List.range' 240 60).all opChkN = true := by decide +kernel
theorem bop_c6 : (List.range' 300 67).all opChkN = true := by decide +kernel

theorem range'_all' {f : Nat → Bool} {a n : Nat} (h : (List.range' a n).all f = true) :
    ∀ m, a ≤ m → m < a + n → f m = true :=
  fun m h1 h2 => List.all_eq_true.1 h m (List.mem_range'_1.2 ⟨h1, h2⟩)

theorem bopN_all (o : Fin NO) : opChkN o.val = true := by
  have := o.isLt
  have hNO : NO = 367 := rfl
  rcases Nat.lt_or_ge o.val 60 with h | h
  · exact range'_all' bop_c1 _ (by omega) (by omega)
  rcases Nat.lt_or_ge o.val 120 with h' | h'
  · exact range'_all' bop_c2 _ (by omega) (by omega)
  rcases Nat.lt_or_ge o.val 180 with h'' | h''
  · exact range'_all' bop_c3 _ (by omega) (by omega)
  rcases Nat.lt_or_ge o.val 240 with h3 | h3
  · exact range'_all' bop_c4 _ (by omega) (by omega)
  rcases Nat.lt_or_ge o.val 300 with h4 | h4
  · exact range'_all' bop_c5 _ (by omega) (by omega)
  · exact range'_all' bop_c6 _ (by omega) (by omega)

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
