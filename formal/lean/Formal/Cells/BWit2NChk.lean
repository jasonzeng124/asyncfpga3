import Formal.Cells.BWit2NDefs
import Formal.Cells.BWitNChk  -- build order only: the kernel-check modules must not build in parallel (memory)

/-!
# Probe Bwit2 (shard B): kernel checks of the mux-extended driver-bound network

`decide +kernel` on every channel (`wireChk`: wires of the bound drivers, sortedness) and
every operator (`opChkB`: links, fork / join C-elements, steer branches and OR, each against
its checker on `chB`'s event lists, with node edge times; every bd_mux: both joins, both acknowledges, the OR, both buffers). Core Lean only.
-/

namespace Formal.Cells.BWit2
open Formal.Net.CapNet Formal.Net.CapNet.Gcd

set_option maxRecDepth 100000

theorem bw_c1 : (List.range' 0 240).all wireChk = true := by decide +kernel
theorem bw_c2 : (List.range' 240 225).all wireChk = true := by decide +kernel
theorem bop_c1 : (List.range' 0 60).all opChkB = true := by decide +kernel
theorem bop_c2 : (List.range' 60 60).all opChkB = true := by decide +kernel
theorem bop_c3 : (List.range' 120 60).all opChkB = true := by decide +kernel
theorem bop_c4 : (List.range' 180 60).all opChkB = true := by decide +kernel
theorem bop_c5 : (List.range' 240 60).all opChkB = true := by decide +kernel
theorem bop_c6 : (List.range' 300 67).all opChkB = true := by decide +kernel

theorem range'_all' {f : Nat → Bool} {a n : Nat} (h : (List.range' a n).all f = true) :
    ∀ m, a ≤ m → m < a + n → f m = true :=
  fun m h1 h2 => List.all_eq_true.1 h m (List.mem_range'_1.2 ⟨h1, h2⟩)

theorem bop_all (o : Fin NO) : opChkB o.val = true := by
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

theorem bw_all (c : Fin NC) : wireChk c.val = true := by
  have := c.isLt
  have hNC : NC = 465 := rfl
  rcases Nat.lt_or_ge c.val 240 with h | h
  · exact range'_all' bw_c1 _ (by omega) (by omega)
  · exact range'_all' bw_c2 _ (by omega) (by omega)

end Formal.Cells.BWit2
