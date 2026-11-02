import Formal.Net.CViewPS.P1Chk0
import Formal.Net.CViewPS.P1Chk1
import Formal.Net.CViewPS.P1Chk2
import Formal.Net.CViewPS.P1Chk3
import Formal.Net.CViewPS.P1Chk4
import Formal.Net.CViewPS.P1Chk5
import Formal.Net.CViewPS.P1Chk6
import Formal.Net.CViewPS.P1Chk7

/-!
# Zero pairs at g = 1, κ = 0: only the reset length remains (shard C)

`correct_n0` at `p1 = (g = 1, κ = 0)` (every arc delay in its corner-`c` window, any corner): its delay
hypotheses are discharged by the kernel (Nat sums of prjxray numbers over the island's 414 gates,
`P1Chk*.lean`), so the only remaining hypothesis is the reset length.
-/

namespace Formal.Net.CViewPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecSettle Formal.Timing.SpecChain
  Formal.Timing.SpecChainM Formal.Timing.ChunkCM Formal.Timing.Huffman Formal.Timing.SpecLoop
  Formal.Timing.Island

theorem p1_ok : islandList.all p1OK = true := by
  simp only [islandList, List.all_append, p1_0_ok, p1_1_ok, p1_2_ok, p1_3_ok, p1_4_ok, p1_5_ok, p1_6_ok, p1_7_ok, Bool.and_self]

set_option maxRecDepth 100000 in
theorem isl_rst : resetList.all (fun r => !(memI r.1) || decide (sumMaxN (arcsPS r.1 r.2.1) ≤ A1)) = true := by
  decide +kernel

/-- **`Correct` for zero pairs at g = 1, κ = 0, for any reset of at least `A1 + 87·M1 + 1` ps
(≈ 353 ns).** -/
theorem correct_n0_p1 (R su Δo : Nat) (hR : A1 + 87 * M1 + 1 ≤ R) :
    ∀ (x : Beh) (va vb : Nat → Nat), Behaves p1 (circuit net boundary) x →
      Env x boundary R su Δo (some 0) va vb → Correct x boundary R Δo (some 0) va vb := by
  have mem : ∀ w, memI w = true → ∃ e ∈ islandList, e.1 = w := by
    intro w hw
    obtain ⟨e, he, h⟩ := List.any_eq_true.mp hw
    exact ⟨e, he, by simpa using h⟩
  apply correct_n0 sane_p1 R su Δo M1 A1
  · intro w hw
    obtain ⟨e, he, rfl⟩ := mem w hw
    have := List.all_eq_true.mp p1_ok e he
    simp only [p1OK, Bool.and_eq_true, decide_eq_true_eq] at this
    simp only [startPS, cStart_p1]; exact this.1.1
  · intro w hw i hi
    obtain ⟨e, he, rfl⟩ := mem w hw
    have := List.all_eq_true.mp p1_ok e he
    simp only [p1OK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at this
    rw [sumMax_p1]; exact this.1.2 i hi
  · intro w hw j hj
    obtain ⟨e, he, rfl⟩ := mem w hw
    have := List.all_eq_true.mp p1_ok e he
    simp only [p1OK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at this
    rw [sumMin_p1]; exact this.2 j hj
  · intro r hr hm
    have := List.all_eq_true.mp isl_rst r hr
    simp only [hm, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
    rw [sumMax_p1]; exact this
  · exact hR

end Formal.Net.CViewPS
