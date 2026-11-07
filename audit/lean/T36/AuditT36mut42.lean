import Formal.Cells.RaceCertPS
namespace Formal.Cells.RaceCertPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecChain Formal.Cells.RaceLinkPS Formal.Net.CViewPS Formal.Cells.ViewPS Formal.Cells.SpecFbChain Formal.Cells.SpecCElemFact Formal.Cells.SpecLatchFact Formal.Cells.ArbViewPS Formal.Cells.CtlChain
theorem race_margin_mut (κ c : ℚ) (hk0 : 0 ≤ κ) (hk : κ ≤ 42 / 100) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    kb.hi ⟨1, κ⟩ c 0 ≤ k1.lo ⟨1, κ⟩ c 4 + k2.lo ⟨1, κ⟩ c 4 + k3.lo ⟨1, κ⟩ c 3 + k4.lo ⟨1, κ⟩ c 3 +
      k5.lo ⟨1, κ⟩ c 4 + kb.lo ⟨1, κ⟩ c 4 := by
  simp only [KRow.lo, KRow.hi, a1, a2, a3, a4, a5, ab4, ab0]
  have L1 := toNat_ge _ |>.trans' (sum_lo_ge (g := 1) (κ := κ) (c := c) [⟨79, 99, 193, 240⟩, ⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨50, 71, 115, 149⟩, ⟨33, 83, 111, 176⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩])
  have L2 := toNat_ge _ |>.trans' (sum_lo_ge (g := 1) (κ := κ) (c := c) [⟨78, 98, 192, 238⟩, ⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩])
  have L3 := toNat_ge _ |>.trans' (sum_lo_ge (g := 1) (κ := κ) (c := c) [⟨133, 165, 329, 408⟩, ⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩])
  have L4 := toNat_ge _ |>.trans' (sum_lo_ge (g := 1) (κ := κ) (c := c) [⟨131, 163, 329, 408⟩, ⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨44, 63, 108, 140⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩])
  have L5 := toNat_ge _ |>.trans' (sum_lo_ge (g := 1) (κ := κ) (c := c) [⟨79, 99, 193, 240⟩, ⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨50, 135, 111, 209⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩])
  have L6 := toNat_ge _ |>.trans' (sum_lo_ge (g := 1) (κ := κ) (c := c) [⟨83, 104, 202, 250⟩, ⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨33, 51, 113, 147⟩, ⟨52, 74, 118, 153⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩])
  have H := sum_hi_le (g := 1) (κ := κ) (c := c) [⟨225, 281, 528, 655⟩, ⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨35, 62, 102, 142⟩, ⟨33, 51, 113, 147⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, lerp, Nat.cast_ofNat, Nat.cast_zero,
    div_one, mul_one] at L1 L2 L3 L4 L5 L6 H
  have Hn := toNat_le H (by
    have : (0 : ℚ) ≤ 1 + κ := by linarith
    have : (0 : ℚ) ≤ 1 - c := by linarith
    positivity)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [← Nat.cast_le (α := ℚ)]
  push_cast
  have hkc : κ * c ≤ 41 / 100 * c := by nlinarith
  nlinarith [L1, L2, L3, L4, L5, L6, Hn, hkc]

end Formal.Cells.RaceCertPS
