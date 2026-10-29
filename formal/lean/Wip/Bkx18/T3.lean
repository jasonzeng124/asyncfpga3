import Wip.Bkx18.Gen
namespace Formal.Cells.OnNetlistArbKappaExact
theorem elim2 {w0 w1 a1 b1 a2 b2 : Int} (hw0 : 0 ≤ w0) (hw1 : 0 ≤ w1) (hw : 0 < w0 + w1)
    (hb1 : 0 < b1) (ha2 : 0 < a2) (h1 : w0 * a1 + w1 * b1 ≤ 0) (h2 : w0 * a2 + w1 * b2 ≤ 0) :
    a2 * b1 ≤ a1 * b2 := by
  by_cases hb2 : 0 < b2
  · exfalso
    have p1 : 0 ≤ w1 * b2 := Int.mul_nonneg hw1 (Int.le_of_lt hb2)
    have p2 : 0 ≤ w0 * a2 := Int.mul_nonneg hw0 (Int.le_of_lt ha2)
    rcases Int.lt_or_eq_of_le hw0 with h0 | h0
    · have := Int.mul_pos h0 ha2; omega
    · subst h0
      have : 0 < w1 := by omega
      have := Int.mul_pos this hb2; omega
  · have nb2 : 0 ≤ -b2 := by omega
    have e1 := Int.mul_le_mul_of_nonneg_left h1 nb2
    have e2 := Int.mul_le_mul_of_nonneg_left h2 (Int.le_of_lt hb1)
    have e3 : w0 * (a2 * b1 - a1 * b2) ≤ 0 := by grind
    rcases Int.lt_or_eq_of_le hw0 with h0 | h0
    · apply Classical.byContradiction; intro hx
      have := Int.mul_pos h0 (show 0 < a2 * b1 - a1 * b2 by omega); omega
    · subst h0
      have : 0 < w1 := by omega
      have := Int.mul_pos this hb1; omega

def Ats : Tab
  | .c => ⟨160, 488, by decide⟩
  | .wSt => ⟨262, 638, by decide⟩
  | .aSt => ⟨45, 100, by decide⟩
  | .wQf => ⟨76, 288, by decide⟩
  | .wQG => ⟨122, 325, by decide⟩
  | .aG => ⟨45, 100, by decide⟩
  | .wGC => ⟨176, 503, by decide⟩
  | .wAC => ⟨453, 955, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨195, 677, by decide⟩

set_option maxRecDepth 100000 in
/-- kill: vector forced, P < 0, κ small. -/
theorem kill_test {k : Kappa} (hk : k.num * 1000 < 181 * k.den)
    (hP : -30715 * (k.num : Int) * k.num + 158805 * k.num * k.den - 27690 * k.den * k.den < 0)
    (c : Corner) (h1 : Scat k c (Ats .wQG) 100) (h2 : Scat k c (Ats .wAC) 535) : False := by
  obtain ⟨w0, w1, hw⟩ := c
  simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, Ats] at h1 h2
  have hN := k.num_le
  generalize k.num = N at *
  generalize k.den = D at *
  obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Nat.add_sub_cancel_left] at h1 h2
  have j1 := Int.ofNat_le.mpr h1.1
  have j2 := Int.ofNat_le.mpr h2.2
  push_cast at j1 j2
  simp only [Int.natCast_add] at hP
  have i1 : (w0:Int) * ((L:Int)*122 - (N+L)*100) + (w1:Int)*((L:Int)*325 - (N+L)*100) ≤ 0 := by
    grind
  have i2 : (w0:Int) * (((N:Int)+L)*535 - (N+N+L)*453) + (w1:Int)*(((N:Int)+L)*535 - (N+N+L)*955) ≤ 0 := by
    grind
  have := elim2 (by omega) (by omega) (by omega) (by omega) (by omega) i1 i2
  grind
end Formal.Cells.OnNetlistArbKappaExact
