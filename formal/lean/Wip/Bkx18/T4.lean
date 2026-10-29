import Wip.Bkx18.Gen
namespace Formal.Cells.OnNetlistArbKappaExact
theorem bern (N D : Int) {p0 q0 p1 q1 : Int} (h0 : p0 * D ≤ q0 * N) (h1 : q1 * N ≤ p1 * D) :
    0 ≤ (q0 * N - p0 * D) * (q0 * N - p0 * D) ∧ 0 ≤ (q0 * N - p0 * D) * (p1 * D - q1 * N) ∧
      0 ≤ (p1 * D - q1 * N) * (p1 * D - q1 * N) :=
  ⟨Int.mul_nonneg (by omega) (by omega), Int.mul_nonneg (by omega) (by omega),
    Int.mul_nonneg (by omega) (by omega)⟩

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

def dW : Arc → Nat
  | .c => 160 | .wSt => 215 | .aSt => 37 | .wQf => 76 | .wQG => 100 | .aG => 37
  | .wGC => 145 | .wAC => 535 | .aC => 45 | .wCf => 195

set_option maxRecDepth 100000 in
theorem wit_test (k : Kappa) (h0 : 18067 * k.den ≤ 100000 * k.num) (h1 : 453 * k.num ≤ 82 * k.den)
    (hP : 0 ≤ -30715 * (k.num : Int) * k.num + 158805 * k.num * k.den - 27690 * k.den * k.den) :
    ∀ e, Scat k ⟨420 * k.den + 955 * k.num, 82 * k.den - 453 * k.num, by have := k.den_pos; omega⟩
      (Ats e) (dW e) := by
  intro e
  have hN := k.num_le
  have hD := k.den_pos
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 18067) (q0 := 100000) (p1 := 82) (q1 := 453) (by omega) (by omega)
  cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, Ats, dW] <;>
  (have hs : 453 * k.num ≤ 82 * k.den := h1
   have hl : k.num ≤ k.den := hN
   constructor <;> apply Int.ofNat_le.mp <;> push_cast [Int.ofNat_sub hs, Int.ofNat_sub hl] <;> grind)
end Formal.Cells.OnNetlistArbKappaExact
