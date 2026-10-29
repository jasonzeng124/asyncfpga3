import Wip.Bkx18.Gen
namespace Formal.Cells.OnNetlistArbKappaExact
set_option maxRecDepth 100000

def A_s1c2_cons : Tab
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

def P_s1c2_cons (k : Kappa) : Int :=
  -30715 * (k.num : Int) * k.num + 158805 * (k.num : Int) * k.den + -27690 * (k.den : Int) * k.den
/-- **κ < κ_ex** (`P < 0` below `u = 15/83`). -/
def Below_s1c2_cons (k : Kappa) : Prop := k.num * 83 < 15 * k.den ∧ P_s1c2_cons k < 0
instance (k : Kappa) : Decidable (Below_s1c2_cons k) := inferInstanceAs (Decidable (_ ∧ _))

def dW_s1c2_cons : Arc → Nat
  | .c => 160 | .wSt => 215 | .aSt => 37 | .wQf => 76 | .wQG => 100 | .aG => 37 | .wGC => 145 | .wAC => 535 | .aC => 45 | .wCf => 195

/-- On `[κ_lo, κ_fix]` with `P ≥ 0`: the binding vector is realised at the corner where the
late arc is exactly at `(1+κ)·nominal` (`w0 = (den+num)·955 − den·535`, `w1 = den·535 − (den+num)·453`). -/
theorem wit_s1c2_cons (k : Kappa) (hlo : 6443 * k.den ≤ 35662 * k.num) (hfix : k.num * 453 ≤ 82 * k.den)
    (hP : 0 ≤ P_s1c2_cons k) (hpos : 0 < (420 * k.den + 955 * k.num) + (82 * k.den - 453 * k.num)) :
    ∀ e, Scat k ⟨420 * k.den + 955 * k.num, 82 * k.den - 453 * k.num, hpos⟩ (A_s1c2_cons e) (dW_s1c2_cons e) := by
  intro e
  have hN := k.num_le
  have hD := k.den_pos
  unfold P_s1c2_cons at hP
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 6443) (q0 := 35662) (p1 := 82) (q1 := 453)
    (by omega) (by omega)
  have hs0 : 453 * k.num ≤ 82 * k.den := by omega
  trace_state
  cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s1c2_cons, dW_s1c2_cons] <;>
  (constructor <;> apply Int.ofNat_le.mp <;>
    push_cast [Int.ofNat_sub hs0, Int.ofNat_sub hN] <;> grind)


end Formal.Cells.OnNetlistArbKappaExact
