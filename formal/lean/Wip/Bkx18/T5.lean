import Wip.Bkx18.Gen
namespace Formal.Cells.OnNetlistArbKappaExact
open Formal.Cells.ArbA0Fork
set_option maxRecDepth 100000

/-! ### Seed 1, client 2, `cons` -/

/-- Arc endpoints (F, S) ps, seed 1, client 2, `cons` (= `OnNetlistArbKappa.A_s1c2_cons`). -/
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

theorem A_s1c2_cons_pos : ∀ e, 0 < (A_s1c2_cons e).F := by intro e; cases e <;> decide

/-- Box chain over `[0, 1]` (16 boxes) at `u = 15/83`. -/
def pts_s1c2_cons : List Pt := [(4279514633, 15452663), (4257776141, 37191155), (16915165939, 264703245), (16770242659, 409626525), (8312659689, 277274903), (16364457473, 815411711), (999228559, 74513265), (7747458895, 842475697), (14770301387, 2409567797), (13755838423, 3424030761), (12335590273, 4844278911), (10364633657, 6815235527), (3805545663, 4784388929), (3727147407, 13452721777), (0, 1)]
def sp_s1c2_cons : List (List Nat) := [[215, 37, 100, 37, 145, 535]]

theorem chain_s1c2_cons : chainOK A_s1c2_cons 15 83 sp_s1c2_cons (1, 0) ((4286760797, 8206499) :: pts_s1c2_cons) = true := by
  decide +kernel
theorem last_s1c2_cons : lastPt (4286760797, 8206499) pts_s1c2_cons = (0, 1) := by decide +kernel

/-- `P(κ)·den²` for the binding vector `[215, 37, 100, 37, 145]`, late 535, binding early arc `wQG`:
the vector is realisable at some corner iff `P ≥ 0`. Its root in `[0, 1]` is
κ_ex ≈ 0.1806787261 (irrational: discriminant 21817034625 is not a square). -/
def P_s1c2_cons (k : Kappa) : Int :=
  -30715 * (k.num : Int) * k.num + 158805 * (k.num : Int) * k.den + -27690 * (k.den : Int) * k.den
/-- **κ < κ_ex** (`P < 0` below `u = 15/83`). -/
def Below_s1c2_cons (k : Kappa) : Prop := k.num * 83 < 15 * k.den ∧ P_s1c2_cons k < 0
instance (k : Kappa) : Decidable (Below_s1c2_cons k) := inferInstanceAs (Decidable (_ ∧ _))

theorem kill_s1c2_cons {k : Kappa} (hb : Below_s1c2_cons k) (c : Corner) (h1 : Scat k c (A_s1c2_cons .wQG) 100)
    (h2 : Scat k c (A_s1c2_cons .wAC) 535) : False := by
  obtain ⟨hk, hP⟩ := hb
  unfold P_s1c2_cons at hP
  obtain ⟨w0, w1, hw⟩ := c
  simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s1c2_cons] at h1 h2
  have hN := k.num_le
  generalize k.num = N at *
  generalize k.den = D at *
  obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Nat.add_sub_cancel_left] at h1 h2
  have j1 := Int.ofNat_le.mpr h1.1
  have j2 := Int.ofNat_le.mpr h2.2
  push_cast at j1 j2
  simp only [Int.natCast_add] at hP
  have i1 : (w0 : Int) * ((L : Int) * 122 - (N + L) * 100) + (w1 : Int) * ((L : Int) * 325 - (N + L) * 100) ≤ 0 := by
    grind
  have i2 : (w0 : Int) * (((N : Int) + L) * 535 - (N + N + L) * 453) +
      (w1 : Int) * (((N : Int) + L) * 535 - (N + N + L) * 955) ≤ 0 := by
    grind
  have := elim2 (by omega) (by omega) (by omega) (by omega) (by omega) i1 i2
  grind

theorem safe_s1c2_cons (k : Kappa) (H_BELOW : Below_s1c2_cons k) (c : Corner) (d : Arc → Nat)
    (H_SCAT : ∀ e, Scat k c (A_s1c2_cons e) (d e)) : Safe F2 G2 true (dlOf d) := by
  apply safe2_of_le
  rcases cover_sound (A_s1c2_cons_pos) (by decide) (by decide) chain_s1c2_cons last_s1c2_cons H_BELOW.1 c d H_SCAT with h | h
  · exact h
  · exfalso
    simp only [sp_s1c2_cons, vec, List.mem_singleton, List.cons.injEq, and_true] at h
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h
    have s1 := H_SCAT .wQG
    have s2 := H_SCAT .wAC
    rw [e3] at s1
    rw [e6] at s2
    exact kill_s1c2_cons H_BELOW c s1 s2

/-- The violating assignment (binding vector, other arcs at their fast endpoint). -/
def dW_s1c2_cons : Arc → Nat
  .c => 160 | .wSt => 215 | .aSt => 37 | .wQf => 76 | .wQG => 100 | .aG => 37 | .wGC => 145 | .wAC => 535 | .aC => 45 | .wCf => 195

/-- Between `u` and `κ_fix = 82/453`, `P ≥ 0` (Bernstein certificate). -/
theorem pos_s1c2_cons (k : Kappa) (hfix : k.num * 453 < 82 * k.den) (hb : ¬ Below_s1c2_cons k) : 0 ≤ P_s1c2_cons k := by
  unfold Below_s1c2_cons at hb
  by_cases hu : k.num * 83 < 15 * k.den
  · have := (not_and.mp hb) hu
    omega
  · unfold P_s1c2_cons
    obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 15) (q0 := 83) (p1 := 82) (q1 := 453)
      (by omega) (by omega)
    grind

/-- `P ≥ 0` forces `κ ≥ κ_lo = 6443/35662` (`P < 0` on `[0, κ_lo)`, Bernstein certificate). -/
theorem lo_s1c2_cons (k : Kappa) (hP : 0 ≤ P_s1c2_cons k) : 6443 * k.den ≤ 35662 * k.num := by
  apply Classical.byContradiction; intro h
  unfold P_s1c2_cons at hP
  have hv : (0 : Int) < 6443 * (k.den : Int) - 35662 * k.num := by omega
  have hv2 := Int.mul_pos hv hv
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 0) (q0 := 1) (p1 := 6443) (q1 := 35662)
    (by omega) (by omega)
  grind

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
  cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s1c2_cons, dW_s1c2_cons] <;>
  (constructor <;> apply Int.ofNat_le.mp <;>
    push_cast [Int.ofNat_sub hs0, Int.ofNat_sub hN] <;> grind)

theorem unsafe_s1c2_cons (k : Kappa) (H_KAPPA : ¬ Below_s1c2_cons k) :
    ∃ c d, (∀ e, Scat k c (A_s1c2_cons e) (d e)) ∧ ¬ Safe F2 G2 true (dlOf d) := by
  by_cases hfix : 82 * k.den ≤ k.num * 453
  · refine ⟨Corner.fast, dW_s1c2_cons, ?_, not_safe2 (by decide) (by decide) (by decide)⟩
    intro e; have := k.num_le
    cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, Corner.fast, A_s1c2_cons, dW_s1c2_cons] <;> omega
  · have hP := pos_s1c2_cons k (by omega) H_KAPPA
    have hlo := lo_s1c2_cons k hP
    have hD := k.den_pos
    exact ⟨_, dW_s1c2_cons, wit_s1c2_cons k hlo (by omega) hP (by omega), not_safe2 (by decide) (by decide) (by decide)⟩

/-- **Exact threshold, seed 1, client 2, `cons`.** Every assignment within κ at every corner is
safe iff `Below_s1c2_cons κ` (i.e. κ < κ_ex ≈ 0.1806787261); otherwise a violating whole-ps assignment exists. -/
theorem exact_s1c2_cons (k : Kappa) :
    (∀ c d, (∀ e, Scat k c (A_s1c2_cons e) (d e)) → Safe F2 G2 true (dlOf d)) ↔ Below_s1c2_cons k := by
  constructor
  · intro hs; apply Classical.byContradiction; intro hb
    obtain ⟨c, d, h1, h2⟩ := unsafe_s1c2_cons k hb
    exact h2 (hs c d h1)
  · intro hb c d h; exact safe_s1c2_cons k hb c d h

/-- Bracket: κ_ex ∈ (90339363/500000000, 1806787261/10000000000]. -/
theorem bracket_s1c2_cons : Below_s1c2_cons ⟨90339363, 500000000, by decide, by decide⟩ ∧
    ¬ Below_s1c2_cons ⟨1806787261, 10000000000, by decide, by decide⟩ := by decide
theorem nonvac_s1c2_cons : Below_s1c2_cons Kappa.zero := by decide

/-! ### Seed 2, client 2, `cons` -/

/-- Arc endpoints (F, S) ps, seed 2, client 2, `cons` (= `OnNetlistArbKappa.A_s2c2_cons`). -/
def A_s2c2_cons : Tab
  | .c => ⟨172, 522, by decide⟩
  | .wSt => ⟨225, 578, by decide⟩
  | .aSt => ⟨45, 100, by decide⟩
  | .wQf => ⟨76, 288, by decide⟩
  | .wQG => ⟨202, 525, by decide⟩
  | .aG => ⟨45, 100, by decide⟩
  | .wGC => ⟨325, 785, by decide⟩
  | .wAC => ⟨466, 940, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨76, 288, by decide⟩

theorem A_s2c2_cons_pos : ∀ e, 0 < (A_s2c2_cons e).F := by intro e; cases e <;> decide

/-- Box chain over `[0, 1]` (15 boxes) at `u = 94/325`. -/
def pts_s2c2_cons : List Pt := [(17145614287, 34254897), (17061274577, 118594607), (8474410815, 115523777), (16808255447, 371613737), (8305731395, 284203197), (8151108593, 438825999), (15908631873, 1271237311), (7659126951, 930807641), (14418630329, 2761238855), (13125421441, 4054447743), (11241834583, 5938034601), (4271481931, 4318452661), (4635223963, 12544645221), (0, 1)]
def sp_s2c2_cons : List (List Nat) := []

theorem chain_s2c2_cons : chainOK A_s2c2_cons 94 325 sp_s2c2_cons (1, 0) ((4293431881, 1535415) :: pts_s2c2_cons) = true := by
  decide +kernel
theorem last_s2c2_cons : lastPt (4293431881, 1535415) pts_s2c2_cons = (0, 1) := by decide +kernel

/-- κ < κ_ex = 94/325 ≈ 0.2892307692 (rational: attained at the fast corner). -/
def Below_s2c2_cons (k : Kappa) : Prop := k.num * 325 < 94 * k.den
instance (k : Kappa) : Decidable (Below_s2c2_cons k) := inferInstanceAs (Decidable (_ < _))

theorem safe_s2c2_cons (k : Kappa) (H_BELOW : Below_s2c2_cons k) (c : Corner) (d : Arc → Nat)
    (H_SCAT : ∀ e, Scat k c (A_s2c2_cons e) (d e)) : Safe F2 G2 true (dlOf d) := by
  apply safe2_of_le
  rcases cover_sound (A_s2c2_cons_pos) (by decide) (by decide) chain_s2c2_cons last_s2c2_cons H_BELOW c d H_SCAT with h | h
  · exact h
  · simp [sp_s2c2_cons] at h

/-- The violating assignment at the fast corner (early arcs at their whole-ps floor, late at 600). -/
def dW_s2c2_cons : Arc → Nat
  .c => 172 | .wSt => 160 | .aSt => 32 | .wQf => 76 | .wQG => 144 | .aG => 32 | .wGC => 231 | .wAC => 600 | .aC => 45 | .wCf => 76

theorem unsafe_s2c2_cons (k : Kappa) (H_KAPPA : ¬ Below_s2c2_cons k) :
    ∃ c d, (∀ e, Scat k c (A_s2c2_cons e) (d e)) ∧ ¬ Safe F2 G2 true (dlOf d) := by
  unfold Below_s2c2_cons at H_KAPPA
  refine ⟨Corner.fast, dW_s2c2_cons, ?_, not_safe2 (by decide) (by decide) (by decide)⟩
  intro e; have := k.num_le
  cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, Corner.fast, A_s2c2_cons, dW_s2c2_cons] <;> omega

/-- **Exact threshold, seed 2, client 2, `cons`.** Every assignment within κ at every corner is
safe iff `Below_s2c2_cons κ` (i.e. κ < κ_ex ≈ 0.2892307692); otherwise a violating whole-ps assignment exists. -/
theorem exact_s2c2_cons (k : Kappa) :
    (∀ c d, (∀ e, Scat k c (A_s2c2_cons e) (d e)) → Safe F2 G2 true (dlOf d)) ↔ Below_s2c2_cons k := by
  constructor
  · intro hs; apply Classical.byContradiction; intro hb
    obtain ⟨c, d, h1, h2⟩ := unsafe_s2c2_cons k hb
    exact h2 (hs c d h1)
  · intro hb c d h; exact safe_s2c2_cons k hb c d h

/-- Bracket: κ_ex ∈ (3759999987/13000000000, 94/325]. -/
theorem bracket_s2c2_cons : Below_s2c2_cons ⟨3759999987, 13000000000, by decide, by decide⟩ ∧
    ¬ Below_s2c2_cons ⟨94, 325, by decide, by decide⟩ := by decide
theorem nonvac_s2c2_cons : Below_s2c2_cons Kappa.zero := by decide


end Formal.Cells.OnNetlistArbKappaExact
