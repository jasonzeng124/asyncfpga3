import Formal.Cells.ArbA0Fork

namespace Formal.Cells.OnNetlistArbKappaExact

open Formal.Cells.ArbA0Fork

/-! ## 0. A's corner model, restated core-only (verbatim definitions of
`Formal.Core.Substrate.CornerNat` §1) -/

structure Kappa where
  num : Nat
  den : Nat
  den_pos : 0 < den
  num_le : num ≤ den
  deriving DecidableEq, Repr

namespace Kappa
def lo (k : Kappa) : Nat := k.den - k.num
def hi (k : Kappa) : Nat := k.den + k.num
end Kappa

structure CArc where
  F : Nat
  S : Nat
  F_le_S : F ≤ S
  deriving DecidableEq, Repr

structure Corner where
  w0 : Nat
  w1 : Nat
  pos : 0 < w0 + w1
  deriving DecidableEq, Repr

namespace Corner
def W (c : Corner) : Nat := c.w0 + c.w1
def fast : Corner := ⟨1, 0, by decide⟩
def slow : Corner := ⟨0, 1, by decide⟩
end Corner

def nom (c : Corner) (a : CArc) : Nat := c.w0 * a.F + c.w1 * a.S

def Scat (k : Kappa) (c : Corner) (a : CArc) (d : Nat) : Prop :=
  k.lo * nom c a ≤ k.den * c.W * d ∧ k.den * c.W * d ≤ k.hi * nom c a

instance (k : Kappa) (c : Corner) (a : CArc) (d : Nat) : Decidable (Scat k c a d) :=
  inferInstanceAs (Decidable (_ ∧ _))

inductive Arc
  | c | wSt | aSt | wQf | wQG | aG | wGC | wAC | aC | wCf
  deriving DecidableEq, Repr

def dlOf (d : Arc → Nat) : Dl :=
  { c := d .c, wSt := d .wSt, pSt := 0, aSt := d .aSt, wQf := d .wQf, pQf := 0,
    wQG := d .wQG, pQG := 0, aG := d .aG, wGC := d .wGC, pGC := 0, wAC := d .wAC,
    pAC := 0, aC := d .aC, wCf := d .wCf, pCf := 0 }

/-! ## 1. Gate level: the fork inequality is exactly safety -/

theorem safe1_of_le {d : Arc → Nat} (h : d .wAC ≤ d .wSt + d .aSt + d .wQG + d .aG + d .wGC) :
    Safe F1 G1 false (dlOf d) := fun _ _ _ _ _ R =>
  (client1_iff R).2 (by simp only [Dl.late, Dl.early, dlOf]; omega)

theorem safe2_of_le {d : Arc → Nat} (h : d .wAC ≤ d .wSt + d .aSt + d .wQG + d .aG + d .wGC) :
    Safe F2 G2 true (dlOf d) := fun _ _ _ _ _ R =>
  (client2_iff R).2 (by simp only [Dl.late, Dl.early, dlOf]; omega)

theorem not_safe1 {d : Arc → Nat} (h : d .wSt + d .aSt + d .wQG + d .aG + d .wGC < d .wAC)
    (hq : 0 < d .aSt + d .wQf) (hc : 0 < d .aC + d .wCf) : ¬ Safe F1 G1 false (dlOf d) := by
  intro hs
  obtain ⟨a0, q, g, A, R⟩ := run_exists F1 G1 true (dlOf d) 1 F1_hold F1_go G1_vals.1
    (by decide) (by simp only [Dl.dQf, dlOf]; omega) (by simp only [Dl.dCf, dlOf]; omega)
  have := (client1_iff R).1 (hs 1 a0 q g A R)
  simp only [Dl.late, Dl.early, dlOf] at this
  omega

theorem not_safe2 {d : Arc → Nat} (h : d .wSt + d .aSt + d .wQG + d .aG + d .wGC < d .wAC)
    (hq : 0 < d .aSt + d .wQf) (hc : 0 < d .aC + d .wCf) : ¬ Safe F2 G2 true (dlOf d) := by
  intro hs
  obtain ⟨a0, q, g, A, R⟩ := run_exists F2 G2 false (dlOf d) 1 F2_hold F2_go G2_vals.1
    (by decide) (by simp only [Dl.dQf, dlOf]; omega) (by simp only [Dl.dCf, dlOf]; omega)
  have := (client2_iff R).1 (hs 1 a0 q g A R)
  simp only [Dl.late, Dl.early, dlOf] at this
  omega

/-! ## 2. Arithmetic lemmas -/

/-- Ceiling division. -/
def cdiv (a b : Nat) : Nat := (a + (b - 1)) / b

theorem cdiv_le {a b x : Nat} (hb : 0 < b) (h : a ≤ b * x) : cdiv a b ≤ x := by
  unfold cdiv
  have : (a + (b - 1)) / b < x + 1 := by
    rw [Nat.div_lt_iff_lt_mul hb, Nat.add_mul, Nat.one_mul, Nat.mul_comm x b]; omega
  omega

theorem le_div_of {a b x : Nat} (hb : 0 < b) (h : b * x ≤ a) : x ≤ a / b := by
  rw [Nat.le_div_iff_mul_le hb, Nat.mul_comm]; exact h

/-- Corner order `ca ≤ c` (as fractions `w1 / W`). -/
def CLe (ca c : Corner) : Prop := ca.w1 * c.W ≤ c.w1 * ca.W

/-- The nominal delay is monotone in the corner (scaled form). -/
theorem nom_mono {ca c : Corner} (h : CLe ca c) (a : CArc) :
    nom ca a * c.W ≤ nom c a * ca.W := by
  obtain ⟨F, S, hFS⟩ := a
  obtain ⟨a0, a1, _⟩ := ca
  obtain ⟨w0, w1, _⟩ := c
  simp only [CLe, Corner.W, nom] at h ⊢
  obtain ⟨Δ, rfl⟩ := Nat.exists_eq_add_of_le hFS
  have := Nat.mul_le_mul_left Δ h
  grind

/-- Lower chain: scatter at `c ≥ ca`, `κ ≤ u` give the bound at `(ca, u)`. -/
theorem chain_lo {L n Dk Wc d Lu Du na Wa : Nat} (hpos : 0 < Dk * Wc)
    (h1 : L * n ≤ Dk * Wc * d) (h2 : Lu * Dk ≤ L * Du) (h3 : na * Wc ≤ n * Wa) :
    Lu * na ≤ Du * Wa * d := by
  have e1 : (Lu * Dk) * (na * Wc) ≤ (L * Du) * (n * Wa) := Nat.mul_le_mul h2 h3
  have e2 : (L * n) * (Du * Wa) ≤ (Dk * Wc * d) * (Du * Wa) := Nat.mul_le_mul_right _ h1
  have e3 : (Dk * Wc) * (Lu * na) ≤ (Dk * Wc) * (Du * Wa * d) := by
    have q1 : (Dk * Wc) * (Lu * na) = (Lu * Dk) * (na * Wc) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have q2 : (L * Du) * (n * Wa) = (L * n) * (Du * Wa) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have q3 : (Dk * Wc * d) * (Du * Wa) = (Dk * Wc) * (Du * Wa * d) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    omega
  exact Nat.le_of_mul_le_mul_left e3 hpos

/-- Upper chain: scatter at `c ≤ cb`, `κ ≤ u`. -/
theorem chain_hi {H n Dk Wc d Hu Du nb Wb : Nat} (hpos : 0 < Dk * Wc)
    (h1 : Dk * Wc * d ≤ H * n) (h2 : H * Du ≤ Hu * Dk) (h3 : n * Wb ≤ nb * Wc) :
    Du * Wb * d ≤ Hu * nb := by
  have e1 : (H * Du) * (n * Wb) ≤ (Hu * Dk) * (nb * Wc) := Nat.mul_le_mul h2 h3
  have e2 : (Dk * Wc * d) * (Du * Wb) ≤ (H * n) * (Du * Wb) := Nat.mul_le_mul_right _ h1
  have e3 : (Dk * Wc) * (Du * Wb * d) ≤ (Dk * Wc) * (Hu * nb) := by
    have q1 : (Dk * Wc) * (Du * Wb * d) = (Dk * Wc * d) * (Du * Wb) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have q2 : (H * n) * (Du * Wb) = (H * Du) * (n * Wb) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have q3 : (Hu * Dk) * (nb * Wc) = (Dk * Wc) * (Hu * nb) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    omega
  exact Nat.le_of_mul_le_mul_left e3 hpos


/-- Strict lower chain (`κ < u`). -/
theorem chain_lo_s {L n Dk Wc d Lu Du na Wa : Nat} (hpos : 0 < Dk * Wc) (hna : 0 < na * Wc)
    (h1 : L * n ≤ Dk * Wc * d) (h2 : Lu * Dk < L * Du) (h3 : na * Wc ≤ n * Wa) :
    Lu * na < Du * Wa * d := by
  have e1 : (Lu * Dk) * (na * Wc) < (L * Du) * (n * Wa) :=
    Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right h2 hna) (Nat.mul_le_mul_left _ h3)
  have e2 : (L * n) * (Du * Wa) ≤ (Dk * Wc * d) * (Du * Wa) := Nat.mul_le_mul_right _ h1
  have e3 : (Dk * Wc) * (Lu * na) < (Dk * Wc) * (Du * Wa * d) := by
    have q1 : (Dk * Wc) * (Lu * na) = (Lu * Dk) * (na * Wc) := by
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    have q2 : (L * Du) * (n * Wa) = (L * n) * (Du * Wa) := by
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    have q3 : (Dk * Wc * d) * (Du * Wa) = (Dk * Wc) * (Du * Wa * d) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    omega
  exact Nat.lt_of_mul_lt_mul_left e3

/-- Strict upper chain (`κ < u`). -/
theorem chain_hi_s {H n Dk Wc d Hu Du nb Wb : Nat} (hpos : 0 < Dk * Wc) (hnb : 0 < nb * Wc)
    (h1 : Dk * Wc * d ≤ H * n) (h2 : H * Du < Hu * Dk) (h3 : n * Wb ≤ nb * Wc) :
    Du * Wb * d < Hu * nb := by
  have e1 : (H * Du) * (n * Wb) < (Hu * Dk) * (nb * Wc) :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ h3) (Nat.mul_lt_mul_of_pos_right h2 hnb)
  have e2 : (Dk * Wc * d) * (Du * Wb) ≤ (H * n) * (Du * Wb) := Nat.mul_le_mul_right _ h1
  have e3 : (Dk * Wc) * (Du * Wb * d) < (Dk * Wc) * (Hu * nb) := by
    have q1 : (Dk * Wc) * (Du * Wb * d) = (Dk * Wc * d) * (Du * Wb) := by
      simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    have q2 : (H * n) * (Du * Wb) = (H * Du) * (n * Wb) := by
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    have q3 : (Hu * Dk) * (nb * Wc) = (Dk * Wc) * (Hu * nb) := by
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    omega
  exact Nat.lt_of_mul_lt_mul_left e3

/-! ## 3. Boxes of corners -/

/-- A box end: corner weights `(x0, x1)`, i.e. `c = x1 / (x0 + x1)`. -/
abbrev Pt := Nat × Nat

def nomP (p : Pt) (a : CArc) : Nat := p.1 * a.F + p.2 * a.S

/-- `p ≤ c`. -/
def PLe (p : Pt) (c : Corner) : Prop := p.2 * c.W ≤ c.w1 * (p.1 + p.2)
/-- `c ≤ q`. -/
def LeP (c : Corner) (q : Pt) : Prop := c.w1 * (q.1 + q.2) ≤ q.2 * c.W

theorem nomP_lo {p : Pt} {c : Corner} (h : PLe p c) (a : CArc) :
    nomP p a * c.W ≤ nom c a * (p.1 + p.2) := by
  obtain ⟨F, S, hFS⟩ := a
  obtain ⟨a0, a1⟩ := p
  obtain ⟨w0, w1, _⟩ := c
  simp only [PLe, Corner.W, nom, nomP] at h ⊢
  obtain ⟨Δ, rfl⟩ := Nat.exists_eq_add_of_le hFS
  have := Nat.mul_le_mul_left Δ h
  grind

theorem nomP_hi {q : Pt} {c : Corner} (h : LeP c q) (a : CArc) :
    nom c a * (q.1 + q.2) ≤ nomP q a * c.W := by
  obtain ⟨F, S, hFS⟩ := a
  obtain ⟨b0, b1⟩ := q
  obtain ⟨w0, w1, _⟩ := c
  simp only [LeP, Corner.W, nom, nomP] at h ⊢
  obtain ⟨Δ, rfl⟩ := Nat.exists_eq_add_of_le hFS
  have := Nat.mul_le_mul_left Δ h
  grind

/-- `κ < un/ud` in the forms the chains use. -/
theorem kap_lo {k : Kappa} {un ud : Nat} (hun : un ≤ ud) (hk : k.num * ud < un * k.den) :
    (ud - un) * k.den < k.lo * ud := by
  unfold Kappa.lo
  have := k.num_le
  rw [Nat.sub_mul, Nat.sub_mul]
  have : k.num * ud ≤ k.den * ud := Nat.mul_le_mul_right _ this
  have : un * k.den ≤ ud * k.den := Nat.mul_le_mul_right _ hun
  rw [Nat.mul_comm k.den ud] at *
  omega

theorem kap_hi {k : Kappa} {un ud : Nat} (hk : k.num * ud < un * k.den) :
    k.hi * ud < (ud + un) * k.den := by
  unfold Kappa.hi
  rw [Nat.add_mul, Nat.add_mul, Nat.mul_comm k.den ud]
  omega

/-- Per-arc lower bound on a box `[p, ·]` for every `κ < un/ud`. -/
theorem arc_lo {k : Kappa} {c : Corner} {a : CArc} {d : Nat} {un ud : Nat} {p : Pt}
    (hS : Scat k c a d) (hun : un ≤ ud) (hk : k.num * ud < un * k.den) (hp : PLe p c)
    (hpw : 0 < p.1 + p.2) (hna : 0 < nomP p a) :
    (ud - un) * nomP p a / (ud * (p.1 + p.2)) + 1 ≤ d := by
  have hW : 0 < c.W := c.pos
  have hpos : 0 < k.den * c.W := Nat.mul_pos k.den_pos hW
  have h := chain_lo_s (Lu := ud - un) (Du := ud) (Wa := p.1 + p.2) hpos (Nat.mul_pos hna hW)
    hS.1 (kap_lo hun hk) (nomP_lo hp a)
  have hb : 0 < ud * (p.1 + p.2) := by
    rcases Nat.eq_zero_or_pos ud with h0 | h0
    · subst h0; simp at h
    · exact Nat.mul_pos h0 hpw
  have : (ud - un) * nomP p a / (ud * (p.1 + p.2)) < d := by
    rw [Nat.div_lt_iff_lt_mul hb, Nat.mul_comm d]; exact h
  omega

/-- Per-arc upper bound on a box `[·, q]` for every `κ < un/ud`. -/
theorem arc_hi {k : Kappa} {c : Corner} {a : CArc} {d : Nat} {un ud : Nat} {q : Pt}
    (hS : Scat k c a d) (hud : 0 < ud) (hk : k.num * ud < un * k.den) (hq : LeP c q)
    (hqw : 0 < q.1 + q.2) (hnb : 0 < nomP q a) :
    d ≤ ((ud + un) * nomP q a - 1) / (ud * (q.1 + q.2)) := by
  have hW : 0 < c.W := c.pos
  have hpos : 0 < k.den * c.W := Nat.mul_pos k.den_pos hW
  have h := chain_hi_s (Hu := ud + un) (Du := ud) (Wb := q.1 + q.2) hpos (Nat.mul_pos hnb hW)
    hS.2 (kap_hi hk) (nomP_hi hq a)
  have hb : 0 < ud * (q.1 + q.2) := Nat.mul_pos hud hqw
  apply le_div_of hb
  omega

/-- The fork's arcs, as data: `A e` per arc. -/
abbrev Tab := Arc → CArc

/-- Lower ends and upper end of a box `[p, q]` at `u = un/ud` (strict rounding). -/
def loB (A : Tab) (un ud : Nat) (p : Pt) (e : Arc) : Nat :=
  (ud - un) * nomP p (A e) / (ud * (p.1 + p.2)) + 1
def hiB (A : Tab) (un ud : Nat) (q : Pt) : Nat :=
  ((ud + un) * nomP q (A .wAC) - 1) / (ud * (q.1 + q.2))
def sumLo (A : Tab) (un ud : Nat) (p : Pt) : Nat :=
  loB A un ud p .wSt + loB A un ud p .aSt + loB A un ud p .wQG + loB A un ud p .aG +
    loB A un ud p .wGC

/-- The fork vector `(wSt, aSt, wQG, aG, wGC, wAC)` of an assignment. -/
def vec (d : Arc → Nat) : List Nat := [d .wSt, d .aSt, d .wQG, d .aG, d .wGC, d .wAC]

/-- Box check: either the box is safe outright (`hi ≤ Σ lo`), or the only
possible violating vector is forced (`hi = Σ lo + 1`) and is in `sp`. -/
def boxOK (A : Tab) (un ud : Nat) (sp : List (List Nat)) (p q : Pt) : Bool :=
  0 < p.1 + p.2 && 0 < q.1 + q.2 &&
  (hiB A un ud q ≤ sumLo A un ud p ||
    (hiB A un ud q == sumLo A un ud p + 1 &&
      sp.contains [loB A un ud p .wSt, loB A un ud p .aSt, loB A un ud p .wQG,
        loB A un ud p .aG, loB A un ud p .wGC, hiB A un ud q]))

theorem box_sound {A : Tab} {un ud : Nat} {sp : List (List Nat)} {p q : Pt}
    (hA : ∀ e, 0 < (A e).F) (hun : un ≤ ud) (hud : 0 < ud)
    (hchk : boxOK A un ud sp p q = true) {k : Kappa} (hk : k.num * ud < un * k.den)
    {c : Corner} (hp : PLe p c) (hq : LeP c q) {d : Arc → Nat}
    (hS : ∀ e, Scat k c (A e) (d e)) :
    d .wAC ≤ d .wSt + d .aSt + d .wQG + d .aG + d .wGC ∨ vec d ∈ sp := by
  simp only [boxOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.contains_iff_mem] at hchk
  obtain ⟨⟨hpw, hqw⟩, hc⟩ := hchk
  have pn : ∀ e, 0 < nomP p (A e) := fun e => by
    unfold nomP; have := hA e
    rcases Nat.eq_zero_or_pos p.1 with h | h
    · have : 0 < p.2 := by omega
      have := (A e).F_le_S
      exact Nat.lt_of_lt_of_le (Nat.mul_pos ‹0 < p.2› (by omega)) (Nat.le_add_left _ _)
    · exact Nat.lt_of_lt_of_le (Nat.mul_pos h (hA e)) (Nat.le_add_right _ _)
  have qn : 0 < nomP q (A .wAC) := by
    unfold nomP; have := hA .wAC
    rcases Nat.eq_zero_or_pos q.1 with h | h
    · have : 0 < q.2 := by omega
      have := (A .wAC).F_le_S
      exact Nat.lt_of_lt_of_le (Nat.mul_pos ‹0 < q.2› (by omega)) (Nat.le_add_left _ _)
    · exact Nat.lt_of_lt_of_le (Nat.mul_pos h (hA .wAC)) (Nat.le_add_right _ _)
  have l1 := arc_lo (hS .wSt) hun hk hp hpw (pn _)
  have l2 := arc_lo (hS .aSt) hun hk hp hpw (pn _)
  have l3 := arc_lo (hS .wQG) hun hk hp hpw (pn _)
  have l4 := arc_lo (hS .aG) hun hk hp hpw (pn _)
  have l5 := arc_lo (hS .wGC) hun hk hp hpw (pn _)
  have u := arc_hi (hS .wAC) hud hk hq hqw qn
  simp only [sumLo, loB, hiB] at hc
  by_cases hle : d .wAC ≤ d .wSt + d .aSt + d .wQG + d .aG + d .wGC
  · exact Or.inl hle
  · right
    rcases hc with hc | ⟨hc1, hc2⟩
    · omega
    · have e1 : d .wSt = (ud - un) * nomP p (A .wSt) / (ud * (p.1 + p.2)) + 1 := by omega
      have e2 : d .aSt = (ud - un) * nomP p (A .aSt) / (ud * (p.1 + p.2)) + 1 := by omega
      have e3 : d .wQG = (ud - un) * nomP p (A .wQG) / (ud * (p.1 + p.2)) + 1 := by omega
      have e4 : d .aG = (ud - un) * nomP p (A .aG) / (ud * (p.1 + p.2)) + 1 := by omega
      have e5 : d .wGC = (ud - un) * nomP p (A .wGC) / (ud * (p.1 + p.2)) + 1 := by omega
      have e6 : d .wAC = ((ud + un) * nomP q (A .wAC) - 1) / (ud * (q.1 + q.2)) := by omega
      simp only [vec, e1, e2, e3, e4, e5, e6]
      exact hc2

/-- All consecutive boxes of a chain of points pass. -/
def chainOK (A : Tab) (un ud : Nat) (sp : List (List Nat)) : Pt → List Pt → Bool
  | _, [] => true
  | p, q :: l => boxOK A un ud sp p q && chainOK A un ud sp q l

def lastPt : Pt → List Pt → Pt
  | p, [] => p
  | _, q :: l => lastPt q l

theorem chain_sound {A : Tab} {un ud : Nat} {sp : List (List Nat)}
    (hA : ∀ e, 0 < (A e).F) (hun : un ≤ ud) (hud : 0 < ud) {k : Kappa}
    (hk : k.num * ud < un * k.den) {c : Corner} {d : Arc → Nat}
    (hS : ∀ e, Scat k c (A e) (d e)) :
    ∀ (l : List Pt) (p q : Pt), chainOK A un ud sp p (q :: l) = true → PLe p c →
      LeP c (lastPt q l) →
      d .wAC ≤ d .wSt + d .aSt + d .wQG + d .aG + d .wGC ∨ vec d ∈ sp := by
  intro l
  induction l with
  | nil =>
    intro p q h hp hq
    simp only [chainOK, Bool.and_true] at h
    exact box_sound hA hun hud h hk hp hq hS
  | cons r l ih =>
    intro p q h hp hq
    simp only [chainOK, Bool.and_eq_true] at h
    by_cases hcq : LeP c q
    · exact box_sound hA hun hud h.1 hk hp hcq hS
    · have hqc : PLe q c := by unfold LeP at hcq; unfold PLe; omega
      exact ih q r (by simp only [chainOK, Bool.and_eq_true]; exact h.2) hqc hq

/-- The chain of boxes from the fast corner `(1, 0)` to the slow corner `(0, 1)`. -/
theorem cover_sound {A : Tab} {un ud : Nat} {sp : List (List Nat)} {l : List Pt} {q : Pt}
    (hA : ∀ e, 0 < (A e).F) (hun : un ≤ ud) (hud : 0 < ud)
    (hchain : chainOK A un ud sp (1, 0) (q :: l) = true) (hlast : lastPt q l = (0, 1))
    {k : Kappa} (hk : k.num * ud < un * k.den) (c : Corner) (d : Arc → Nat)
    (hS : ∀ e, Scat k c (A e) (d e)) :
    d .wAC ≤ d .wSt + d .aSt + d .wQG + d .aG + d .wGC ∨ vec d ∈ sp := by
  refine chain_sound hA hun hud hk hS l (1, 0) q hchain ?_ ?_
  · unfold PLe; simp
  · rw [hlast]; unfold LeP Corner.W; simp

end Formal.Cells.OnNetlistArbKappaExact
