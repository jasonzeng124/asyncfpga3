import Formal.Cells.ArbA0Fork
import Formal.Cells.OnNetlistArbKappa

/-!
# Probe Bkx18: EXACT κ thresholds of the routed arbiter's A0 fork (whole-ps model)

Shard B. Notes: `formal/notes/B-arb-kappa-exact.md`. Closes the gap left open by
`OnNetlistArbKappa` (audit row 18: "exact per-pair kappa thresholds" OVERSTATED): that file
proves safety for κ ≤ κ* (the real-relaxation endpoint bound) and a counter-instance only
from κ* + 6/(E+L); in between it decides nothing.

## The model (exactly `OnNetlistArbKappa`'s, i.e. A's `CornerNat`)

* κ = num/den is RATIONAL; the corner c = w1/(w0+w1) is RATIONAL and shared by the die;
* every delay is a WHOLE number of ps (`Nat`), within `1 ± κ` of the arc's nominal delay at c
  (`Scat`: `(den-num)·nom ≤ den·W·d ≤ (den+num)·nom`);
* the fork is 7g's gate-level condition (`ArbA0Fork`): `Safe` (no early ack on any run of the
  gate relations) iff `wAC ≤ wSt + aSt + wQG + aG + wGC` (`safe{1,2}_of_le`, `not_safe{1,2}`).

The definitions of §0 (`Kappa`, `CArc`, `Corner`, `nom`, `Scat`, `Arc`, `dlOf`) and the 16 arc
tables are restated (verbatim, core-only; the work was done before Mathlib was built). §8
bridges them: `Scat` is A's `Formal.Core.Substrate.Scat` by `Iff.rfl`, the tables equal
`OnNetlistArbKappa.A_*` by `rfl`, and `Bridge.exact_*` restates every `exact_*` in A's types.

## Proved, per seed × client × reading (16 pairs), `exact_*`

`(∀ c d, (∀ e, Scat κ c (A e) (d e)) → Safe …) ↔ Below κ`, where `Below κ` is
* 15 pairs: `κ < u ∧ P(κ) < 0` with `P` an explicit integer quadratic form in (num, den) whose
  root in [0, 1] is IRRATIONAL (κ_ex, ≈ 1e-10 bracket `bracket_*`). Since κ is rational,
  safe ⟺ κ < κ_ex ⟺ κ ≤ κ_ex. The infimum is approached only at an interior corner
  (c* ≈ 0.0003–0.003 for `cons`, 1 − c* ≈ 0.0002–0.013 for `lit`) that moves with κ, and is not
  attained: for every rational κ > κ_ex a violating assignment exists, at a κ-dependent corner;
* s2c2 `cons`: `κ < 94/325`, attained at the fast corner (κ ≥ 94/325 is unsafe).

Both sides are at the same level: the safe side is 7g's `Safe` over every run for every corner
and every whole-ps assignment within κ; the unsafe side exhibits a corner and an assignment within
κ (all ten arcs) on which every run acks early (and runs exist).
`safe_antitone`: the safe κ form an initial segment (no staircase in κ).

## How (method, not assumed)

* safe side: [0, 1] is covered by a chain of corner boxes checked by kernel evaluation
  (`chainOK`, `cover_sound`); in each box either the outward-rounded whole-ps bounds already
  give `late ≤ early`, or they force the single binding vector, which is then excluded exactly
  by eliminating the corner (`elim2`: realisable iff `P ≥ 0`);
* unsafe side: for κ ≥ κ_fix a fixed endpoint-corner assignment; for κ ∈ [κ_lo, κ_fix) the corner
  `w0 = (den+num)·S_L − den·M`, `w1 = den·M − (den+num)·F_L` (late arc exactly at its upper
  band end), with every arc's band checked by Bernstein certificates (`bern`, `grind`).

## NOT covered
Delays varying per tick (one fixed delay per arc per run, as 7g); the A0 rise; arbitration
(mutual exclusion); Kleene X / metastability; the value of κ itself (unmeasured); the `cons`
early SLOW_MIN / late FAST_MAX endpoints are Bt3's per-corner windows, not tied to a file.
-/

namespace Formal.Cells.OnNetlistArbKappaExact

-- omega / grind certificates on coefficients up to ~10^12, and kernel evaluation of the box chains.
set_option maxRecDepth 100000

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
/-- No scatter. -/
def zero : Kappa := ⟨0, 1, by decide, by decide⟩
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

/-- Lower chain: scatter at `c ≥ ca`, `κ ≤ u` give the bound at `(ca, u)`. -/
theorem chain_lo {L n Dk Wc d Lu Du na Wa : Nat} (hpos : 0 < Dk * Wc)
    (h1 : L * n ≤ Dk * Wc * d) (h2 : Lu * Dk ≤ L * Du) (h3 : na * Wc ≤ n * Wa) :
    Lu * na ≤ Du * Wa * d := by
  have e1 : (Lu * Dk) * (na * Wc) ≤ (L * Du) * (n * Wa) := Nat.mul_le_mul h2 h3
  have e2 : (L * n) * (Du * Wa) ≤ (Dk * Wc * d) * (Du * Wa) := Nat.mul_le_mul_right _ h1
  have e3 : (Dk * Wc) * (Lu * na) ≤ (Dk * Wc) * (Du * Wa * d) := by
    have q1 : (Dk * Wc) * (Lu * na) = (Lu * Dk) * (na * Wc) := by
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    have q2 : (L * Du) * (n * Wa) = (L * n) * (Du * Wa) := by
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    have q3 : (Dk * Wc * d) * (Du * Wa) = (Dk * Wc) * (Du * Wa * d) := by
      simp only [Nat.mul_comm, Nat.mul_left_comm]
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
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    have q2 : (H * n) * (Du * Wb) = (H * Du) * (n * Wb) := by
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    have q3 : (Hu * Dk) * (nb * Wc) = (Dk * Wc) * (Hu * nb) := by
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    omega
  exact Nat.le_of_mul_le_mul_left e3 hpos


/-- Strict lower chain (`κ < u`). -/
theorem chain_lo_s {L n Dk Wc d Lu Du na Wa : Nat} (_hpos : 0 < Dk * Wc) (hna : 0 < na * Wc)
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
      simp only [Nat.mul_comm, Nat.mul_left_comm]
    omega
  exact Nat.lt_of_mul_lt_mul_left e3

/-- Strict upper chain (`κ < u`). -/
theorem chain_hi_s {H n Dk Wc d Hu Du nb Wb : Nat} (_hpos : 0 < Dk * Wc) (hnb : 0 < nb * Wc)
    (h1 : Dk * Wc * d ≤ H * n) (h2 : H * Du < Hu * Dk) (h3 : n * Wb ≤ nb * Wc) :
    Du * Wb * d < Hu * nb := by
  have e1 : (H * Du) * (n * Wb) < (Hu * Dk) * (nb * Wc) :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ h3) (Nat.mul_lt_mul_of_pos_right h2 hnb)
  have e2 : (Dk * Wc * d) * (Du * Wb) ≤ (H * n) * (Du * Wb) := Nat.mul_le_mul_right _ h1
  have e3 : (Dk * Wc) * (Du * Wb * d) < (Dk * Wc) * (Hu * nb) := by
    have q1 : (Dk * Wc) * (Du * Wb * d) = (Dk * Wc * d) * (Du * Wb) := by
      simp only [Nat.mul_comm, Nat.mul_left_comm]
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

/-! ## 4. Eliminating the corner; Bernstein products -/

/-- Two half-planes through the origin in `(w0, w1)` with `b1 > 0`, `a2 > 0` meet in the
closed positive quadrant only if `a2·b1 ≤ a1·b2`. -/
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

/-- The three Bernstein products of `t = N/D ∈ [p0/q0, p1/q1]`. -/
theorem bern (N D : Int) {p0 q0 p1 q1 : Int} (h0 : p0 * D ≤ q0 * N) (h1 : q1 * N ≤ p1 * D) :
    0 ≤ (q0 * N - p0 * D) * (q0 * N - p0 * D) ∧ 0 ≤ (q0 * N - p0 * D) * (p1 * D - q1 * N) ∧
      0 ≤ (p1 * D - q1 * N) * (p1 * D - q1 * N) :=
  ⟨Int.mul_nonneg (by omega) (by omega), Int.mul_nonneg (by omega) (by omega),
    Int.mul_nonneg (by omega) (by omega)⟩

/-! ## 5. Monotonicity in κ: the safe set is an initial segment -/

/-- Scatter bands only grow with κ. -/
theorem scat_mono {k k' : Kappa} (hkk : k.num * k'.den ≤ k'.num * k.den) {c : Corner} {a : CArc}
    {d : Nat} (h : Scat k c a d) : Scat k' c a d := by
  have hpos : 0 < k.den * c.W := Nat.mul_pos k.den_pos c.pos
  have n1 := k.num_le
  have n2 := k'.num_le
  constructor
  · refine chain_lo (Lu := k'.lo) (Du := k'.den) (na := nom c a) (Wa := c.W) hpos h.1 ?_ (Nat.le_refl _)
    unfold Kappa.lo
    rw [Nat.sub_mul, Nat.sub_mul]
    have : k'.num * k.den ≤ k'.den * k.den := Nat.mul_le_mul_right _ n2
    have : k.num * k'.den ≤ k.den * k'.den := Nat.mul_le_mul_right _ n1
    rw [Nat.mul_comm k.den k'.den] at *
    omega
  · refine chain_hi (Hu := k'.hi) (Du := k'.den) (nb := nom c a) (Wb := c.W) hpos h.2 ?_ (Nat.le_refl _)
    unfold Kappa.hi
    rw [Nat.add_mul, Nat.add_mul, Nat.mul_comm k.den k'.den]
    omega

/-- **The whole-ps model has no staircase in κ**: if every assignment within κ' (at every
corner) has property `Q`, so does every assignment within any κ ≤ κ'. Hence the safe κ of each
pair form an initial segment, and the unsafe ones the complementary final segment. -/
theorem safe_antitone {A : Tab} {Q : (Arc → Nat) → Prop} {k k' : Kappa}
    (hkk : k.num * k'.den ≤ k'.num * k.den)
    (h : ∀ c d, (∀ e, Scat k' c (A e) (d e)) → Q d) :
    ∀ c d, (∀ e, Scat k c (A e) (d e)) → Q d :=
  fun c d hS => h c d (fun e => scat_mono hkk (hS e))

/-! ## 6. Per seed x client x reading: exact thresholds -/

/-! ### Seed 1, client 1, `cons` -/

/-- Arc endpoints (F, S) ps, seed 1, client 1, `cons` (= `OnNetlistArbKappa.A_s1c1_cons`). -/
def A_s1c1_cons : Tab
  | .c => ⟨160, 488, by decide⟩
  | .wSt => ⟨262, 638, by decide⟩
  | .aSt => ⟨45, 100, by decide⟩
  | .wQf => ⟨76, 288, by decide⟩
  | .wQG => ⟨122, 325, by decide⟩
  | .aG => ⟨48, 93, by decide⟩
  | .wGC => ⟨209, 524, by decide⟩
  | .wAC => ⟨375, 795, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨71, 276, by decide⟩

theorem A_s1c1_cons_pos : ∀ e, 0 < (A_s1c1_cons e).F := by intro e; cases e <;> decide

/-- Box chain over `[0, 1]` (21 boxes) at `u = 487/1648`. -/
def pts_s1c1_cons : List Pt := [(133679031, 538697), (17079341947, 100527237), (8508096953, 81837639), (16889897823, 289971361), (4190900435, 104066861), (16637305657, 542563527), (16479435553, 700433631), (16226843387, 953025797), (996417325, 77324499), (7766107465, 823827127), (15058604619, 2121264565), (14427124203, 2752744981), (3409443421, 885523875), (12595830999, 4584038185), (5603287043, 2986647549), (36992199, 30116665), (7196673449, 9983195735), (4260289519, 12919579665), (534555069, 16645314115), (0, 1)]
def sp_s1c1_cons : List (List Nat) := [[185, 32, 86, 34, 148, 486]]

theorem chain_s1c1_cons : chainOK A_s1c1_cons 487 1648 sp_s1c1_cons (1, 0) ((17142489989, 37379195) :: pts_s1c1_cons) = true := by
  decide +kernel
theorem last_s1c1_cons : lastPt (17142489989, 37379195) pts_s1c1_cons = (0, 1) := by decide +kernel

/-- `P(κ)·den²` for the binding vector `[185, 32, 86, 34, 148]`, late 486, binding early arc `wQG`:
the vector is realisable at some corner iff `P ≥ 0`. Its root in `[0, 1]` is
κ_ex ≈ 0.2954922165 (irrational: discriminant 14417129664 is not a square). -/
def P_s1c1_cons (k : Kappa) : Int :=
  -24885 * (k.num : Int) * k.num + 134778 * (k.num : Int) * k.den + -37653 * (k.den : Int) * k.den
/-- **κ < κ_ex** (`P < 0` below `u = 487/1648`). -/
def Below_s1c1_cons (k : Kappa) : Prop := k.num * 1648 < 487 * k.den ∧ P_s1c1_cons k < 0
instance (k : Kappa) : Decidable (Below_s1c1_cons k) := inferInstanceAs (Decidable (_ ∧ _))

theorem kill_s1c1_cons {k : Kappa} (hb : Below_s1c1_cons k) (c : Corner) (h1 : Scat k c (A_s1c1_cons .wQG) 86)
    (h2 : Scat k c (A_s1c1_cons .wAC) 486) : False := by
  obtain ⟨hk, hP⟩ := hb
  unfold P_s1c1_cons at hP
  obtain ⟨w0, w1, hw⟩ := c
  simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s1c1_cons] at h1 h2
  have hN := k.num_le
  generalize k.num = N at *
  generalize k.den = D at *
  obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Nat.add_sub_cancel_left] at h1 h2
  have j1 := Int.ofNat_le.mpr h1.1
  have j2 := Int.ofNat_le.mpr h2.2
  push_cast at j1 j2
  simp only [Int.natCast_add] at hP
  have i1 : (w0 : Int) * ((L : Int) * 122 - (N + L) * 86) + (w1 : Int) * ((L : Int) * 325 - (N + L) * 86) ≤ 0 := by
    grind
  have i2 : (w0 : Int) * (((N : Int) + L) * 486 - (N + N + L) * 375) +
      (w1 : Int) * (((N : Int) + L) * 486 - (N + N + L) * 795) ≤ 0 := by
    grind
  have := elim2 (by omega) (by omega) (by omega) (by omega) (by omega) i1 i2
  grind

theorem safe_s1c1_cons (k : Kappa) (H_BELOW : Below_s1c1_cons k) (c : Corner) (d : Arc → Nat)
    (H_SCAT : ∀ e, Scat k c (A_s1c1_cons e) (d e)) : Safe F1 G1 false (dlOf d) := by
  apply safe1_of_le
  rcases cover_sound (A_s1c1_cons_pos) (by decide) (by decide) chain_s1c1_cons last_s1c1_cons H_BELOW.1 c d H_SCAT with h | h
  · exact h
  · exfalso
    simp only [sp_s1c1_cons, vec, List.mem_singleton, List.cons.injEq, and_true] at h
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h
    have s1 := H_SCAT .wQG
    have s2 := H_SCAT .wAC
    rw [e3] at s1
    rw [e6] at s2
    exact kill_s1c1_cons H_BELOW c s1 s2

/-- The violating assignment (binding vector, other arcs at their fast endpoint). -/
def dW_s1c1_cons : Arc → Nat
  | .c => 160 | .wSt => 185 | .aSt => 32 | .wQf => 76 | .wQG => 86 | .aG => 34 | .wGC => 148 | .wAC => 486 | .aC => 45 | .wCf => 71

/-- Between `u` and `κ_fix = 37/125`, `P ≥ 0` (Bernstein certificate). -/
theorem pos_s1c1_cons (k : Kappa) (hfix : k.num * 125 < 37 * k.den) (hb : ¬ Below_s1c1_cons k) : 0 ≤ P_s1c1_cons k := by
  unfold Below_s1c1_cons at hb
  by_cases hu : k.num * 1648 < 487 * k.den
  · have := (not_and.mp hb) hu
    omega
  · unfold P_s1c1_cons
    obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 487) (q0 := 1648) (p1 := 37) (q1 := 125)
      (by omega) (by omega)
    grind

/-- `P ≥ 0` forces `κ ≥ κ_lo = 1147/3882` (`P < 0` on `[0, κ_lo)`, Bernstein certificate). -/
theorem lo_s1c1_cons (k : Kappa) (hP : 0 ≤ P_s1c1_cons k) : 1147 * k.den ≤ 3882 * k.num := by
  apply Classical.byContradiction; intro h
  unfold P_s1c1_cons at hP
  have hv : (0 : Int) < 1147 * (k.den : Int) - 3882 * k.num := by omega
  have hv2 := Int.mul_pos hv hv
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 0) (q0 := 1) (p1 := 1147) (q1 := 3882)
    (by omega) (by omega)
  grind

/-- On `[κ_lo, κ_fix]` with `P ≥ 0`: the binding vector is realised at the corner where the
late arc is exactly at `(1+κ)·nominal` (`w0 = (den+num)·795 − den·486`, `w1 = den·486 − (den+num)·375`). -/
theorem wit_s1c1_cons (k : Kappa) (hlo : 1147 * k.den ≤ 3882 * k.num) (hfix : k.num * 125 ≤ 37 * k.den)
    (hP : 0 ≤ P_s1c1_cons k) (hpos : 0 < (309 * k.den + 795 * k.num) + (111 * k.den - 375 * k.num)) :
    ∀ e, Scat k ⟨309 * k.den + 795 * k.num, 111 * k.den - 375 * k.num, hpos⟩ (A_s1c1_cons e) (dW_s1c1_cons e) := by
  intro e
  have hN := k.num_le
  have hD := k.den_pos
  unfold P_s1c1_cons at hP
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 1147) (q0 := 3882) (p1 := 37) (q1 := 125)
    (by omega) (by omega)
  have hs0 : 375 * k.num ≤ 111 * k.den := by omega
  cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s1c1_cons, dW_s1c1_cons] <;>
  (constructor <;> apply Int.ofNat_le.mp <;>
    push_cast [Int.ofNat_sub hs0, Int.ofNat_sub hN] <;> grind)

theorem unsafe_s1c1_cons (k : Kappa) (H_KAPPA : ¬ Below_s1c1_cons k) :
    ∃ c d, (∀ e, Scat k c (A_s1c1_cons e) (d e)) ∧ ¬ Safe F1 G1 false (dlOf d) := by
  by_cases hfix : 37 * k.den ≤ k.num * 125
  · refine ⟨Corner.fast, dW_s1c1_cons, ?_, not_safe1 (by decide) (by decide) (by decide)⟩
    intro e; have := k.num_le
    cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, Corner.fast, A_s1c1_cons, dW_s1c1_cons] <;> omega
  · have hP := pos_s1c1_cons k (by omega) H_KAPPA
    have hlo := lo_s1c1_cons k hP
    have hD := k.den_pos
    exact ⟨_, dW_s1c1_cons, wit_s1c1_cons k hlo (by omega) hP (by omega), not_safe1 (by decide) (by decide) (by decide)⟩

/-- **Exact threshold, seed 1, client 1, `cons`.** Every assignment within κ at every corner is
safe iff `Below_s1c1_cons κ` (i.e. κ < κ_ex ≈ 0.2954922165); otherwise a violating whole-ps assignment exists. -/
theorem exact_s1c1_cons (k : Kappa) :
    (∀ c d, (∀ e, Scat k c (A_s1c1_cons e) (d e)) → Safe F1 G1 false (dlOf d)) ↔ Below_s1c1_cons k := by
  constructor
  · intro hs; apply Classical.byContradiction; intro hb
    obtain ⟨c, d, h1, h2⟩ := unsafe_s1c1_cons k hb
    exact h2 (hs c d h1)
  · intro hb c d h; exact safe_s1c1_cons k hb c d h

/-- Bracket: κ_ex ∈ (738730541/2500000000, 590984433/2000000000]. -/
theorem bracket_s1c1_cons : Below_s1c1_cons ⟨738730541, 2500000000, by decide, by decide⟩ ∧
    ¬ Below_s1c1_cons ⟨590984433, 2000000000, by decide, by decide⟩ := by decide
theorem nonvac_s1c1_cons : Below_s1c1_cons Kappa.zero := by decide

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
  | .c => 160 | .wSt => 215 | .aSt => 37 | .wQf => 76 | .wQG => 100 | .aG => 37 | .wGC => 145 | .wAC => 535 | .aC => 45 | .wCf => 195

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

/-! ### Seed 2, client 1, `cons` -/

/-- Arc endpoints (F, S) ps, seed 2, client 1, `cons` (= `OnNetlistArbKappa.A_s2c1_cons`). -/
def A_s2c1_cons : Tab
  | .c => ⟨172, 522, by decide⟩
  | .wSt => ⟨225, 578, by decide⟩
  | .aSt => ⟨45, 100, by decide⟩
  | .wQf => ⟨76, 288, by decide⟩
  | .wQG => ⟨202, 525, by decide⟩
  | .aG => ⟨43, 120, by decide⟩
  | .wGC => ⟨241, 610, by decide⟩
  | .wAC => ⟨378, 760, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨115, 423, by decide⟩

theorem A_s2c1_cons_pos : ∀ e, 0 < (A_s2c1_cons e).F := by intro e; cases e <;> decide

/-- Box chain over `[0, 1]` (13 boxes) at `u = 47/140`. -/
def pts_s2c1_cons : List Pt := [(17008152263, 171716921), (4218368081, 76599215), (65122861, 1986003), (8184211277, 405723315), (15930712753, 1249156431), (15257313059, 1922556125), (7106771767, 1483162825), (12597384269, 4582484915), (10105805403, 7074063781), (3150548567, 5439386025), (59523723, 2087959925), (0, 1)]
def sp_s2c1_cons : List (List Nat) := [[150, 30, 135, 29, 161, 506]]

theorem chain_s2c1_cons : chainOK A_s2c1_cons 47 140 sp_s2c1_cons (1, 0) ((17109162217, 70706967) :: pts_s2c1_cons) = true := by
  decide +kernel
theorem last_s2c1_cons : lastPt (17109162217, 70706967) pts_s2c1_cons = (0, 1) := by decide +kernel

/-- `P(κ)·den²` for the binding vector `[150, 30, 135, 29, 161]`, late 506, binding early arc `wSt`:
the vector is realisable at some corner iff `P ≥ 0`. Its root in `[0, 1]` is
κ_ex ≈ 0.3356387991 (irrational: discriminant 41633568100 is not a square). -/
def P_s2c1_cons (k : Kappa) : Int :=
  -47484 * (k.num : Int) * k.num + 235918 * (k.num : Int) * k.den + -73834 * (k.den : Int) * k.den
/-- **κ < κ_ex** (`P < 0` below `u = 47/140`). -/
def Below_s2c1_cons (k : Kappa) : Prop := k.num * 140 < 47 * k.den ∧ P_s2c1_cons k < 0
instance (k : Kappa) : Decidable (Below_s2c1_cons k) := inferInstanceAs (Decidable (_ ∧ _))

theorem kill_s2c1_cons {k : Kappa} (hb : Below_s2c1_cons k) (c : Corner) (h1 : Scat k c (A_s2c1_cons .wSt) 150)
    (h2 : Scat k c (A_s2c1_cons .wAC) 506) : False := by
  obtain ⟨hk, hP⟩ := hb
  unfold P_s2c1_cons at hP
  obtain ⟨w0, w1, hw⟩ := c
  simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s2c1_cons] at h1 h2
  have hN := k.num_le
  generalize k.num = N at *
  generalize k.den = D at *
  obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Nat.add_sub_cancel_left] at h1 h2
  have j1 := Int.ofNat_le.mpr h1.1
  have j2 := Int.ofNat_le.mpr h2.2
  push_cast at j1 j2
  simp only [Int.natCast_add] at hP
  have i1 : (w0 : Int) * ((L : Int) * 225 - (N + L) * 150) + (w1 : Int) * ((L : Int) * 578 - (N + L) * 150) ≤ 0 := by
    grind
  have i2 : (w0 : Int) * (((N : Int) + L) * 506 - (N + N + L) * 378) +
      (w1 : Int) * (((N : Int) + L) * 506 - (N + N + L) * 760) ≤ 0 := by
    grind
  have := elim2 (by omega) (by omega) (by omega) (by omega) (by omega) i1 i2
  grind

theorem safe_s2c1_cons (k : Kappa) (H_BELOW : Below_s2c1_cons k) (c : Corner) (d : Arc → Nat)
    (H_SCAT : ∀ e, Scat k c (A_s2c1_cons e) (d e)) : Safe F1 G1 false (dlOf d) := by
  apply safe1_of_le
  rcases cover_sound (A_s2c1_cons_pos) (by decide) (by decide) chain_s2c1_cons last_s2c1_cons H_BELOW.1 c d H_SCAT with h | h
  · exact h
  · exfalso
    simp only [sp_s2c1_cons, vec, List.mem_singleton, List.cons.injEq, and_true] at h
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h
    have s1 := H_SCAT .wSt
    have s2 := H_SCAT .wAC
    rw [e1] at s1
    rw [e6] at s2
    exact kill_s2c1_cons H_BELOW c s1 s2

/-- The violating assignment (binding vector, other arcs at their fast endpoint). -/
def dW_s2c1_cons : Arc → Nat
  | .c => 172 | .wSt => 150 | .aSt => 30 | .wQf => 76 | .wQG => 135 | .aG => 29 | .wGC => 161 | .wAC => 506 | .aC => 45 | .wCf => 115

/-- Between `u` and `κ_fix = 64/189`, `P ≥ 0` (Bernstein certificate). -/
theorem pos_s2c1_cons (k : Kappa) (hfix : k.num * 189 < 64 * k.den) (hb : ¬ Below_s2c1_cons k) : 0 ≤ P_s2c1_cons k := by
  unfold Below_s2c1_cons at hb
  by_cases hu : k.num * 140 < 47 * k.den
  · have := (not_and.mp hb) hu
    omega
  · unfold P_s2c1_cons
    obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 47) (q0 := 140) (p1 := 64) (q1 := 189)
      (by omega) (by omega)
    grind

/-- `P ≥ 0` forces `κ ≥ κ_lo = 49/146` (`P < 0` on `[0, κ_lo)`, Bernstein certificate). -/
theorem lo_s2c1_cons (k : Kappa) (hP : 0 ≤ P_s2c1_cons k) : 49 * k.den ≤ 146 * k.num := by
  apply Classical.byContradiction; intro h
  unfold P_s2c1_cons at hP
  have hv : (0 : Int) < 49 * (k.den : Int) - 146 * k.num := by omega
  have hv2 := Int.mul_pos hv hv
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 0) (q0 := 1) (p1 := 49) (q1 := 146)
    (by omega) (by omega)
  grind

/-- On `[κ_lo, κ_fix]` with `P ≥ 0`: the binding vector is realised at the corner where the
late arc is exactly at `(1+κ)·nominal` (`w0 = (den+num)·760 − den·506`, `w1 = den·506 − (den+num)·378`). -/
theorem wit_s2c1_cons (k : Kappa) (hlo : 49 * k.den ≤ 146 * k.num) (hfix : k.num * 189 ≤ 64 * k.den)
    (hP : 0 ≤ P_s2c1_cons k) (hpos : 0 < (254 * k.den + 760 * k.num) + (128 * k.den - 378 * k.num)) :
    ∀ e, Scat k ⟨254 * k.den + 760 * k.num, 128 * k.den - 378 * k.num, hpos⟩ (A_s2c1_cons e) (dW_s2c1_cons e) := by
  intro e
  have hN := k.num_le
  have hD := k.den_pos
  unfold P_s2c1_cons at hP
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 49) (q0 := 146) (p1 := 64) (q1 := 189)
    (by omega) (by omega)
  have hs0 : 378 * k.num ≤ 128 * k.den := by omega
  cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s2c1_cons, dW_s2c1_cons] <;>
  (constructor <;> apply Int.ofNat_le.mp <;>
    push_cast [Int.ofNat_sub hs0, Int.ofNat_sub hN] <;> grind)

theorem unsafe_s2c1_cons (k : Kappa) (H_KAPPA : ¬ Below_s2c1_cons k) :
    ∃ c d, (∀ e, Scat k c (A_s2c1_cons e) (d e)) ∧ ¬ Safe F1 G1 false (dlOf d) := by
  by_cases hfix : 64 * k.den ≤ k.num * 189
  · refine ⟨Corner.fast, dW_s2c1_cons, ?_, not_safe1 (by decide) (by decide) (by decide)⟩
    intro e; have := k.num_le
    cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, Corner.fast, A_s2c1_cons, dW_s2c1_cons] <;> omega
  · have hP := pos_s2c1_cons k (by omega) H_KAPPA
    have hlo := lo_s2c1_cons k hP
    have hD := k.den_pos
    exact ⟨_, dW_s2c1_cons, wit_s2c1_cons k hlo (by omega) hP (by omega), not_safe1 (by decide) (by decide) (by decide)⟩

/-- **Exact threshold, seed 2, client 1, `cons`.** Every assignment within κ at every corner is
safe iff `Below_s2c1_cons κ` (i.e. κ < κ_ex ≈ 0.3356387991); otherwise a violating whole-ps assignment exists. -/
theorem exact_s2c1_cons (k : Kappa) :
    (∀ c d, (∀ e, Scat k c (A_s2c1_cons e) (d e)) → Safe F1 G1 false (dlOf d)) ↔ Below_s2c1_cons k := by
  constructor
  · intro hs; apply Classical.byContradiction; intro hb
    obtain ⟨c, d, h1, h2⟩ := unsafe_s2c1_cons k hb
    exact h2 (hs c d h1)
  · intro hb c d h; exact safe_s2c1_cons k hb c d h

/-- Bracket: κ_ex ∈ (3356387991/10000000000, 419548499/1250000000]. -/
theorem bracket_s2c1_cons : Below_s2c1_cons ⟨3356387991, 10000000000, by decide, by decide⟩ ∧
    ¬ Below_s2c1_cons ⟨419548499, 1250000000, by decide, by decide⟩ := by decide
theorem nonvac_s2c1_cons : Below_s2c1_cons Kappa.zero := by decide

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
  | .c => 172 | .wSt => 160 | .aSt => 32 | .wQf => 76 | .wQG => 144 | .aG => 32 | .wGC => 231 | .wAC => 600 | .aC => 45 | .wCf => 76

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

/-! ### Seed 3, client 1, `cons` -/

/-- Arc endpoints (F, S) ps, seed 3, client 1, `cons` (= `OnNetlistArbKappa.A_s3c1_cons`). -/
def A_s3c1_cons : Tab
  | .c => ⟨216, 652, by decide⟩
  | .wSt => ⟨178, 505, by decide⟩
  | .aSt => ⟨45, 100, by decide⟩
  | .wQf => ⟨286, 973, by decide⟩
  | .wQG => ⟨218, 543, by decide⟩
  | .aG => ⟨48, 93, by decide⟩
  | .wGC => ⟨274, 662, by decide⟩
  | .wAC => ⟨404, 809, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨69, 298, by decide⟩

theorem A_s3c1_cons_pos : ∀ e, 0 < (A_s3c1_cons e).F := by intro e; cases e <;> decide

/-- Box chain over `[0, 1]` (17 boxes) at `u = 932/2997`. -/
def pts_s3c1_cons : List Pt := [(8551671813, 38262779), (17070986529, 108882655), (1062892021, 10849803), (16941558143, 238311041), (8422243427, 167691165), (4170675343, 124291953), (16456201697, 723667487), (4025068409, 269898887), (3895640023, 399327273), (7419173437, 1170761155), (6852924249, 1737010343), (12055636579, 5124232605), (9628854345, 7551014839), (6037216639, 11142652545), (174573931, 4120393365), (0, 1)]
def sp_s3c1_cons : List (List Nat) := [[123, 32, 151, 34, 189, 530]]

theorem chain_s3c1_cons : chainOK A_s3c1_cons 932 2997 sp_s3c1_cons (1, 0) ((8567850361, 22084231) :: pts_s3c1_cons) = true := by
  decide +kernel
theorem last_s3c1_cons : lastPt (8567850361, 22084231) pts_s3c1_cons = (0, 1) := by decide +kernel

/-- `P(κ)·den²` for the binding vector `[123, 32, 151, 34, 189]`, late 530, binding early arc `wGC`:
the vector is realisable at some corner iff `P ≥ 0`. Its root in `[0, 1]` is
κ_ex ≈ 0.3109272633 (irrational: discriminant 64371431161 is not a square). -/
def P_s3c1_cons (k : Kappa) : Int :=
  -45782 * (k.num : Int) * k.num + 282185 * (k.num : Int) * k.den + -83313 * (k.den : Int) * k.den
/-- **κ < κ_ex** (`P < 0` below `u = 932/2997`). -/
def Below_s3c1_cons (k : Kappa) : Prop := k.num * 2997 < 932 * k.den ∧ P_s3c1_cons k < 0
instance (k : Kappa) : Decidable (Below_s3c1_cons k) := inferInstanceAs (Decidable (_ ∧ _))

theorem kill_s3c1_cons {k : Kappa} (hb : Below_s3c1_cons k) (c : Corner) (h1 : Scat k c (A_s3c1_cons .wGC) 189)
    (h2 : Scat k c (A_s3c1_cons .wAC) 530) : False := by
  obtain ⟨hk, hP⟩ := hb
  unfold P_s3c1_cons at hP
  obtain ⟨w0, w1, hw⟩ := c
  simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s3c1_cons] at h1 h2
  have hN := k.num_le
  generalize k.num = N at *
  generalize k.den = D at *
  obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Nat.add_sub_cancel_left] at h1 h2
  have j1 := Int.ofNat_le.mpr h1.1
  have j2 := Int.ofNat_le.mpr h2.2
  push_cast at j1 j2
  simp only [Int.natCast_add] at hP
  have i1 : (w0 : Int) * ((L : Int) * 274 - (N + L) * 189) + (w1 : Int) * ((L : Int) * 662 - (N + L) * 189) ≤ 0 := by
    grind
  have i2 : (w0 : Int) * (((N : Int) + L) * 530 - (N + N + L) * 404) +
      (w1 : Int) * (((N : Int) + L) * 530 - (N + N + L) * 809) ≤ 0 := by
    grind
  have := elim2 (by omega) (by omega) (by omega) (by omega) (by omega) i1 i2
  grind

theorem safe_s3c1_cons (k : Kappa) (H_BELOW : Below_s3c1_cons k) (c : Corner) (d : Arc → Nat)
    (H_SCAT : ∀ e, Scat k c (A_s3c1_cons e) (d e)) : Safe F1 G1 false (dlOf d) := by
  apply safe1_of_le
  rcases cover_sound (A_s3c1_cons_pos) (by decide) (by decide) chain_s3c1_cons last_s3c1_cons H_BELOW.1 c d H_SCAT with h | h
  · exact h
  · exfalso
    simp only [sp_s3c1_cons, vec, List.mem_singleton, List.cons.injEq, and_true] at h
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h
    have s1 := H_SCAT .wGC
    have s2 := H_SCAT .wAC
    rw [e5] at s1
    rw [e6] at s2
    exact kill_s3c1_cons H_BELOW c s1 s2

/-- The violating assignment (binding vector, other arcs at their fast endpoint). -/
def dW_s3c1_cons : Arc → Nat
  | .c => 216 | .wSt => 123 | .aSt => 32 | .wQf => 286 | .wQG => 151 | .aG => 34 | .wGC => 189 | .wAC => 530 | .aC => 45 | .wCf => 69

/-- Between `u` and `κ_fix = 63/202`, `P ≥ 0` (Bernstein certificate). -/
theorem pos_s3c1_cons (k : Kappa) (hfix : k.num * 202 < 63 * k.den) (hb : ¬ Below_s3c1_cons k) : 0 ≤ P_s3c1_cons k := by
  unfold Below_s3c1_cons at hb
  by_cases hu : k.num * 2997 < 932 * k.den
  · have := (not_and.mp hb) hu
    omega
  · unfold P_s3c1_cons
    obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 932) (q0 := 2997) (p1 := 63) (q1 := 202)
      (by omega) (by omega)
    grind

/-- `P ≥ 0` forces `κ ≥ κ_lo = 1127/3625` (`P < 0` on `[0, κ_lo)`, Bernstein certificate). -/
theorem lo_s3c1_cons (k : Kappa) (hP : 0 ≤ P_s3c1_cons k) : 1127 * k.den ≤ 3625 * k.num := by
  apply Classical.byContradiction; intro h
  unfold P_s3c1_cons at hP
  have hv : (0 : Int) < 1127 * (k.den : Int) - 3625 * k.num := by omega
  have hv2 := Int.mul_pos hv hv
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 0) (q0 := 1) (p1 := 1127) (q1 := 3625)
    (by omega) (by omega)
  grind

/-- On `[κ_lo, κ_fix]` with `P ≥ 0`: the binding vector is realised at the corner where the
late arc is exactly at `(1+κ)·nominal` (`w0 = (den+num)·809 − den·530`, `w1 = den·530 − (den+num)·404`). -/
theorem wit_s3c1_cons (k : Kappa) (hlo : 1127 * k.den ≤ 3625 * k.num) (hfix : k.num * 202 ≤ 63 * k.den)
    (hP : 0 ≤ P_s3c1_cons k) (hpos : 0 < (279 * k.den + 809 * k.num) + (126 * k.den - 404 * k.num)) :
    ∀ e, Scat k ⟨279 * k.den + 809 * k.num, 126 * k.den - 404 * k.num, hpos⟩ (A_s3c1_cons e) (dW_s3c1_cons e) := by
  intro e
  have hN := k.num_le
  have hD := k.den_pos
  unfold P_s3c1_cons at hP
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 1127) (q0 := 3625) (p1 := 63) (q1 := 202)
    (by omega) (by omega)
  have hs0 : 404 * k.num ≤ 126 * k.den := by omega
  cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s3c1_cons, dW_s3c1_cons] <;>
  (constructor <;> apply Int.ofNat_le.mp <;>
    push_cast [Int.ofNat_sub hs0, Int.ofNat_sub hN] <;> grind)

theorem unsafe_s3c1_cons (k : Kappa) (H_KAPPA : ¬ Below_s3c1_cons k) :
    ∃ c d, (∀ e, Scat k c (A_s3c1_cons e) (d e)) ∧ ¬ Safe F1 G1 false (dlOf d) := by
  by_cases hfix : 63 * k.den ≤ k.num * 202
  · refine ⟨Corner.fast, dW_s3c1_cons, ?_, not_safe1 (by decide) (by decide) (by decide)⟩
    intro e; have := k.num_le
    cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, Corner.fast, A_s3c1_cons, dW_s3c1_cons] <;> omega
  · have hP := pos_s3c1_cons k (by omega) H_KAPPA
    have hlo := lo_s3c1_cons k hP
    have hD := k.den_pos
    exact ⟨_, dW_s3c1_cons, wit_s3c1_cons k hlo (by omega) hP (by omega), not_safe1 (by decide) (by decide) (by decide)⟩

/-- **Exact threshold, seed 3, client 1, `cons`.** Every assignment within κ at every corner is
safe iff `Below_s3c1_cons κ` (i.e. κ < κ_ex ≈ 0.3109272633); otherwise a violating whole-ps assignment exists. -/
theorem exact_s3c1_cons (k : Kappa) :
    (∀ c d, (∀ e, Scat k c (A_s3c1_cons e) (d e)) → Safe F1 G1 false (dlOf d)) ↔ Below_s3c1_cons k := by
  constructor
  · intro hs; apply Classical.byContradiction; intro hb
    obtain ⟨c, d, h1, h2⟩ := unsafe_s3c1_cons k hb
    exact h2 (hs c d h1)
  · intro hb c d h; exact safe_s3c1_cons k hb c d h

/-- Bracket: κ_ex ∈ (388659079/1250000000, 3109272633/10000000000]. -/
theorem bracket_s3c1_cons : Below_s3c1_cons ⟨388659079, 1250000000, by decide, by decide⟩ ∧
    ¬ Below_s3c1_cons ⟨3109272633, 10000000000, by decide, by decide⟩ := by decide
theorem nonvac_s3c1_cons : Below_s3c1_cons Kappa.zero := by decide

/-! ### Seed 3, client 2, `cons` -/

/-- Arc endpoints (F, S) ps, seed 3, client 2, `cons` (= `OnNetlistArbKappa.A_s3c2_cons`). -/
def A_s3c2_cons : Tab
  | .c => ⟨216, 652, by decide⟩
  | .wSt => ⟨178, 505, by decide⟩
  | .aSt => ⟨45, 100, by decide⟩
  | .wQf => ⟨286, 973, by decide⟩
  | .wQG => ⟨218, 543, by decide⟩
  | .aG => ⟨45, 100, by decide⟩
  | .wGC => ⟨268, 677, by decide⟩
  | .wAC => ⟨461, 965, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨211, 685, by decide⟩

theorem A_s3c2_cons_pos : ∀ e, 0 < (A_s3c2_cons e).F := by intro e; cases e <;> decide

/-- Box chain over `[0, 1]` (18 boxes) at `u = 257/1053`. -/
def pts_s3c2_cons : List Pt := [(17084347405, 95521779), (17029547931, 150321253), (8487374229, 102560363), (16892549247, 287319937), (4202587509, 92379787), (2084168919, 63314729), (8227076729, 362857863), (16180156089, 999713095), (15769160037, 1410709147), (3805291325, 489675971), (3613493167, 681474129), (13357983195, 3821885989), (5884399229, 2705535363), (9522020037, 7657849147), (6371050301, 10808818883), (1877493459, 15302375725), (0, 1)]
def sp_s3c2_cons : List (List Nat) := [[135, 35, 165, 35, 203, 574]]

theorem chain_s3c2_cons : chainOK A_s3c2_cons 257 1053 sp_s3c2_cons (1, 0) ((17139146879, 40722305) :: pts_s3c2_cons) = true := by
  decide +kernel
theorem last_s3c2_cons : lastPt (17139146879, 40722305) pts_s3c2_cons = (0, 1) := by decide +kernel

/-- `P(κ)·den²` for the binding vector `[135, 35, 165, 35, 203]`, late 574, binding early arc `wQG`:
the vector is realisable at some corner iff `P ≥ 0`. Its root in `[0, 1]` is
κ_ex ≈ 0.2440255855 (irrational: discriminant 62605490256 is not a square). -/
def P_s3c2_cons (k : Kappa) : Int :=
  -39953 * (k.num : Int) * k.num + 269710 * (k.num : Int) * k.den + -63437 * (k.den : Int) * k.den
/-- **κ < κ_ex** (`P < 0` below `u = 257/1053`). -/
def Below_s3c2_cons (k : Kappa) : Prop := k.num * 1053 < 257 * k.den ∧ P_s3c2_cons k < 0
instance (k : Kappa) : Decidable (Below_s3c2_cons k) := inferInstanceAs (Decidable (_ ∧ _))

theorem kill_s3c2_cons {k : Kappa} (hb : Below_s3c2_cons k) (c : Corner) (h1 : Scat k c (A_s3c2_cons .wQG) 165)
    (h2 : Scat k c (A_s3c2_cons .wAC) 574) : False := by
  obtain ⟨hk, hP⟩ := hb
  unfold P_s3c2_cons at hP
  obtain ⟨w0, w1, hw⟩ := c
  simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s3c2_cons] at h1 h2
  have hN := k.num_le
  generalize k.num = N at *
  generalize k.den = D at *
  obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Nat.add_sub_cancel_left] at h1 h2
  have j1 := Int.ofNat_le.mpr h1.1
  have j2 := Int.ofNat_le.mpr h2.2
  push_cast at j1 j2
  simp only [Int.natCast_add] at hP
  have i1 : (w0 : Int) * ((L : Int) * 218 - (N + L) * 165) + (w1 : Int) * ((L : Int) * 543 - (N + L) * 165) ≤ 0 := by
    grind
  have i2 : (w0 : Int) * (((N : Int) + L) * 574 - (N + N + L) * 461) +
      (w1 : Int) * (((N : Int) + L) * 574 - (N + N + L) * 965) ≤ 0 := by
    grind
  have := elim2 (by omega) (by omega) (by omega) (by omega) (by omega) i1 i2
  grind

theorem safe_s3c2_cons (k : Kappa) (H_BELOW : Below_s3c2_cons k) (c : Corner) (d : Arc → Nat)
    (H_SCAT : ∀ e, Scat k c (A_s3c2_cons e) (d e)) : Safe F2 G2 true (dlOf d) := by
  apply safe2_of_le
  rcases cover_sound (A_s3c2_cons_pos) (by decide) (by decide) chain_s3c2_cons last_s3c2_cons H_BELOW.1 c d H_SCAT with h | h
  · exact h
  · exfalso
    simp only [sp_s3c2_cons, vec, List.mem_singleton, List.cons.injEq, and_true] at h
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h
    have s1 := H_SCAT .wQG
    have s2 := H_SCAT .wAC
    rw [e3] at s1
    rw [e6] at s2
    exact kill_s3c2_cons H_BELOW c s1 s2

/-- The violating assignment (binding vector, other arcs at their fast endpoint). -/
def dW_s3c2_cons : Arc → Nat
  | .c => 216 | .wSt => 135 | .aSt => 35 | .wQf => 286 | .wQG => 165 | .aG => 35 | .wGC => 203 | .wAC => 574 | .aC => 45 | .wCf => 211

/-- Between `u` and `κ_fix = 113/461`, `P ≥ 0` (Bernstein certificate). -/
theorem pos_s3c2_cons (k : Kappa) (hfix : k.num * 461 < 113 * k.den) (hb : ¬ Below_s3c2_cons k) : 0 ≤ P_s3c2_cons k := by
  unfold Below_s3c2_cons at hb
  by_cases hu : k.num * 1053 < 257 * k.den
  · have := (not_and.mp hb) hu
    omega
  · unfold P_s3c2_cons
    obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 257) (q0 := 1053) (p1 := 113) (q1 := 461)
      (by omega) (by omega)
    grind

/-- `P ≥ 0` forces `κ ≥ κ_lo = 783/3209` (`P < 0` on `[0, κ_lo)`, Bernstein certificate). -/
theorem lo_s3c2_cons (k : Kappa) (hP : 0 ≤ P_s3c2_cons k) : 783 * k.den ≤ 3209 * k.num := by
  apply Classical.byContradiction; intro h
  unfold P_s3c2_cons at hP
  have hv : (0 : Int) < 783 * (k.den : Int) - 3209 * k.num := by omega
  have hv2 := Int.mul_pos hv hv
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 0) (q0 := 1) (p1 := 783) (q1 := 3209)
    (by omega) (by omega)
  grind

/-- On `[κ_lo, κ_fix]` with `P ≥ 0`: the binding vector is realised at the corner where the
late arc is exactly at `(1+κ)·nominal` (`w0 = (den+num)·965 − den·574`, `w1 = den·574 − (den+num)·461`). -/
theorem wit_s3c2_cons (k : Kappa) (hlo : 783 * k.den ≤ 3209 * k.num) (hfix : k.num * 461 ≤ 113 * k.den)
    (hP : 0 ≤ P_s3c2_cons k) (hpos : 0 < (391 * k.den + 965 * k.num) + (113 * k.den - 461 * k.num)) :
    ∀ e, Scat k ⟨391 * k.den + 965 * k.num, 113 * k.den - 461 * k.num, hpos⟩ (A_s3c2_cons e) (dW_s3c2_cons e) := by
  intro e
  have hN := k.num_le
  have hD := k.den_pos
  unfold P_s3c2_cons at hP
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 783) (q0 := 3209) (p1 := 113) (q1 := 461)
    (by omega) (by omega)
  have hs0 : 461 * k.num ≤ 113 * k.den := by omega
  cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s3c2_cons, dW_s3c2_cons] <;>
  (constructor <;> apply Int.ofNat_le.mp <;>
    push_cast [Int.ofNat_sub hs0, Int.ofNat_sub hN] <;> grind)

theorem unsafe_s3c2_cons (k : Kappa) (H_KAPPA : ¬ Below_s3c2_cons k) :
    ∃ c d, (∀ e, Scat k c (A_s3c2_cons e) (d e)) ∧ ¬ Safe F2 G2 true (dlOf d) := by
  by_cases hfix : 113 * k.den ≤ k.num * 461
  · refine ⟨Corner.fast, dW_s3c2_cons, ?_, not_safe2 (by decide) (by decide) (by decide)⟩
    intro e; have := k.num_le
    cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, Corner.fast, A_s3c2_cons, dW_s3c2_cons] <;> omega
  · have hP := pos_s3c2_cons k (by omega) H_KAPPA
    have hlo := lo_s3c2_cons k hP
    have hD := k.den_pos
    exact ⟨_, dW_s3c2_cons, wit_s3c2_cons k hlo (by omega) hP (by omega), not_safe2 (by decide) (by decide) (by decide)⟩

/-- **Exact threshold, seed 3, client 2, `cons`.** Every assignment within κ at every corner is
safe iff `Below_s3c2_cons κ` (i.e. κ < κ_ex ≈ 0.2440255855); otherwise a violating whole-ps assignment exists. -/
theorem exact_s3c2_cons (k : Kappa) :
    (∀ c d, (∀ e, Scat k c (A_s3c2_cons e) (d e)) → Safe F2 G2 true (dlOf d)) ↔ Below_s3c2_cons k := by
  constructor
  · intro hs; apply Classical.byContradiction; intro hb
    obtain ⟨c, d, h1, h2⟩ := unsafe_s3c2_cons k hb
    exact h2 (hs c d h1)
  · intro hb c d h; exact safe_s3c2_cons k hb c d h

/-- Bracket: κ_ex ∈ (488051171/2000000000, 152515991/625000000]. -/
theorem bracket_s3c2_cons : Below_s3c2_cons ⟨488051171, 2000000000, by decide, by decide⟩ ∧
    ¬ Below_s3c2_cons ⟨152515991, 625000000, by decide, by decide⟩ := by decide
theorem nonvac_s3c2_cons : Below_s3c2_cons Kappa.zero := by decide

/-! ### Seed 4, client 1, `cons` -/

/-- Arc endpoints (F, S) ps, seed 4, client 1, `cons` (= `OnNetlistArbKappa.A_s4c1_cons`). -/
def A_s4c1_cons : Tab
  | .c => ⟨172, 522, by decide⟩
  | .wSt => ⟨312, 749, by decide⟩
  | .aSt => ⟨45, 100, by decide⟩
  | .wQf => ⟨76, 288, by decide⟩
  | .wQG => ⟨172, 434, by decide⟩
  | .aG => ⟨48, 93, by decide⟩
  | .wGC => ⟨127, 356, by decide⟩
  | .wAC => ⟨464, 978, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨214, 689, by decide⟩

theorem A_s4c1_cons_pos : ∀ e, 0 < (A_s4c1_cons e).F := by intro e; cases e <;> decide

/-- Box chain over `[0, 1]` (19 boxes) at `u = 241/1158`. -/
def pts_s4c1_cons : List Pt := [(8528605733, 61328859), (17029545389, 150323795), (8459440541, 130494051), (8404108387, 185826205), (16697552467, 482316717), (8265778003, 324156589), (16282561315, 897307869), (7989117235, 600817357), (7795454697, 794479895), (15065253935, 2114615249), (1803616771, 343866877), (13571285787, 3608583397), (6232321357, 2357613235), (5485337283, 3104597309), (1125797889, 1021685759), (6488770121, 10691099063), (1570587413, 7019347179), (0, 1)]
def sp_s4c1_cons : List (List Nat) := [[248, 36, 137, 39, 101, 562]]

theorem chain_s4c1_cons : chainOK A_s4c1_cons 241 1158 sp_s4c1_cons (1, 0) ((17112543619, 67325565) :: pts_s4c1_cons) = true := by
  decide +kernel
theorem last_s4c1_cons : lastPt (17112543619, 67325565) pts_s4c1_cons = (0, 1) := by decide +kernel

/-- `P(κ)·den²` for the binding vector `[248, 36, 137, 39, 101]`, late 562, binding early arc `wGC`:
the vector is realisable at some corner iff `P ≥ 0`. Its root in `[0, 1]` is
κ_ex ≈ 0.2080707755 (irrational: discriminant 26751661472 is not a square). -/
def P_s4c1_cons (k : Kappa) : Int :=
  -40978 * (k.num : Int) * k.num + 180612 * (k.num : Int) * k.den + -35806 * (k.den : Int) * k.den
/-- **κ < κ_ex** (`P < 0` below `u = 241/1158`). -/
def Below_s4c1_cons (k : Kappa) : Prop := k.num * 1158 < 241 * k.den ∧ P_s4c1_cons k < 0
instance (k : Kappa) : Decidable (Below_s4c1_cons k) := inferInstanceAs (Decidable (_ ∧ _))

theorem kill_s4c1_cons {k : Kappa} (hb : Below_s4c1_cons k) (c : Corner) (h1 : Scat k c (A_s4c1_cons .wGC) 101)
    (h2 : Scat k c (A_s4c1_cons .wAC) 562) : False := by
  obtain ⟨hk, hP⟩ := hb
  unfold P_s4c1_cons at hP
  obtain ⟨w0, w1, hw⟩ := c
  simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s4c1_cons] at h1 h2
  have hN := k.num_le
  generalize k.num = N at *
  generalize k.den = D at *
  obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Nat.add_sub_cancel_left] at h1 h2
  have j1 := Int.ofNat_le.mpr h1.1
  have j2 := Int.ofNat_le.mpr h2.2
  push_cast at j1 j2
  simp only [Int.natCast_add] at hP
  have i1 : (w0 : Int) * ((L : Int) * 127 - (N + L) * 101) + (w1 : Int) * ((L : Int) * 356 - (N + L) * 101) ≤ 0 := by
    grind
  have i2 : (w0 : Int) * (((N : Int) + L) * 562 - (N + N + L) * 464) +
      (w1 : Int) * (((N : Int) + L) * 562 - (N + N + L) * 978) ≤ 0 := by
    grind
  have := elim2 (by omega) (by omega) (by omega) (by omega) (by omega) i1 i2
  grind

theorem safe_s4c1_cons (k : Kappa) (H_BELOW : Below_s4c1_cons k) (c : Corner) (d : Arc → Nat)
    (H_SCAT : ∀ e, Scat k c (A_s4c1_cons e) (d e)) : Safe F1 G1 false (dlOf d) := by
  apply safe1_of_le
  rcases cover_sound (A_s4c1_cons_pos) (by decide) (by decide) chain_s4c1_cons last_s4c1_cons H_BELOW.1 c d H_SCAT with h | h
  · exact h
  · exfalso
    simp only [sp_s4c1_cons, vec, List.mem_singleton, List.cons.injEq, and_true] at h
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h
    have s1 := H_SCAT .wGC
    have s2 := H_SCAT .wAC
    rw [e5] at s1
    rw [e6] at s2
    exact kill_s4c1_cons H_BELOW c s1 s2

/-- The violating assignment (binding vector, other arcs at their fast endpoint). -/
def dW_s4c1_cons : Arc → Nat
  | .c => 172 | .wSt => 248 | .aSt => 36 | .wQf => 76 | .wQG => 137 | .aG => 39 | .wGC => 101 | .wAC => 562 | .aC => 45 | .wCf => 214

/-- Between `u` and `κ_fix = 49/232`, `P ≥ 0` (Bernstein certificate). -/
theorem pos_s4c1_cons (k : Kappa) (hfix : k.num * 232 < 49 * k.den) (hb : ¬ Below_s4c1_cons k) : 0 ≤ P_s4c1_cons k := by
  unfold Below_s4c1_cons at hb
  by_cases hu : k.num * 1158 < 241 * k.den
  · have := (not_and.mp hb) hu
    omega
  · unfold P_s4c1_cons
    obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 241) (q0 := 1158) (p1 := 49) (q1 := 232)
      (by omega) (by omega)
    grind

/-- `P ≥ 0` forces `κ ≥ κ_lo = 31/149` (`P < 0` on `[0, κ_lo)`, Bernstein certificate). -/
theorem lo_s4c1_cons (k : Kappa) (hP : 0 ≤ P_s4c1_cons k) : 31 * k.den ≤ 149 * k.num := by
  apply Classical.byContradiction; intro h
  unfold P_s4c1_cons at hP
  have hv : (0 : Int) < 31 * (k.den : Int) - 149 * k.num := by omega
  have hv2 := Int.mul_pos hv hv
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 0) (q0 := 1) (p1 := 31) (q1 := 149)
    (by omega) (by omega)
  grind

/-- On `[κ_lo, κ_fix]` with `P ≥ 0`: the binding vector is realised at the corner where the
late arc is exactly at `(1+κ)·nominal` (`w0 = (den+num)·978 − den·562`, `w1 = den·562 − (den+num)·464`). -/
theorem wit_s4c1_cons (k : Kappa) (hlo : 31 * k.den ≤ 149 * k.num) (hfix : k.num * 232 ≤ 49 * k.den)
    (hP : 0 ≤ P_s4c1_cons k) (hpos : 0 < (416 * k.den + 978 * k.num) + (98 * k.den - 464 * k.num)) :
    ∀ e, Scat k ⟨416 * k.den + 978 * k.num, 98 * k.den - 464 * k.num, hpos⟩ (A_s4c1_cons e) (dW_s4c1_cons e) := by
  intro e
  have hN := k.num_le
  have hD := k.den_pos
  unfold P_s4c1_cons at hP
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 31) (q0 := 149) (p1 := 49) (q1 := 232)
    (by omega) (by omega)
  have hs0 : 464 * k.num ≤ 98 * k.den := by omega
  cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s4c1_cons, dW_s4c1_cons] <;>
  (constructor <;> apply Int.ofNat_le.mp <;>
    push_cast [Int.ofNat_sub hs0, Int.ofNat_sub hN] <;> grind)

theorem unsafe_s4c1_cons (k : Kappa) (H_KAPPA : ¬ Below_s4c1_cons k) :
    ∃ c d, (∀ e, Scat k c (A_s4c1_cons e) (d e)) ∧ ¬ Safe F1 G1 false (dlOf d) := by
  by_cases hfix : 49 * k.den ≤ k.num * 232
  · refine ⟨Corner.fast, dW_s4c1_cons, ?_, not_safe1 (by decide) (by decide) (by decide)⟩
    intro e; have := k.num_le
    cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, Corner.fast, A_s4c1_cons, dW_s4c1_cons] <;> omega
  · have hP := pos_s4c1_cons k (by omega) H_KAPPA
    have hlo := lo_s4c1_cons k hP
    have hD := k.den_pos
    exact ⟨_, dW_s4c1_cons, wit_s4c1_cons k hlo (by omega) hP (by omega), not_safe1 (by decide) (by decide) (by decide)⟩

/-- **Exact threshold, seed 4, client 1, `cons`.** Every assignment within κ at every corner is
safe iff `Below_s4c1_cons κ` (i.e. κ < κ_ex ≈ 0.2080707755); otherwise a violating whole-ps assignment exists. -/
theorem exact_s4c1_cons (k : Kappa) :
    (∀ c d, (∀ e, Scat k c (A_s4c1_cons e) (d e)) → Safe F1 G1 false (dlOf d)) ↔ Below_s4c1_cons k := by
  constructor
  · intro hs; apply Classical.byContradiction; intro hb
    obtain ⟨c, d, h1, h2⟩ := unsafe_s4c1_cons k hb
    exact h2 (hs c d h1)
  · intro hb c d h; exact safe_s4c1_cons k hb c d h

/-- Bracket: κ_ex ∈ (1040353877/5000000000, 416141551/2000000000]. -/
theorem bracket_s4c1_cons : Below_s4c1_cons ⟨1040353877, 5000000000, by decide, by decide⟩ ∧
    ¬ Below_s4c1_cons ⟨416141551, 2000000000, by decide, by decide⟩ := by decide
theorem nonvac_s4c1_cons : Below_s4c1_cons Kappa.zero := by decide

/-! ### Seed 4, client 2, `cons` -/

/-- Arc endpoints (F, S) ps, seed 4, client 2, `cons` (= `OnNetlistArbKappa.A_s4c2_cons`). -/
def A_s4c2_cons : Tab
  | .c => ⟨172, 522, by decide⟩
  | .wSt => ⟨312, 749, by decide⟩
  | .aSt => ⟨45, 100, by decide⟩
  | .wQf => ⟨76, 288, by decide⟩
  | .wQG => ⟨172, 434, by decide⟩
  | .aG => ⟨45, 100, by decide⟩
  | .wGC => ⟨258, 671, by decide⟩
  | .wAC => ⟨468, 942, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨71, 274, by decide⟩

theorem A_s4c2_cons_pos : ∀ e, 0 < (A_s4c2_cons e).F := by intro e; cases e <;> decide

/-- Box chain over `[0, 1]` (17 boxes) at `u = 13/46`. -/
def pts_s4c2_cons : List Pt := [(17102465783, 77403401), (8522974507, 66960085), (16989432245, 190436939), (16904657091, 275212093), (8409940969, 179993623), (8311036623, 278897969), (16367747785, 812121399), (15972130401, 1207738783), (15435221095, 1744648089), (14643986327, 2535882857), (842837035, 230904789), (11874664641, 5305204543), (9529218723, 7650650461), (191819143, 345051769), (78094503, 995647321), (0, 1)]
def sp_s4c2_cons : List (List Nat) := [[225, 33, 124, 33, 186, 602]]

theorem chain_s4c2_cons : chainOK A_s4c2_cons 13 46 sp_s4c2_cons (1, 0) ((2144872819, 2610829) :: pts_s4c2_cons) = true := by
  decide +kernel
theorem last_s4c2_cons : lastPt (2144872819, 2610829) pts_s4c2_cons = (0, 1) := by decide +kernel

/-- `P(κ)·den²` for the binding vector `[225, 33, 124, 33, 186]`, late 602, binding early arc `wGC`:
the vector is realisable at some corner iff `P ≥ 0`. Its root in `[0, 1]` is
κ_ex ≈ 0.2824744854 (irrational: discriminant 88020887140 is not a square). -/
def P_s4c2_cons (k : Kappa) : Int :=
  -70992 * (k.num : Int) * k.num + 336790 * (k.num : Int) * k.den + -89470 * (k.den : Int) * k.den
/-- **κ < κ_ex** (`P < 0` below `u = 13/46`). -/
def Below_s4c2_cons (k : Kappa) : Prop := k.num * 46 < 13 * k.den ∧ P_s4c2_cons k < 0
instance (k : Kappa) : Decidable (Below_s4c2_cons k) := inferInstanceAs (Decidable (_ ∧ _))

theorem kill_s4c2_cons {k : Kappa} (hb : Below_s4c2_cons k) (c : Corner) (h1 : Scat k c (A_s4c2_cons .wGC) 186)
    (h2 : Scat k c (A_s4c2_cons .wAC) 602) : False := by
  obtain ⟨hk, hP⟩ := hb
  unfold P_s4c2_cons at hP
  obtain ⟨w0, w1, hw⟩ := c
  simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s4c2_cons] at h1 h2
  have hN := k.num_le
  generalize k.num = N at *
  generalize k.den = D at *
  obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Nat.add_sub_cancel_left] at h1 h2
  have j1 := Int.ofNat_le.mpr h1.1
  have j2 := Int.ofNat_le.mpr h2.2
  push_cast at j1 j2
  simp only [Int.natCast_add] at hP
  have i1 : (w0 : Int) * ((L : Int) * 258 - (N + L) * 186) + (w1 : Int) * ((L : Int) * 671 - (N + L) * 186) ≤ 0 := by
    grind
  have i2 : (w0 : Int) * (((N : Int) + L) * 602 - (N + N + L) * 468) +
      (w1 : Int) * (((N : Int) + L) * 602 - (N + N + L) * 942) ≤ 0 := by
    grind
  have := elim2 (by omega) (by omega) (by omega) (by omega) (by omega) i1 i2
  grind

theorem safe_s4c2_cons (k : Kappa) (H_BELOW : Below_s4c2_cons k) (c : Corner) (d : Arc → Nat)
    (H_SCAT : ∀ e, Scat k c (A_s4c2_cons e) (d e)) : Safe F2 G2 true (dlOf d) := by
  apply safe2_of_le
  rcases cover_sound (A_s4c2_cons_pos) (by decide) (by decide) chain_s4c2_cons last_s4c2_cons H_BELOW.1 c d H_SCAT with h | h
  · exact h
  · exfalso
    simp only [sp_s4c2_cons, vec, List.mem_singleton, List.cons.injEq, and_true] at h
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h
    have s1 := H_SCAT .wGC
    have s2 := H_SCAT .wAC
    rw [e5] at s1
    rw [e6] at s2
    exact kill_s4c2_cons H_BELOW c s1 s2

/-- The violating assignment (binding vector, other arcs at their fast endpoint). -/
def dW_s4c2_cons : Arc → Nat
  | .c => 172 | .wSt => 225 | .aSt => 33 | .wQf => 76 | .wQG => 124 | .aG => 33 | .wGC => 186 | .wAC => 602 | .aC => 45 | .wCf => 71

/-- Between `u` and `κ_fix = 67/234`, `P ≥ 0` (Bernstein certificate). -/
theorem pos_s4c2_cons (k : Kappa) (hfix : k.num * 234 < 67 * k.den) (hb : ¬ Below_s4c2_cons k) : 0 ≤ P_s4c2_cons k := by
  unfold Below_s4c2_cons at hb
  by_cases hu : k.num * 46 < 13 * k.den
  · have := (not_and.mp hb) hu
    omega
  · unfold P_s4c2_cons
    obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 13) (q0 := 46) (p1 := 67) (q1 := 234)
      (by omega) (by omega)
    grind

/-- `P ≥ 0` forces `κ ≥ κ_lo = 731/2588` (`P < 0` on `[0, κ_lo)`, Bernstein certificate). -/
theorem lo_s4c2_cons (k : Kappa) (hP : 0 ≤ P_s4c2_cons k) : 731 * k.den ≤ 2588 * k.num := by
  apply Classical.byContradiction; intro h
  unfold P_s4c2_cons at hP
  have hv : (0 : Int) < 731 * (k.den : Int) - 2588 * k.num := by omega
  have hv2 := Int.mul_pos hv hv
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 0) (q0 := 1) (p1 := 731) (q1 := 2588)
    (by omega) (by omega)
  grind

/-- On `[κ_lo, κ_fix]` with `P ≥ 0`: the binding vector is realised at the corner where the
late arc is exactly at `(1+κ)·nominal` (`w0 = (den+num)·942 − den·602`, `w1 = den·602 − (den+num)·468`). -/
theorem wit_s4c2_cons (k : Kappa) (hlo : 731 * k.den ≤ 2588 * k.num) (hfix : k.num * 234 ≤ 67 * k.den)
    (hP : 0 ≤ P_s4c2_cons k) (hpos : 0 < (340 * k.den + 942 * k.num) + (134 * k.den - 468 * k.num)) :
    ∀ e, Scat k ⟨340 * k.den + 942 * k.num, 134 * k.den - 468 * k.num, hpos⟩ (A_s4c2_cons e) (dW_s4c2_cons e) := by
  intro e
  have hN := k.num_le
  have hD := k.den_pos
  unfold P_s4c2_cons at hP
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 731) (q0 := 2588) (p1 := 67) (q1 := 234)
    (by omega) (by omega)
  have hs0 : 468 * k.num ≤ 134 * k.den := by omega
  cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s4c2_cons, dW_s4c2_cons] <;>
  (constructor <;> apply Int.ofNat_le.mp <;>
    push_cast [Int.ofNat_sub hs0, Int.ofNat_sub hN] <;> grind)

theorem unsafe_s4c2_cons (k : Kappa) (H_KAPPA : ¬ Below_s4c2_cons k) :
    ∃ c d, (∀ e, Scat k c (A_s4c2_cons e) (d e)) ∧ ¬ Safe F2 G2 true (dlOf d) := by
  by_cases hfix : 67 * k.den ≤ k.num * 234
  · refine ⟨Corner.fast, dW_s4c2_cons, ?_, not_safe2 (by decide) (by decide) (by decide)⟩
    intro e; have := k.num_le
    cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, Corner.fast, A_s4c2_cons, dW_s4c2_cons] <;> omega
  · have hP := pos_s4c2_cons k (by omega) H_KAPPA
    have hlo := lo_s4c2_cons k hP
    have hD := k.den_pos
    exact ⟨_, dW_s4c2_cons, wit_s4c2_cons k hlo (by omega) hP (by omega), not_safe2 (by decide) (by decide) (by decide)⟩

/-- **Exact threshold, seed 4, client 2, `cons`.** Every assignment within κ at every corner is
safe iff `Below_s4c2_cons κ` (i.e. κ < κ_ex ≈ 0.2824744854); otherwise a violating whole-ps assignment exists. -/
theorem exact_s4c2_cons (k : Kappa) :
    (∀ c d, (∀ e, Scat k c (A_s4c2_cons e) (d e)) → Safe F2 G2 true (dlOf d)) ↔ Below_s4c2_cons k := by
  constructor
  · intro hs; apply Classical.byContradiction; intro hb
    obtain ⟨c, d, h1, h2⟩ := unsafe_s4c2_cons k hb
    exact h2 (hs c d h1)
  · intro hb c d h; exact safe_s4c2_cons k hb c d h

/-- Bracket: κ_ex ∈ (1412372427/5000000000, 564948971/2000000000]. -/
theorem bracket_s4c2_cons : Below_s4c2_cons ⟨1412372427, 5000000000, by decide, by decide⟩ ∧
    ¬ Below_s4c2_cons ⟨564948971, 2000000000, by decide, by decide⟩ := by decide
theorem nonvac_s4c2_cons : Below_s4c2_cons Kappa.zero := by decide

/-! ### Seed 1, client 1, `lit` -/

/-- Arc endpoints (F, S) ps, seed 1, client 1, `lit` (= `OnNetlistArbKappa.A_s1c1_lit`). -/
def A_s1c1_lit : Tab
  | .c => ⟨160, 488, by decide⟩
  | .wSt => ⟨262, 903, by decide⟩
  | .aSt => ⟨45, 124, by decide⟩
  | .wQf => ⟨76, 288, by decide⟩
  | .wQG => ⟨122, 429, by decide⟩
  | .aG => ⟨48, 116, by decide⟩
  | .wGC => ⟨209, 677, by decide⟩
  | .wAC => ⟨196, 795, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨71, 276, by decide⟩

theorem A_s1c1_lit_pos : ∀ e, 0 < (A_s1c1_lit e).F := by intro e; cases e <;> decide

/-- Box chain over `[0, 1]` (51 boxes) at `u = 1078/2253`. -/
def pts_s1c1_lit : List Pt := [(1817168775, 330314873), (13354010529, 3825858655), (12267665913, 4912203271), (11258917341, 5920951843), (646697739, 427044085), (9493607341, 7686261843), (8717646901, 8462222283), (3999941747, 4589992845), (114692455, 153743001), (209985899, 326885013), (6156977449, 11022891735), (5652603163, 11527266021), (5187026899, 11992842285), (4740849647, 12439019537), (4352869427, 12826999757), (3964889207, 13214979977), (908776505, 3386190791), (3344120855, 13835748329), (3072534701, 14107334483), (86923423, 449947489), (2568160415, 14611708769), (1177385647, 7412548945), (2141382173, 15038487011), (1947392063, 15232477121), (443200241, 3851767055), (404402219, 3890565077), (365604197, 3929363099), (326806175, 3968161121), (595415317, 7994519275), (134304571, 2013179077), (479021251, 8110913341), (861047447, 16318821737), (783451403, 16396417781), (362627185, 8227307407), (171614087, 4123353209), (589461293, 16590407891), (511865249, 16668003935), (473067227, 16706801957), (207435097, 8382499495), (94018043, 4200949253), (168637075, 8421297517), (9327379, 527543533), (279077117, 16900792067), (55220021, 4239747275), (91041031, 8498893561), (123885029, 17055984155), (85087007, 17094782177), (16421999, 4278545297), (13444987, 8576489605), (0, 1)]
def sp_s1c1_lit : List (List Nat) := [[471, 65, 224, 61, 353, 1175]]

theorem chain_s1c1_lit : chainOK A_s1c1_lit 1078 2253 sp_s1c1_lit (1, 0) ((7899142957, 690791635) :: pts_s1c1_lit) = true := by
  decide +kernel
theorem last_s1c1_lit : lastPt (7899142957, 690791635) pts_s1c1_lit = (0, 1) := by decide +kernel

/-- `P(κ)·den²` for the binding vector `[471, 65, 224, 61, 353]`, late 1175, binding early arc `wGC`:
the vector is realisable at some corner iff `P ≥ 0`. Its root in `[0, 1]` is
κ_ex ≈ 0.4784365954 (irrational: discriminant 629430954841 is not a square). -/
def P_s1c1_lit (k : Kappa) : Int :=
  33463 * (k.num : Int) * k.num + 761347 * (k.num : Int) * k.den + -371916 * (k.den : Int) * k.den
/-- **κ < κ_ex** (`P < 0` below `u = 1078/2253`). -/
def Below_s1c1_lit (k : Kappa) : Prop := k.num * 2253 < 1078 * k.den ∧ P_s1c1_lit k < 0
instance (k : Kappa) : Decidable (Below_s1c1_lit k) := inferInstanceAs (Decidable (_ ∧ _))

theorem kill_s1c1_lit {k : Kappa} (hb : Below_s1c1_lit k) (c : Corner) (h1 : Scat k c (A_s1c1_lit .wGC) 353)
    (h2 : Scat k c (A_s1c1_lit .wAC) 1175) : False := by
  obtain ⟨hk, hP⟩ := hb
  unfold P_s1c1_lit at hP
  obtain ⟨w0, w1, hw⟩ := c
  simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s1c1_lit] at h1 h2
  have hN := k.num_le
  generalize k.num = N at *
  generalize k.den = D at *
  obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Nat.add_sub_cancel_left] at h1 h2
  have j1 := Int.ofNat_le.mpr h1.1
  have j2 := Int.ofNat_le.mpr h2.2
  push_cast at j1 j2
  simp only [Int.natCast_add] at hP
  have i1 : (w0 : Int) * ((L : Int) * 209 - (N + L) * 353) + (w1 : Int) * ((L : Int) * 677 - (N + L) * 353) ≤ 0 := by
    grind
  have i2 : (w0 : Int) * (((N : Int) + L) * 1175 - (N + N + L) * 196) +
      (w1 : Int) * (((N : Int) + L) * 1175 - (N + N + L) * 795) ≤ 0 := by
    grind
  have := elim2 (by omega) (by omega) (by omega) (by omega) (by omega) i1 i2
  grind

theorem safe_s1c1_lit (k : Kappa) (H_BELOW : Below_s1c1_lit k) (c : Corner) (d : Arc → Nat)
    (H_SCAT : ∀ e, Scat k c (A_s1c1_lit e) (d e)) : Safe F1 G1 false (dlOf d) := by
  apply safe1_of_le
  rcases cover_sound (A_s1c1_lit_pos) (by decide) (by decide) chain_s1c1_lit last_s1c1_lit H_BELOW.1 c d H_SCAT with h | h
  · exact h
  · exfalso
    simp only [sp_s1c1_lit, vec, List.mem_singleton, List.cons.injEq, and_true] at h
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h
    have s1 := H_SCAT .wGC
    have s2 := H_SCAT .wAC
    rw [e5] at s1
    rw [e6] at s2
    exact kill_s1c1_lit H_BELOW c s1 s2

/-- The violating assignment (binding vector, other arcs at their slow endpoint). -/
def dW_s1c1_lit : Arc → Nat
  | .c => 488 | .wSt => 471 | .aSt => 65 | .wQf => 288 | .wQG => 224 | .aG => 61 | .wGC => 353 | .wAC => 1175 | .aC => 124 | .wCf => 276

/-- Between `u` and `κ_fix = 324/677`, `P ≥ 0` (Bernstein certificate). -/
theorem pos_s1c1_lit (k : Kappa) (hfix : k.num * 677 < 324 * k.den) (hb : ¬ Below_s1c1_lit k) : 0 ≤ P_s1c1_lit k := by
  unfold Below_s1c1_lit at hb
  by_cases hu : k.num * 2253 < 1078 * k.den
  · have := (not_and.mp hb) hu
    omega
  · unfold P_s1c1_lit
    obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 1078) (q0 := 2253) (p1 := 324) (q1 := 677)
      (by omega) (by omega)
    grind

/-- `P ≥ 0` forces `κ ≥ κ_lo = 277/579` (`P < 0` on `[0, κ_lo)`, Bernstein certificate). -/
theorem lo_s1c1_lit (k : Kappa) (hP : 0 ≤ P_s1c1_lit k) : 277 * k.den ≤ 579 * k.num := by
  apply Classical.byContradiction; intro h
  unfold P_s1c1_lit at hP
  have hv : (0 : Int) < 277 * (k.den : Int) - 579 * k.num := by omega
  have hv2 := Int.mul_pos hv hv
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 0) (q0 := 1) (p1 := 277) (q1 := 579)
    (by omega) (by omega)
  grind

/-- On `[κ_lo, κ_fix]` with `P ≥ 0`: the binding vector is realised at the corner where the
late arc is exactly at `(1+κ)·nominal` (`w0 = (den+num)·795 − den·1175`, `w1 = den·1175 − (den+num)·196`). -/
theorem wit_s1c1_lit (k : Kappa) (hlo : 277 * k.den ≤ 579 * k.num) (hfix : k.num * 677 ≤ 324 * k.den)
    (hP : 0 ≤ P_s1c1_lit k) (hpos : 0 < (795 * k.num - 380 * k.den) + (979 * k.den - 196 * k.num)) :
    ∀ e, Scat k ⟨795 * k.num - 380 * k.den, 979 * k.den - 196 * k.num, hpos⟩ (A_s1c1_lit e) (dW_s1c1_lit e) := by
  intro e
  have hN := k.num_le
  have hD := k.den_pos
  unfold P_s1c1_lit at hP
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 277) (q0 := 579) (p1 := 324) (q1 := 677)
    (by omega) (by omega)
  have hs0 : 196 * k.num ≤ 979 * k.den := by omega
  have hs1 : 380 * k.den ≤ 795 * k.num := by omega
  cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s1c1_lit, dW_s1c1_lit] <;>
  (constructor <;> apply Int.ofNat_le.mp <;>
    push_cast [Int.ofNat_sub hs0, Int.ofNat_sub hs1, Int.ofNat_sub hN] <;> grind)

theorem unsafe_s1c1_lit (k : Kappa) (H_KAPPA : ¬ Below_s1c1_lit k) :
    ∃ c d, (∀ e, Scat k c (A_s1c1_lit e) (d e)) ∧ ¬ Safe F1 G1 false (dlOf d) := by
  by_cases hfix : 324 * k.den ≤ k.num * 677
  · refine ⟨Corner.slow, dW_s1c1_lit, ?_, not_safe1 (by decide) (by decide) (by decide)⟩
    intro e; have := k.num_le
    cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, Corner.slow, A_s1c1_lit, dW_s1c1_lit] <;> omega
  · have hP := pos_s1c1_lit k (by omega) H_KAPPA
    have hlo := lo_s1c1_lit k hP
    have hD := k.den_pos
    exact ⟨_, dW_s1c1_lit, wit_s1c1_lit k hlo (by omega) hP (by omega), not_safe1 (by decide) (by decide) (by decide)⟩

/-- **Exact threshold, seed 1, client 1, `lit`.** Every assignment within κ at every corner is
safe iff `Below_s1c1_lit κ` (i.e. κ < κ_ex ≈ 0.4784365954); otherwise a violating whole-ps assignment exists. -/
theorem exact_s1c1_lit (k : Kappa) :
    (∀ c d, (∀ e, Scat k c (A_s1c1_lit e) (d e)) → Safe F1 G1 false (dlOf d)) ↔ Below_s1c1_lit k := by
  constructor
  · intro hs; apply Classical.byContradiction; intro hb
    obtain ⟨c, d, h1, h2⟩ := unsafe_s1c1_lit k hb
    exact h2 (hs c d h1)
  · intro hb c d h; exact safe_s1c1_lit k hb c d h

/-- Bracket: κ_ex ∈ (4784365953/10000000000, 2392182977/5000000000]. -/
theorem bracket_s1c1_lit : Below_s1c1_lit ⟨4784365953, 10000000000, by decide, by decide⟩ ∧
    ¬ Below_s1c1_lit ⟨2392182977, 5000000000, by decide, by decide⟩ := by decide
theorem nonvac_s1c1_lit : Below_s1c1_lit Kappa.zero := by decide

/-! ### Seed 1, client 2, `lit` -/

/-- Arc endpoints (F, S) ps, seed 1, client 2, `lit` (= `OnNetlistArbKappa.A_s1c2_lit`). -/
def A_s1c2_lit : Tab
  | .c => ⟨160, 488, by decide⟩
  | .wSt => ⟨262, 903, by decide⟩
  | .aSt => ⟨45, 124, by decide⟩
  | .wQf => ⟨76, 288, by decide⟩
  | .wQG => ⟨122, 429, by decide⟩
  | .aG => ⟨45, 124, by decide⟩
  | .wGC => ⟨176, 651, by decide⟩
  | .wAC => ⟨259, 955, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨195, 677, by decide⟩

theorem A_s1c2_lit_pos : ∀ e, 0 < (A_s1c2_lit e).F := by intro e; cases e <;> decide

/-- Box chain over `[0, 1]` (101 boxes) at `u = 71/177`. -/
def pts_s1c2_lit : List Pt := [(16156191519, 1023677665), (15662915241, 1516953943), (3792409741, 502557555), (7355798353, 1234136239), (14253554449, 2926314735), (13795512191, 3384356993), (417346467, 119524445), (3237473929, 1057493367), (1568088061, 579395587), (6078565135, 2511369457), (5893586531, 2696348061), (357338527, 179532385), (5541246333, 3048688259), (2682538117, 1612429179), (5188906135, 3401028457), (2515176523, 1779790773), (9743599913, 7436269271), (9426493735, 7753375449), (9109387557, 8070481627), (8792281379, 8387587805), (4246396105, 4343538487), (2052730013, 2242237283), (7946664903, 9233204281), (7682409755, 9497459429), (3709077303, 4880857289), (7171516467, 10008352717), (6924878329, 10254990855), (3339120095, 5250814497), (6466836071, 10713033113), (390964497, 682777327), (753301353, 1394182295), (5815006705, 11364862479), (1405304899, 2889662397), (5445049497, 11734819687), (1312815597, 2982151699), (5092709299, 12087159885), (76820925, 191614531), (2378993055, 6210941537), (4581816011, 12598053173), (1110219983, 3184747313), (4264709833, 12915159351), (513269593, 1634214055), (3982837675, 13197031509), (3841901595, 13337967589), (1859291263, 6730643329), (3560029437, 13619839747), (107397199, 429473713), (832752077, 3462215219), (3190072229, 13989796955), (383344145, 1764139503), (1471717045, 7118217547), (2802498011, 14377371173), (168549747, 905192077), (647773473, 3647193823), (2485391833, 14694477351), (2379689773, 14800179411), (572901181, 3722066115), (555284171, 3739683125), (2097817615, 15082051569), (2009732565, 15170136619), (969632263, 7620302329), (934398243, 7655536349), (1780711437, 15399157747), (1710243397, 15469625787), (1639775357, 15540093827), (784653659, 7805280933), (47389259, 489481653), (180748531, 1966735117), (1375520209, 15804348975), (1287435159, 15892434025), (76060445, 997681379), (295433275, 3999534021), (546824025, 8043110567), (1023180011, 16156689173), (987945991, 16191923193), (935094961, 16244774223), (899860941, 16280008243), (432313461, 8157621131), (414696451, 8175238141), (48533867, 1025207957), (88259229, 2059224419), (635605793, 16544263391), (582754763, 16597114421), (547520743, 16632348441), (128071681, 4166895615), (14907897, 521963015), (229717847, 8360216745), (110454671, 4184512625), (194483827, 8395450765), (21007289, 1052734535), (283265595, 16896603589), (248031575, 16931837609), (212797555, 16967071629), (177563535, 17002305649), (159946525, 17019922659), (13386937, 2134096711), (44739243, 8545195349), (27122233, 8562812359), (9505223, 8580429369), (0, 1)]
def sp_s1c2_lit : List (List Nat) := [[538, 74, 256, 74, 388, 1331]]

theorem chain_s1c2_lit : chainOK A_s1c2_lit 71 177 sp_s1c2_lit (1, 0) ((8333542403, 256392189) :: pts_s1c2_lit) = true := by
  decide +kernel
theorem last_s1c2_lit : lastPt (8333542403, 256392189) pts_s1c2_lit = (0, 1) := by decide +kernel

/-- `P(κ)·den²` for the binding vector `[538, 74, 256, 74, 388]`, late 1331, binding early arc `wSt`:
the vector is realisable at some corner iff `P ≥ 0`. Its root in `[0, 1]` is
κ_ex ≈ 0.4011244586 (irrational: discriminant 1539391407753 is not a square). -/
def P_s1c2_lit (k : Kappa) : Int :=
  16333 * (k.num : Int) * k.num + 1227619 * (k.num : Int) * k.den + -495056 * (k.den : Int) * k.den
/-- **κ < κ_ex** (`P < 0` below `u = 71/177`). -/
def Below_s1c2_lit (k : Kappa) : Prop := k.num * 177 < 71 * k.den ∧ P_s1c2_lit k < 0
instance (k : Kappa) : Decidable (Below_s1c2_lit k) := inferInstanceAs (Decidable (_ ∧ _))

theorem kill_s1c2_lit {k : Kappa} (hb : Below_s1c2_lit k) (c : Corner) (h1 : Scat k c (A_s1c2_lit .wSt) 538)
    (h2 : Scat k c (A_s1c2_lit .wAC) 1331) : False := by
  obtain ⟨hk, hP⟩ := hb
  unfold P_s1c2_lit at hP
  obtain ⟨w0, w1, hw⟩ := c
  simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s1c2_lit] at h1 h2
  have hN := k.num_le
  generalize k.num = N at *
  generalize k.den = D at *
  obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Nat.add_sub_cancel_left] at h1 h2
  have j1 := Int.ofNat_le.mpr h1.1
  have j2 := Int.ofNat_le.mpr h2.2
  push_cast at j1 j2
  simp only [Int.natCast_add] at hP
  have i1 : (w0 : Int) * ((L : Int) * 262 - (N + L) * 538) + (w1 : Int) * ((L : Int) * 903 - (N + L) * 538) ≤ 0 := by
    grind
  have i2 : (w0 : Int) * (((N : Int) + L) * 1331 - (N + N + L) * 259) +
      (w1 : Int) * (((N : Int) + L) * 1331 - (N + N + L) * 955) ≤ 0 := by
    grind
  have := elim2 (by omega) (by omega) (by omega) (by omega) (by omega) i1 i2
  grind

theorem safe_s1c2_lit (k : Kappa) (H_BELOW : Below_s1c2_lit k) (c : Corner) (d : Arc → Nat)
    (H_SCAT : ∀ e, Scat k c (A_s1c2_lit e) (d e)) : Safe F2 G2 true (dlOf d) := by
  apply safe2_of_le
  rcases cover_sound (A_s1c2_lit_pos) (by decide) (by decide) chain_s1c2_lit last_s1c2_lit H_BELOW.1 c d H_SCAT with h | h
  · exact h
  · exfalso
    simp only [sp_s1c2_lit, vec, List.mem_singleton, List.cons.injEq, and_true] at h
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h
    have s1 := H_SCAT .wSt
    have s2 := H_SCAT .wAC
    rw [e1] at s1
    rw [e6] at s2
    exact kill_s1c2_lit H_BELOW c s1 s2

/-- The violating assignment (binding vector, other arcs at their slow endpoint). -/
def dW_s1c2_lit : Arc → Nat
  | .c => 488 | .wSt => 538 | .aSt => 74 | .wQf => 288 | .wQG => 256 | .aG => 74 | .wGC => 388 | .wAC => 1331 | .aC => 124 | .wCf => 677

/-- Between `u` and `κ_fix = 365/903`, `P ≥ 0` (Bernstein certificate). -/
theorem pos_s1c2_lit (k : Kappa) (hfix : k.num * 903 < 365 * k.den) (hb : ¬ Below_s1c2_lit k) : 0 ≤ P_s1c2_lit k := by
  unfold Below_s1c2_lit at hb
  by_cases hu : k.num * 177 < 71 * k.den
  · have := (not_and.mp hb) hu
    omega
  · unfold P_s1c2_lit
    obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 71) (q0 := 177) (p1 := 365) (q1 := 903)
      (by omega) (by omega)
    grind

/-- `P ≥ 0` forces `κ ≥ κ_lo = 1093/2725` (`P < 0` on `[0, κ_lo)`, Bernstein certificate). -/
theorem lo_s1c2_lit (k : Kappa) (hP : 0 ≤ P_s1c2_lit k) : 1093 * k.den ≤ 2725 * k.num := by
  apply Classical.byContradiction; intro h
  unfold P_s1c2_lit at hP
  have hv : (0 : Int) < 1093 * (k.den : Int) - 2725 * k.num := by omega
  have hv2 := Int.mul_pos hv hv
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 0) (q0 := 1) (p1 := 1093) (q1 := 2725)
    (by omega) (by omega)
  grind

/-- On `[κ_lo, κ_fix]` with `P ≥ 0`: the binding vector is realised at the corner where the
late arc is exactly at `(1+κ)·nominal` (`w0 = (den+num)·955 − den·1331`, `w1 = den·1331 − (den+num)·259`). -/
theorem wit_s1c2_lit (k : Kappa) (hlo : 1093 * k.den ≤ 2725 * k.num) (hfix : k.num * 903 ≤ 365 * k.den)
    (hP : 0 ≤ P_s1c2_lit k) (hpos : 0 < (955 * k.num - 376 * k.den) + (1072 * k.den - 259 * k.num)) :
    ∀ e, Scat k ⟨955 * k.num - 376 * k.den, 1072 * k.den - 259 * k.num, hpos⟩ (A_s1c2_lit e) (dW_s1c2_lit e) := by
  intro e
  have hN := k.num_le
  have hD := k.den_pos
  unfold P_s1c2_lit at hP
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 1093) (q0 := 2725) (p1 := 365) (q1 := 903)
    (by omega) (by omega)
  have hs0 : 259 * k.num ≤ 1072 * k.den := by omega
  have hs1 : 376 * k.den ≤ 955 * k.num := by omega
  cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s1c2_lit, dW_s1c2_lit] <;>
  (constructor <;> apply Int.ofNat_le.mp <;>
    push_cast [Int.ofNat_sub hs0, Int.ofNat_sub hs1, Int.ofNat_sub hN] <;> grind)

theorem unsafe_s1c2_lit (k : Kappa) (H_KAPPA : ¬ Below_s1c2_lit k) :
    ∃ c d, (∀ e, Scat k c (A_s1c2_lit e) (d e)) ∧ ¬ Safe F2 G2 true (dlOf d) := by
  by_cases hfix : 365 * k.den ≤ k.num * 903
  · refine ⟨Corner.slow, dW_s1c2_lit, ?_, not_safe2 (by decide) (by decide) (by decide)⟩
    intro e; have := k.num_le
    cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, Corner.slow, A_s1c2_lit, dW_s1c2_lit] <;> omega
  · have hP := pos_s1c2_lit k (by omega) H_KAPPA
    have hlo := lo_s1c2_lit k hP
    have hD := k.den_pos
    exact ⟨_, dW_s1c2_lit, wit_s1c2_lit k hlo (by omega) hP (by omega), not_safe2 (by decide) (by decide) (by decide)⟩

/-- **Exact threshold, seed 1, client 2, `lit`.** Every assignment within κ at every corner is
safe iff `Below_s1c2_lit κ` (i.e. κ < κ_ex ≈ 0.4011244586); otherwise a violating whole-ps assignment exists. -/
theorem exact_s1c2_lit (k : Kappa) :
    (∀ c d, (∀ e, Scat k c (A_s1c2_lit e) (d e)) → Safe F2 G2 true (dlOf d)) ↔ Below_s1c2_lit k := by
  constructor
  · intro hs; apply Classical.byContradiction; intro hb
    obtain ⟨c, d, h1, h2⟩ := unsafe_s1c2_lit k hb
    exact h2 (hs c d h1)
  · intro hb c d h; exact safe_s1c2_lit k hb c d h

/-- Bracket: κ_ex ∈ (802248917/2000000000, 2005622293/5000000000]. -/
theorem bracket_s1c2_lit : Below_s1c2_lit ⟨802248917, 2000000000, by decide, by decide⟩ ∧
    ¬ Below_s1c2_lit ⟨2005622293, 5000000000, by decide, by decide⟩ := by decide
theorem nonvac_s1c2_lit : Below_s1c2_lit Kappa.zero := by decide

/-! ### Seed 2, client 1, `lit` -/

/-- Arc endpoints (F, S) ps, seed 2, client 1, `lit` (= `OnNetlistArbKappa.A_s2c1_lit`). -/
def A_s2c1_lit : Tab
  | .c => ⟨172, 522, by decide⟩
  | .wSt => ⟨225, 849, by decide⟩
  | .aSt => ⟨45, 124, by decide⟩
  | .wQf => ⟨76, 288, by decide⟩
  | .wQG => ⟨202, 677, by decide⟩
  | .aG => ⟨43, 148, by decide⟩
  | .wGC => ⟨241, 801, by decide⟩
  | .wAC => ⟨192, 760, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨115, 423, by decide⟩

theorem A_s2c1_lit_pos : ∀ e, 0 < (A_s2c1_lit e).F := by intro e; cases e <;> decide

/-- Box chain over `[0, 1]` (68 boxes) at `u = 4443/8105`. -/
def pts_s2c1_lit : List Pt := [(15367856639, 1812012545), (14527780825, 2652088359), (13746314951, 3433554233), (3246096431, 1048870865), (12261529791, 4918339393), (11577747151, 5602122033), (2738143613, 1556823683), (323341825, 213529087), (4890187821, 3699746771), (9252886177, 7926983007), (8744933359, 8434935825), (2064129297, 2230837999), (243363677, 293507235), (7357831433, 9822037751), (54430457, 79787271), (6576365559, 10603503625), (6205169269, 10974699915), (2926754813, 5663179779), (1385230819, 2909736477), (5228336927, 11951532257), (616910903, 1530572745), (2321118761, 6268815831), (2184362233, 6405572359), (129196397, 407674515), (3880308295, 13299560889), (3665405179, 13514464005), (215656379, 858085445), (813783899, 3481183397), (3059769127, 14120100057), (1441969653, 7147964939), (677027371, 3617939925), (314092877, 1833390771), (296998311, 1850485337), (2219693313, 14960175871), (1031700069, 7558234523), (963321805, 7626612787), (1809423729, 15370445455), (211525481, 1935958167), (797260307, 7792674285), (374209345, 3920757951), (1399154145, 15780715039), (160241783, 1987241865), (592125515, 7997809077), (271641949, 4023325347), (1027957855, 16151911329), (237452817, 4057514479), (426064017, 8163870575), (386990723, 8202943869), (357685753, 8232248839), (169074553, 4125892743), (38605517, 1035136307), (559078331, 16620790853), (520005037, 16659864147), (461395097, 16718474087), (383248509, 16796620675), (324638569, 16855230615), (285565275, 16894303909), (123245991, 8466688601), (3240917, 265194539), (84172697, 8505761895), (148808747, 17031060437), (54867727, 8535066865), (90198807, 17089670377), (51125513, 17128743671), (15794433, 8574140159), (12052219, 17167816965), (0, 1)]
def sp_s2c1_lit : List (List Nat) := [[383, 56, 305, 67, 361, 1173]]

theorem chain_s2c1_lit : chainOK A_s2c1_lit 4443 8105 sp_s2c1_lit (1, 0) ((16247005747, 932863437) :: pts_s2c1_lit) = true := by
  decide +kernel
theorem last_s2c1_lit : lastPt (16247005747, 932863437) pts_s2c1_lit = (0, 1) := by decide +kernel

/-- `P(κ)·den²` for the binding vector `[383, 56, 305, 67, 361]`, late 1173, binding early arc `wQG`:
the vector is realisable at some corner iff `P ≥ 0`. Its root in `[0, 1]` is
κ_ex ≈ 0.5481793473 (irrational: discriminant 571867022049 is not a square). -/
def P_s2c1_lit (k : Kappa) : Int :=
  23536 * (k.num : Int) * k.num + 730415 * (k.num : Int) * k.den + -407471 * (k.den : Int) * k.den
/-- **κ < κ_ex** (`P < 0` below `u = 4443/8105`). -/
def Below_s2c1_lit (k : Kappa) : Prop := k.num * 8105 < 4443 * k.den ∧ P_s2c1_lit k < 0
instance (k : Kappa) : Decidable (Below_s2c1_lit k) := inferInstanceAs (Decidable (_ ∧ _))

theorem kill_s2c1_lit {k : Kappa} (hb : Below_s2c1_lit k) (c : Corner) (h1 : Scat k c (A_s2c1_lit .wQG) 305)
    (h2 : Scat k c (A_s2c1_lit .wAC) 1173) : False := by
  obtain ⟨hk, hP⟩ := hb
  unfold P_s2c1_lit at hP
  obtain ⟨w0, w1, hw⟩ := c
  simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s2c1_lit] at h1 h2
  have hN := k.num_le
  generalize k.num = N at *
  generalize k.den = D at *
  obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Nat.add_sub_cancel_left] at h1 h2
  have j1 := Int.ofNat_le.mpr h1.1
  have j2 := Int.ofNat_le.mpr h2.2
  push_cast at j1 j2
  simp only [Int.natCast_add] at hP
  have i1 : (w0 : Int) * ((L : Int) * 202 - (N + L) * 305) + (w1 : Int) * ((L : Int) * 677 - (N + L) * 305) ≤ 0 := by
    grind
  have i2 : (w0 : Int) * (((N : Int) + L) * 1173 - (N + N + L) * 192) +
      (w1 : Int) * (((N : Int) + L) * 1173 - (N + N + L) * 760) ≤ 0 := by
    grind
  have := elim2 (by omega) (by omega) (by omega) (by omega) (by omega) i1 i2
  grind

theorem safe_s2c1_lit (k : Kappa) (H_BELOW : Below_s2c1_lit k) (c : Corner) (d : Arc → Nat)
    (H_SCAT : ∀ e, Scat k c (A_s2c1_lit e) (d e)) : Safe F1 G1 false (dlOf d) := by
  apply safe1_of_le
  rcases cover_sound (A_s2c1_lit_pos) (by decide) (by decide) chain_s2c1_lit last_s2c1_lit H_BELOW.1 c d H_SCAT with h | h
  · exact h
  · exfalso
    simp only [sp_s2c1_lit, vec, List.mem_singleton, List.cons.injEq, and_true] at h
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h
    have s1 := H_SCAT .wQG
    have s2 := H_SCAT .wAC
    rw [e3] at s1
    rw [e6] at s2
    exact kill_s2c1_lit H_BELOW c s1 s2

/-- The violating assignment (binding vector, other arcs at their slow endpoint). -/
def dW_s2c1_lit : Arc → Nat
  | .c => 522 | .wSt => 383 | .aSt => 56 | .wQf => 288 | .wQG => 305 | .aG => 67 | .wGC => 361 | .wAC => 1173 | .aC => 124 | .wCf => 423

/-- Between `u` and `κ_fix = 372/677`, `P ≥ 0` (Bernstein certificate). -/
theorem pos_s2c1_lit (k : Kappa) (hfix : k.num * 677 < 372 * k.den) (hb : ¬ Below_s2c1_lit k) : 0 ≤ P_s2c1_lit k := by
  unfold Below_s2c1_lit at hb
  by_cases hu : k.num * 8105 < 4443 * k.den
  · have := (not_and.mp hb) hu
    omega
  · unfold P_s2c1_lit
    obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 4443) (q0 := 8105) (p1 := 372) (q1 := 677)
      (by omega) (by omega)
    grind

/-- `P ≥ 0` forces `κ ≥ κ_lo = 1987/3625` (`P < 0` on `[0, κ_lo)`, Bernstein certificate). -/
theorem lo_s2c1_lit (k : Kappa) (hP : 0 ≤ P_s2c1_lit k) : 1987 * k.den ≤ 3625 * k.num := by
  apply Classical.byContradiction; intro h
  unfold P_s2c1_lit at hP
  have hv : (0 : Int) < 1987 * (k.den : Int) - 3625 * k.num := by omega
  have hv2 := Int.mul_pos hv hv
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 0) (q0 := 1) (p1 := 1987) (q1 := 3625)
    (by omega) (by omega)
  grind

/-- On `[κ_lo, κ_fix]` with `P ≥ 0`: the binding vector is realised at the corner where the
late arc is exactly at `(1+κ)·nominal` (`w0 = (den+num)·760 − den·1173`, `w1 = den·1173 − (den+num)·192`). -/
theorem wit_s2c1_lit (k : Kappa) (hlo : 1987 * k.den ≤ 3625 * k.num) (hfix : k.num * 677 ≤ 372 * k.den)
    (hP : 0 ≤ P_s2c1_lit k) (hpos : 0 < (760 * k.num - 413 * k.den) + (981 * k.den - 192 * k.num)) :
    ∀ e, Scat k ⟨760 * k.num - 413 * k.den, 981 * k.den - 192 * k.num, hpos⟩ (A_s2c1_lit e) (dW_s2c1_lit e) := by
  intro e
  have hN := k.num_le
  have hD := k.den_pos
  unfold P_s2c1_lit at hP
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 1987) (q0 := 3625) (p1 := 372) (q1 := 677)
    (by omega) (by omega)
  have hs0 : 192 * k.num ≤ 981 * k.den := by omega
  have hs1 : 413 * k.den ≤ 760 * k.num := by omega
  cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s2c1_lit, dW_s2c1_lit] <;>
  (constructor <;> apply Int.ofNat_le.mp <;>
    push_cast [Int.ofNat_sub hs0, Int.ofNat_sub hs1, Int.ofNat_sub hN] <;> grind)

theorem unsafe_s2c1_lit (k : Kappa) (H_KAPPA : ¬ Below_s2c1_lit k) :
    ∃ c d, (∀ e, Scat k c (A_s2c1_lit e) (d e)) ∧ ¬ Safe F1 G1 false (dlOf d) := by
  by_cases hfix : 372 * k.den ≤ k.num * 677
  · refine ⟨Corner.slow, dW_s2c1_lit, ?_, not_safe1 (by decide) (by decide) (by decide)⟩
    intro e; have := k.num_le
    cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, Corner.slow, A_s2c1_lit, dW_s2c1_lit] <;> omega
  · have hP := pos_s2c1_lit k (by omega) H_KAPPA
    have hlo := lo_s2c1_lit k hP
    have hD := k.den_pos
    exact ⟨_, dW_s2c1_lit, wit_s2c1_lit k hlo (by omega) hP (by omega), not_safe1 (by decide) (by decide) (by decide)⟩

/-- **Exact threshold, seed 2, client 1, `lit`.** Every assignment within κ at every corner is
safe iff `Below_s2c1_lit κ` (i.e. κ < κ_ex ≈ 0.5481793473); otherwise a violating whole-ps assignment exists. -/
theorem exact_s2c1_lit (k : Kappa) :
    (∀ c d, (∀ e, Scat k c (A_s2c1_lit e) (d e)) → Safe F1 G1 false (dlOf d)) ↔ Below_s2c1_lit k := by
  constructor
  · intro hs; apply Classical.byContradiction; intro hb
    obtain ⟨c, d, h1, h2⟩ := unsafe_s2c1_lit k hb
    exact h2 (hs c d h1)
  · intro hb c d h; exact safe_s2c1_lit k hb c d h

/-- Bracket: κ_ex ∈ (85653023/156250000, 5481793473/10000000000]. -/
theorem bracket_s2c1_lit : Below_s2c1_lit ⟨85653023, 156250000, by decide, by decide⟩ ∧
    ¬ Below_s2c1_lit ⟨5481793473, 10000000000, by decide, by decide⟩ := by decide
theorem nonvac_s2c1_lit : Below_s2c1_lit Kappa.zero := by decide

/-! ### Seed 2, client 2, `lit` -/

/-- Arc endpoints (F, S) ps, seed 2, client 2, `lit` (= `OnNetlistArbKappa.A_s2c2_lit`). -/
def A_s2c2_lit : Tab
  | .c => ⟨172, 522, by decide⟩
  | .wSt => ⟨225, 849, by decide⟩
  | .aSt => ⟨45, 124, by decide⟩
  | .wQf => ⟨76, 288, by decide⟩
  | .wQG => ⟨202, 677, by decide⟩
  | .aG => ⟨45, 124, by decide⟩
  | .wGC => ⟨325, 1015, by decide⟩
  | .wAC => ⟨262, 940, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨76, 288, by decide⟩

theorem A_s2c2_lit_pos : ∀ e, 0 < (A_s2c2_lit e).F := by intro e; cases e <;> decide

/-- Box chain over `[0, 1]` (91 boxes) at `u = 205/413`. -/
def pts_s2c2_lit : List Pt := [(15995330563, 1184538621), (15436518625, 1743350559), (7447320191, 1142614401), (7193314765, 1396619827), (13861684983, 3318184201), (13370607825, 3809261359), (6456699029, 2133235563), (12456188291, 4723680893), (12015912219, 5163956965), (5796284921, 2793649671), (1398270145, 749213503), (10796686173, 6383183011), (5203605593, 3386328999), (1252217025, 895266623), (2411298727, 1883668569), (579540851, 494200973), (8967847105, 8212022079), (4323053449, 4266881143), (2081091673, 2213875623), (8002626485, 9177242699), (7714753669, 9465115515), (7426880853, 9752988331), (7155941731, 10023927453), (6901936305, 10277932879), (6647930879, 10531938305), (6393925453, 10785943731), (6173787417, 11006081767), (2968357843, 5621576749), (5716577649, 11463291535), (2739752959, 5850181633), (5276301577, 11903567607), (5056163541, 12123705643), (152184153, 384686759), (4666688555, 12513180629), (1124337901, 3170629395), (4294147263, 12885721921), (4107876617, 13071992567), (3955473361, 13224395823), (1893068205, 6696866387), (3633733155, 13546136029), (866099051, 3428868245), (827998237, 3466969059), (3193457083, 13986412101), (3041053827, 14138815357), (2922517961, 14257351223), (2787048401, 14392820783), (1342723115, 7247211477), (2566910365, 14612958819), (2448374499, 14731494685), (295463253, 1852020395), (2262103853, 14917765331), (535891997, 3759075299), (2041965817, 15137903367), (978648671, 7611285921), (944781281, 7645153311), (1787960391, 15391908793), (1686358221, 15493510963), (1601689745, 15578179439), (1533954965, 15645914219), (1466220185, 15713648999), (1381551709, 15798317475), (648441617, 7941492975), (1246082149, 15933787035), (1195281063, 15984588121), (1127546283, 16052322901), (538372599, 8051561993), (65179863, 1008561961), (239552333, 4055414963), (111309319, 2036174329), (205684943, 4089282353), (385969343, 8203965249), (721137601, 16458731583), (687270211, 16492598973), (318234563, 8271700029), (75325217, 2072158431), (275900325, 8314034267), (242032935, 8347901657), (433264785, 16746604399), (399397395, 16780471789), (348596309, 16831272875), (37224403, 2110259245), (131963917, 8457970675), (246994139, 16932875045), (98096527, 8491838065), (179259359, 17000609825), (128458273, 17051410911), (19414297, 4275552999), (21894899, 8568039693), (1240301, 2146243347), (0, 1)]
def sp_s2c2_lit : List (List Nat) := [[424, 62, 338, 62, 507, 1394]]

theorem chain_s2c2_lit : chainOK A_s2c2_lit 205 413 sp_s2c2_lit (1, 0) ((8294004945, 295929647) :: pts_s2c2_lit) = true := by
  decide +kernel
theorem last_s2c2_lit : lastPt (8294004945, 295929647) pts_s2c2_lit = (0, 1) := by decide +kernel

/-- `P(κ)·den²` for the binding vector `[424, 62, 338, 62, 507]`, late 1394, binding early arc `wQG`:
the vector is realisable at some corner iff `P ≥ 0`. Its root in `[0, 1]` is
κ_ex ≈ 0.4963580515 (irrational: discriminant 816725938404 is not a square). -/
def P_s2c2_lit (k : Kappa) : Int :=
  12506 * (k.num : Int) * k.num + 891314 * (k.num : Int) * k.den + -445492 * (k.den : Int) * k.den
/-- **κ < κ_ex** (`P < 0` below `u = 205/413`). -/
def Below_s2c2_lit (k : Kappa) : Prop := k.num * 413 < 205 * k.den ∧ P_s2c2_lit k < 0
instance (k : Kappa) : Decidable (Below_s2c2_lit k) := inferInstanceAs (Decidable (_ ∧ _))

theorem kill_s2c2_lit {k : Kappa} (hb : Below_s2c2_lit k) (c : Corner) (h1 : Scat k c (A_s2c2_lit .wQG) 338)
    (h2 : Scat k c (A_s2c2_lit .wAC) 1394) : False := by
  obtain ⟨hk, hP⟩ := hb
  unfold P_s2c2_lit at hP
  obtain ⟨w0, w1, hw⟩ := c
  simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s2c2_lit] at h1 h2
  have hN := k.num_le
  generalize k.num = N at *
  generalize k.den = D at *
  obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Nat.add_sub_cancel_left] at h1 h2
  have j1 := Int.ofNat_le.mpr h1.1
  have j2 := Int.ofNat_le.mpr h2.2
  push_cast at j1 j2
  simp only [Int.natCast_add] at hP
  have i1 : (w0 : Int) * ((L : Int) * 202 - (N + L) * 338) + (w1 : Int) * ((L : Int) * 677 - (N + L) * 338) ≤ 0 := by
    grind
  have i2 : (w0 : Int) * (((N : Int) + L) * 1394 - (N + N + L) * 262) +
      (w1 : Int) * (((N : Int) + L) * 1394 - (N + N + L) * 940) ≤ 0 := by
    grind
  have := elim2 (by omega) (by omega) (by omega) (by omega) (by omega) i1 i2
  grind

theorem safe_s2c2_lit (k : Kappa) (H_BELOW : Below_s2c2_lit k) (c : Corner) (d : Arc → Nat)
    (H_SCAT : ∀ e, Scat k c (A_s2c2_lit e) (d e)) : Safe F2 G2 true (dlOf d) := by
  apply safe2_of_le
  rcases cover_sound (A_s2c2_lit_pos) (by decide) (by decide) chain_s2c2_lit last_s2c2_lit H_BELOW.1 c d H_SCAT with h | h
  · exact h
  · exfalso
    simp only [sp_s2c2_lit, vec, List.mem_singleton, List.cons.injEq, and_true] at h
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h
    have s1 := H_SCAT .wQG
    have s2 := H_SCAT .wAC
    rw [e3] at s1
    rw [e6] at s2
    exact kill_s2c2_lit H_BELOW c s1 s2

/-- The violating assignment (binding vector, other arcs at their slow endpoint). -/
def dW_s2c2_lit : Arc → Nat
  | .c => 522 | .wSt => 424 | .aSt => 62 | .wQf => 288 | .wQG => 338 | .aG => 62 | .wGC => 507 | .wAC => 1394 | .aC => 124 | .wCf => 288

/-- Between `u` and `κ_fix = 339/677`, `P ≥ 0` (Bernstein certificate). -/
theorem pos_s2c2_lit (k : Kappa) (hfix : k.num * 677 < 339 * k.den) (hb : ¬ Below_s2c2_lit k) : 0 ≤ P_s2c2_lit k := by
  unfold Below_s2c2_lit at hb
  by_cases hu : k.num * 413 < 205 * k.den
  · have := (not_and.mp hb) hu
    omega
  · unfold P_s2c2_lit
    obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 205) (q0 := 413) (p1 := 339) (q1 := 677)
      (by omega) (by omega)
    grind

/-- `P ≥ 0` forces `κ ≥ κ_lo = 203/409` (`P < 0` on `[0, κ_lo)`, Bernstein certificate). -/
theorem lo_s2c2_lit (k : Kappa) (hP : 0 ≤ P_s2c2_lit k) : 203 * k.den ≤ 409 * k.num := by
  apply Classical.byContradiction; intro h
  unfold P_s2c2_lit at hP
  have hv : (0 : Int) < 203 * (k.den : Int) - 409 * k.num := by omega
  have hv2 := Int.mul_pos hv hv
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 0) (q0 := 1) (p1 := 203) (q1 := 409)
    (by omega) (by omega)
  grind

/-- On `[κ_lo, κ_fix]` with `P ≥ 0`: the binding vector is realised at the corner where the
late arc is exactly at `(1+κ)·nominal` (`w0 = (den+num)·940 − den·1394`, `w1 = den·1394 − (den+num)·262`). -/
theorem wit_s2c2_lit (k : Kappa) (hlo : 203 * k.den ≤ 409 * k.num) (hfix : k.num * 677 ≤ 339 * k.den)
    (hP : 0 ≤ P_s2c2_lit k) (hpos : 0 < (940 * k.num - 454 * k.den) + (1132 * k.den - 262 * k.num)) :
    ∀ e, Scat k ⟨940 * k.num - 454 * k.den, 1132 * k.den - 262 * k.num, hpos⟩ (A_s2c2_lit e) (dW_s2c2_lit e) := by
  intro e
  have hN := k.num_le
  have hD := k.den_pos
  unfold P_s2c2_lit at hP
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 203) (q0 := 409) (p1 := 339) (q1 := 677)
    (by omega) (by omega)
  have hs0 : 262 * k.num ≤ 1132 * k.den := by omega
  have hs1 : 454 * k.den ≤ 940 * k.num := by omega
  cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s2c2_lit, dW_s2c2_lit] <;>
  (constructor <;> apply Int.ofNat_le.mp <;>
    push_cast [Int.ofNat_sub hs0, Int.ofNat_sub hs1, Int.ofNat_sub hN] <;> grind)

theorem unsafe_s2c2_lit (k : Kappa) (H_KAPPA : ¬ Below_s2c2_lit k) :
    ∃ c d, (∀ e, Scat k c (A_s2c2_lit e) (d e)) ∧ ¬ Safe F2 G2 true (dlOf d) := by
  by_cases hfix : 339 * k.den ≤ k.num * 677
  · refine ⟨Corner.slow, dW_s2c2_lit, ?_, not_safe2 (by decide) (by decide) (by decide)⟩
    intro e; have := k.num_le
    cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, Corner.slow, A_s2c2_lit, dW_s2c2_lit] <;> omega
  · have hP := pos_s2c2_lit k (by omega) H_KAPPA
    have hlo := lo_s2c2_lit k hP
    have hD := k.den_pos
    exact ⟨_, dW_s2c2_lit, wit_s2c2_lit k hlo (by omega) hP (by omega), not_safe2 (by decide) (by decide) (by decide)⟩

/-- **Exact threshold, seed 2, client 2, `lit`.** Every assignment within κ at every corner is
safe iff `Below_s2c2_lit κ` (i.e. κ < κ_ex ≈ 0.4963580515); otherwise a violating whole-ps assignment exists. -/
theorem exact_s2c2_lit (k : Kappa) :
    (∀ c d, (∀ e, Scat k c (A_s2c2_lit e) (d e)) → Safe F2 G2 true (dlOf d)) ↔ Below_s2c2_lit k := by
  constructor
  · intro hs; apply Classical.byContradiction; intro hb
    obtain ⟨c, d, h1, h2⟩ := unsafe_s2c2_lit k hb
    exact h2 (hs c d h1)
  · intro hb c d h; exact safe_s2c2_lit k hb c d h

/-- Bracket: κ_ex ∈ (992716103/2000000000, 1240895129/2500000000]. -/
theorem bracket_s2c2_lit : Below_s2c2_lit ⟨992716103, 2000000000, by decide, by decide⟩ ∧
    ¬ Below_s2c2_lit ⟨1240895129, 2500000000, by decide, by decide⟩ := by decide
theorem nonvac_s2c2_lit : Below_s2c2_lit Kappa.zero := by decide

/-! ### Seed 3, client 1, `lit` -/

/-- Arc endpoints (F, S) ps, seed 3, client 1, `lit` (= `OnNetlistArbKappa.A_s3c1_lit`). -/
def A_s3c1_lit : Tab
  | .c => ⟨216, 652, by decide⟩
  | .wSt => ⟨178, 761, by decide⟩
  | .aSt => ⟨45, 124, by decide⟩
  | .wQf => ⟨286, 973, by decide⟩
  | .wQG => ⟨218, 714, by decide⟩
  | .aG => ⟨48, 116, by decide⟩
  | .wGC => ⟨274, 972, by decide⟩
  | .wAC => ⟨183, 809, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨69, 298, by decide⟩

theorem A_s3c1_lit_pos : ∀ e, 0 < (A_s3c1_lit e).F := by intro e; cases e <;> decide

/-- Box chain over `[0, 1]` (58 boxes) at `u = 49760/92493`. -/
def pts_s3c1_lit : List Pt := [(14618386449, 2561482735), (6747106271, 1842828321), (12459258787, 4720610397), (89810009, 44407719), (10603479639, 6576389545), (1220601277, 926882371), (9015360945, 8164508239), (4150799867, 4439134725), (3820685307, 4769249285), (440782351, 632959473), (6499352677, 10680516507), (5981875799, 11197993385), (5517931013, 11661938171), (316989391, 756752433), (582677195, 1564806453), (1071673231, 3223294065), (3947656349, 13232212835), (1822153917, 6767780675), (1679401675, 6910532917), (1536649433, 7053285159), (355165809, 1792317839), (2609354079, 14570515105), (598806429, 3696160867), (272637169, 1874846479), (1001328525, 7588606067), (1824216747, 15355652437), (1681464505, 15498404679), (1538712263, 15641156921), (1395960021, 15783909163), (1271051809, 15908817375), (1163987627, 16015881557), (1056923445, 16122945739), (14841551, 253593905), (107579889, 2039903759), (771418961, 16408450223), (87505355, 2059978293), (646510749, 16533358435), (296489329, 8293445263), (67430821, 2080052827), (485914477, 16693954707), (28139151, 1045602673), (103634589, 4191332707), (361006265, 16818862919), (81329551, 4213637745), (153737087, 8436197505), (135893057, 8454041535), (236098053, 16943771131), (218254023, 16961615161), (200409993, 16979459191), (41180483, 4253786813), (73438951, 8516495641), (129033871, 17050835313), (93345811, 17086523373), (28828875, 8561105717), (4976715, 2142506933), (10984845, 8578949747), (0, 1)]
def sp_s3c1_lit : List (List Nat) := [[352, 58, 330, 54, 449, 1244]]

theorem chain_s3c1_lit : chainOK A_s3c1_lit 49760 92493 sp_s3c1_lit (1, 0) ((7924812269, 665122323) :: pts_s3c1_lit) = true := by
  decide +kernel
theorem last_s3c1_lit : lastPt (7924812269, 665122323) pts_s3c1_lit = (0, 1) := by decide +kernel

/-- `P(κ)·den²` for the binding vector `[352, 58, 330, 54, 449]`, late 1244, binding early arc `wGC`:
the vector is realisable at some corner iff `P ≥ 0`. Its root in `[0, 1]` is
κ_ex ≈ 0.5379862760 (irrational: discriminant 1431619041476 is not a square). -/
def P_s3c1_lit (k : Kappa) : Int :=
  43790 * (k.num : Int) * k.num + 1149386 * (k.num : Int) * k.den + -631028 * (k.den : Int) * k.den
/-- **κ < κ_ex** (`P < 0` below `u = 49760/92493`). -/
def Below_s3c1_lit (k : Kappa) : Prop := k.num * 92493 < 49760 * k.den ∧ P_s3c1_lit k < 0
instance (k : Kappa) : Decidable (Below_s3c1_lit k) := inferInstanceAs (Decidable (_ ∧ _))

theorem kill_s3c1_lit {k : Kappa} (hb : Below_s3c1_lit k) (c : Corner) (h1 : Scat k c (A_s3c1_lit .wGC) 449)
    (h2 : Scat k c (A_s3c1_lit .wAC) 1244) : False := by
  obtain ⟨hk, hP⟩ := hb
  unfold P_s3c1_lit at hP
  obtain ⟨w0, w1, hw⟩ := c
  simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s3c1_lit] at h1 h2
  have hN := k.num_le
  generalize k.num = N at *
  generalize k.den = D at *
  obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Nat.add_sub_cancel_left] at h1 h2
  have j1 := Int.ofNat_le.mpr h1.1
  have j2 := Int.ofNat_le.mpr h2.2
  push_cast at j1 j2
  simp only [Int.natCast_add] at hP
  have i1 : (w0 : Int) * ((L : Int) * 274 - (N + L) * 449) + (w1 : Int) * ((L : Int) * 972 - (N + L) * 449) ≤ 0 := by
    grind
  have i2 : (w0 : Int) * (((N : Int) + L) * 1244 - (N + N + L) * 183) +
      (w1 : Int) * (((N : Int) + L) * 1244 - (N + N + L) * 809) ≤ 0 := by
    grind
  have := elim2 (by omega) (by omega) (by omega) (by omega) (by omega) i1 i2
  grind

theorem safe_s3c1_lit (k : Kappa) (H_BELOW : Below_s3c1_lit k) (c : Corner) (d : Arc → Nat)
    (H_SCAT : ∀ e, Scat k c (A_s3c1_lit e) (d e)) : Safe F1 G1 false (dlOf d) := by
  apply safe1_of_le
  rcases cover_sound (A_s3c1_lit_pos) (by decide) (by decide) chain_s3c1_lit last_s3c1_lit H_BELOW.1 c d H_SCAT with h | h
  · exact h
  · exfalso
    simp only [sp_s3c1_lit, vec, List.mem_singleton, List.cons.injEq, and_true] at h
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h
    have s1 := H_SCAT .wGC
    have s2 := H_SCAT .wAC
    rw [e5] at s1
    rw [e6] at s2
    exact kill_s3c1_lit H_BELOW c s1 s2

/-- The violating assignment (binding vector, other arcs at their slow endpoint). -/
def dW_s3c1_lit : Arc → Nat
  | .c => 652 | .wSt => 352 | .aSt => 58 | .wQf => 973 | .wQG => 330 | .aG => 54 | .wGC => 449 | .wAC => 1244 | .aC => 124 | .wCf => 298

/-- Between `u` and `κ_fix = 523/972`, `P ≥ 0` (Bernstein certificate). -/
theorem pos_s3c1_lit (k : Kappa) (hfix : k.num * 972 < 523 * k.den) (hb : ¬ Below_s3c1_lit k) : 0 ≤ P_s3c1_lit k := by
  unfold Below_s3c1_lit at hb
  by_cases hu : k.num * 92493 < 49760 * k.den
  · have := (not_and.mp hb) hu
    omega
  · unfold P_s3c1_lit
    obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 49760) (q0 := 92493) (p1 := 523) (q1 := 972)
      (by omega) (by omega)
    grind

/-- `P ≥ 0` forces `κ ≥ κ_lo = 404/751` (`P < 0` on `[0, κ_lo)`, Bernstein certificate). -/
theorem lo_s3c1_lit (k : Kappa) (hP : 0 ≤ P_s3c1_lit k) : 404 * k.den ≤ 751 * k.num := by
  apply Classical.byContradiction; intro h
  unfold P_s3c1_lit at hP
  have hv : (0 : Int) < 404 * (k.den : Int) - 751 * k.num := by omega
  have hv2 := Int.mul_pos hv hv
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 0) (q0 := 1) (p1 := 404) (q1 := 751)
    (by omega) (by omega)
  grind

/-- On `[κ_lo, κ_fix]` with `P ≥ 0`: the binding vector is realised at the corner where the
late arc is exactly at `(1+κ)·nominal` (`w0 = (den+num)·809 − den·1244`, `w1 = den·1244 − (den+num)·183`). -/
theorem wit_s3c1_lit (k : Kappa) (hlo : 404 * k.den ≤ 751 * k.num) (hfix : k.num * 972 ≤ 523 * k.den)
    (hP : 0 ≤ P_s3c1_lit k) (hpos : 0 < (809 * k.num - 435 * k.den) + (1061 * k.den - 183 * k.num)) :
    ∀ e, Scat k ⟨809 * k.num - 435 * k.den, 1061 * k.den - 183 * k.num, hpos⟩ (A_s3c1_lit e) (dW_s3c1_lit e) := by
  intro e
  have hN := k.num_le
  have hD := k.den_pos
  unfold P_s3c1_lit at hP
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 404) (q0 := 751) (p1 := 523) (q1 := 972)
    (by omega) (by omega)
  have hs0 : 183 * k.num ≤ 1061 * k.den := by omega
  have hs1 : 435 * k.den ≤ 809 * k.num := by omega
  cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s3c1_lit, dW_s3c1_lit] <;>
  (constructor <;> apply Int.ofNat_le.mp <;>
    push_cast [Int.ofNat_sub hs0, Int.ofNat_sub hs1, Int.ofNat_sub hN] <;> grind)

theorem unsafe_s3c1_lit (k : Kappa) (H_KAPPA : ¬ Below_s3c1_lit k) :
    ∃ c d, (∀ e, Scat k c (A_s3c1_lit e) (d e)) ∧ ¬ Safe F1 G1 false (dlOf d) := by
  by_cases hfix : 523 * k.den ≤ k.num * 972
  · refine ⟨Corner.slow, dW_s3c1_lit, ?_, not_safe1 (by decide) (by decide) (by decide)⟩
    intro e; have := k.num_le
    cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, Corner.slow, A_s3c1_lit, dW_s3c1_lit] <;> omega
  · have hP := pos_s3c1_lit k (by omega) H_KAPPA
    have hlo := lo_s3c1_lit k hP
    have hD := k.den_pos
    exact ⟨_, dW_s3c1_lit, wit_s3c1_lit k hlo (by omega) hP (by omega), not_safe1 (by decide) (by decide) (by decide)⟩

/-- **Exact threshold, seed 3, client 1, `lit`.** Every assignment within κ at every corner is
safe iff `Below_s3c1_lit κ` (i.e. κ < κ_ex ≈ 0.5379862760); otherwise a violating whole-ps assignment exists. -/
theorem exact_s3c1_lit (k : Kappa) :
    (∀ c d, (∀ e, Scat k c (A_s3c1_lit e) (d e)) → Safe F1 G1 false (dlOf d)) ↔ Below_s3c1_lit k := by
  constructor
  · intro hs; apply Classical.byContradiction; intro hb
    obtain ⟨c, d, h1, h2⟩ := unsafe_s3c1_lit k hb
    exact h2 (hs c d h1)
  · intro hb c d h; exact safe_s3c1_lit k hb c d h

/-- Bracket: κ_ex ∈ (134496569/250000000, 5379862761/10000000000]. -/
theorem bracket_s3c1_lit : Below_s3c1_lit ⟨134496569, 250000000, by decide, by decide⟩ ∧
    ¬ Below_s3c1_lit ⟨5379862761, 10000000000, by decide, by decide⟩ := by decide
theorem nonvac_s3c1_lit : Below_s3c1_lit Kappa.zero := by decide

/-! ### Seed 3, client 2, `lit` -/

/-- Arc endpoints (F, S) ps, seed 3, client 2, `lit` (= `OnNetlistArbKappa.A_s3c2_lit`). -/
def A_s3c2_lit : Tab
  | .c => ⟨216, 652, by decide⟩
  | .wSt => ⟨178, 761, by decide⟩
  | .aSt => ⟨45, 124, by decide⟩
  | .wQf => ⟨286, 973, by decide⟩
  | .wQG => ⟨218, 714, by decide⟩
  | .aG => ⟨45, 124, by decide⟩
  | .wGC => ⟨268, 879, by decide⟩
  | .wAC => ⟨258, 965, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨211, 685, by decide⟩

theorem A_s3c2_lit_pos : ∀ e, 0 < (A_s3c2_lit e).F := by intro e; cases e <;> decide

/-- Box chain over `[0, 1]` (93 boxes) at `u = 249/542`. -/
def pts_s3c2_lit : List Pt := [(1004567627, 69174197), (15506970295, 1672898889), (7495404797, 1094529795), (7245649619, 1344284973), (6995894441, 1594040151), (13508928871, 3670940313), (6521359603, 2068574989), (12593159885, 4586709299), (6080125455, 2509809137), (1467999035, 679484613), (11361034341, 5818834843), (5497363373, 3092571219), (664276197, 409465627), (10262111557, 6917757627), (2478113577, 1816853719), (9562797059, 7617072125), (9229790155, 7950079029), (8896783251, 8283085933), (2145106673, 2149860623), (8280720479, 8899148705), (3998832305, 4591102287), (7697958397, 9481910787), (3715776437, 4874158155), (7165147351, 10014721833), (6898741827, 10281127357), (6665636995, 10514232189), (6415881817, 10763987367), (772847123, 1374636525), (93223789, 175211667), (5749868009, 11430001175), (2775031933, 5814902659), (5333609379, 11846259805), (2575227791, 6014706801), (4950651439, 12229217745), (4784147987, 12395721197), (4584343845, 12595525339), (137537189, 399333723), (2109018125, 6480916467), (4034882453, 13144986731), (240733041, 833008783), (3701875549, 13477993635), (3552022443, 13627846741), (425271167, 1722212481), (3285616919, 13894252265), (1576207079, 7013727513), (754802849, 3540164447), (2886008635, 14293860549), (2786106563, 14393762621), (1326451901, 7263482691), (2536351385, 14643517799), (1218224657, 7371709935), (588299397, 3706667899), (559161293, 3735806003), (2120092755, 15059776429), (2036841029, 15143028155), (968469479, 7621465113), (28963863, 239471593), (1753785161, 15426084023), (1670533435, 15509335749), (801966027, 7787968565), (190085041, 1957398607), (718714301, 7871220291), (338544219, 3956423077), (160946937, 1986536711), (309406115, 3985561181), (74229589, 999512235), (552210849, 8037723743), (518910159, 8071024433), (971218937, 16208650247), (921267901, 16258601283), (435658433, 8154276159), (410682915, 8179251677), (385707397, 8204227195), (352406707, 8237527885), (327431189, 8262503403), (302455671, 8287478921), (554960307, 16624908877), (505009271, 16674859913), (113764559, 4181202737), (421757545, 16758111639), (388456855, 16791412329), (338505819, 16841363365), (9017337, 527853575), (59650937, 4235316359), (23581589, 2123902059), (77676011, 8512258581), (30512833, 4264454463), (88750641, 17091118543), (9012537, 2138471111), (55449951, 17124419233), (5498915, 17174370269), (0, 1)]
def sp_s3c2_lit : List (List Nat) := [[411, 67, 386, 67, 475, 1407]]

theorem chain_s3c2_lit : chainOK A_s3c2_lit 249 542 sp_s3c2_lit (1, 0) ((8302946539, 286988053) :: pts_s3c2_lit) = true := by
  decide +kernel
theorem last_s3c2_lit : lastPt (8302946539, 286988053) pts_s3c2_lit = (0, 1) := by decide +kernel

/-- `P(κ)·den²` for the binding vector `[411, 67, 386, 67, 475]`, late 1407, binding early arc `wSt`:
the vector is realisable at some corner iff `P ≥ 0`. Its root in `[0, 1]` is
κ_ex ≈ 0.4593934492 (irrational: discriminant 1184364771172 is not a square). -/
def P_s3c2_lit (k : Kappa) : Int :=
  -24568 * (k.num : Int) * k.num + 1110858 * (k.num : Int) * k.den + -505136 * (k.den : Int) * k.den
/-- **κ < κ_ex** (`P < 0` below `u = 249/542`). -/
def Below_s3c2_lit (k : Kappa) : Prop := k.num * 542 < 249 * k.den ∧ P_s3c2_lit k < 0
instance (k : Kappa) : Decidable (Below_s3c2_lit k) := inferInstanceAs (Decidable (_ ∧ _))

theorem kill_s3c2_lit {k : Kappa} (hb : Below_s3c2_lit k) (c : Corner) (h1 : Scat k c (A_s3c2_lit .wSt) 411)
    (h2 : Scat k c (A_s3c2_lit .wAC) 1407) : False := by
  obtain ⟨hk, hP⟩ := hb
  unfold P_s3c2_lit at hP
  obtain ⟨w0, w1, hw⟩ := c
  simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s3c2_lit] at h1 h2
  have hN := k.num_le
  generalize k.num = N at *
  generalize k.den = D at *
  obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Nat.add_sub_cancel_left] at h1 h2
  have j1 := Int.ofNat_le.mpr h1.1
  have j2 := Int.ofNat_le.mpr h2.2
  push_cast at j1 j2
  simp only [Int.natCast_add] at hP
  have i1 : (w0 : Int) * ((L : Int) * 178 - (N + L) * 411) + (w1 : Int) * ((L : Int) * 761 - (N + L) * 411) ≤ 0 := by
    grind
  have i2 : (w0 : Int) * (((N : Int) + L) * 1407 - (N + N + L) * 258) +
      (w1 : Int) * (((N : Int) + L) * 1407 - (N + N + L) * 965) ≤ 0 := by
    grind
  have := elim2 (by omega) (by omega) (by omega) (by omega) (by omega) i1 i2
  grind

theorem safe_s3c2_lit (k : Kappa) (H_BELOW : Below_s3c2_lit k) (c : Corner) (d : Arc → Nat)
    (H_SCAT : ∀ e, Scat k c (A_s3c2_lit e) (d e)) : Safe F2 G2 true (dlOf d) := by
  apply safe2_of_le
  rcases cover_sound (A_s3c2_lit_pos) (by decide) (by decide) chain_s3c2_lit last_s3c2_lit H_BELOW.1 c d H_SCAT with h | h
  · exact h
  · exfalso
    simp only [sp_s3c2_lit, vec, List.mem_singleton, List.cons.injEq, and_true] at h
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h
    have s1 := H_SCAT .wSt
    have s2 := H_SCAT .wAC
    rw [e1] at s1
    rw [e6] at s2
    exact kill_s3c2_lit H_BELOW c s1 s2

/-- The violating assignment (binding vector, other arcs at their slow endpoint). -/
def dW_s3c2_lit : Arc → Nat
  | .c => 652 | .wSt => 411 | .aSt => 67 | .wQf => 973 | .wQG => 386 | .aG => 67 | .wGC => 475 | .wAC => 1407 | .aC => 124 | .wCf => 685

/-- Between `u` and `κ_fix = 350/761`, `P ≥ 0` (Bernstein certificate). -/
theorem pos_s3c2_lit (k : Kappa) (hfix : k.num * 761 < 350 * k.den) (hb : ¬ Below_s3c2_lit k) : 0 ≤ P_s3c2_lit k := by
  unfold Below_s3c2_lit at hb
  by_cases hu : k.num * 542 < 249 * k.den
  · have := (not_and.mp hb) hu
    omega
  · unfold P_s3c2_lit
    obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 249) (q0 := 542) (p1 := 350) (q1 := 761)
      (by omega) (by omega)
    grind

/-- `P ≥ 0` forces `κ ≥ κ_lo = 3923/8540` (`P < 0` on `[0, κ_lo)`, Bernstein certificate). -/
theorem lo_s3c2_lit (k : Kappa) (hP : 0 ≤ P_s3c2_lit k) : 3923 * k.den ≤ 8540 * k.num := by
  apply Classical.byContradiction; intro h
  unfold P_s3c2_lit at hP
  have hv : (0 : Int) < 3923 * (k.den : Int) - 8540 * k.num := by omega
  have hv2 := Int.mul_pos hv hv
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 0) (q0 := 1) (p1 := 3923) (q1 := 8540)
    (by omega) (by omega)
  grind

/-- On `[κ_lo, κ_fix]` with `P ≥ 0`: the binding vector is realised at the corner where the
late arc is exactly at `(1+κ)·nominal` (`w0 = (den+num)·965 − den·1407`, `w1 = den·1407 − (den+num)·258`). -/
theorem wit_s3c2_lit (k : Kappa) (hlo : 3923 * k.den ≤ 8540 * k.num) (hfix : k.num * 761 ≤ 350 * k.den)
    (hP : 0 ≤ P_s3c2_lit k) (hpos : 0 < (965 * k.num - 442 * k.den) + (1149 * k.den - 258 * k.num)) :
    ∀ e, Scat k ⟨965 * k.num - 442 * k.den, 1149 * k.den - 258 * k.num, hpos⟩ (A_s3c2_lit e) (dW_s3c2_lit e) := by
  intro e
  have hN := k.num_le
  have hD := k.den_pos
  unfold P_s3c2_lit at hP
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 3923) (q0 := 8540) (p1 := 350) (q1 := 761)
    (by omega) (by omega)
  have hs0 : 258 * k.num ≤ 1149 * k.den := by omega
  have hs1 : 442 * k.den ≤ 965 * k.num := by omega
  cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s3c2_lit, dW_s3c2_lit] <;>
  (constructor <;> apply Int.ofNat_le.mp <;>
    push_cast [Int.ofNat_sub hs0, Int.ofNat_sub hs1, Int.ofNat_sub hN] <;> grind)

theorem unsafe_s3c2_lit (k : Kappa) (H_KAPPA : ¬ Below_s3c2_lit k) :
    ∃ c d, (∀ e, Scat k c (A_s3c2_lit e) (d e)) ∧ ¬ Safe F2 G2 true (dlOf d) := by
  by_cases hfix : 350 * k.den ≤ k.num * 761
  · refine ⟨Corner.slow, dW_s3c2_lit, ?_, not_safe2 (by decide) (by decide) (by decide)⟩
    intro e; have := k.num_le
    cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, Corner.slow, A_s3c2_lit, dW_s3c2_lit] <;> omega
  · have hP := pos_s3c2_lit k (by omega) H_KAPPA
    have hlo := lo_s3c2_lit k hP
    have hD := k.den_pos
    exact ⟨_, dW_s3c2_lit, wit_s3c2_lit k hlo (by omega) hP (by omega), not_safe2 (by decide) (by decide) (by decide)⟩

/-- **Exact threshold, seed 3, client 2, `lit`.** Every assignment within κ at every corner is
safe iff `Below_s3c2_lit κ` (i.e. κ < κ_ex ≈ 0.4593934492); otherwise a violating whole-ps assignment exists. -/
theorem exact_s3c2_lit (k : Kappa) :
    (∀ c d, (∀ e, Scat k c (A_s3c2_lit e) (d e)) → Safe F2 G2 true (dlOf d)) ↔ Below_s3c2_lit k := by
  constructor
  · intro hs; apply Classical.byContradiction; intro hb
    obtain ⟨c, d, h1, h2⟩ := unsafe_s3c2_lit k hb
    exact h2 (hs c d h1)
  · intro hb c d h; exact safe_s3c2_lit k hb c d h

/-- Bracket: κ_ex ∈ (1148483623/2500000000, 4593934493/10000000000]. -/
theorem bracket_s3c2_lit : Below_s3c2_lit ⟨1148483623, 2500000000, by decide, by decide⟩ ∧
    ¬ Below_s3c2_lit ⟨4593934493, 10000000000, by decide, by decide⟩ := by decide
theorem nonvac_s3c2_lit : Below_s3c2_lit Kappa.zero := by decide

/-! ### Seed 4, client 1, `lit` -/

/-- Arc endpoints (F, S) ps, seed 4, client 1, `lit` (= `OnNetlistArbKappa.A_s4c1_lit`). -/
def A_s4c1_lit : Tab
  | .c => ⟨172, 522, by decide⟩
  | .wSt => ⟨312, 1079, by decide⟩
  | .aSt => ⟨45, 124, by decide⟩
  | .wQf => ⟨76, 288, by decide⟩
  | .wQG => ⟨172, 571, by decide⟩
  | .aG => ⟨48, 116, by decide⟩
  | .wGC => ⟨127, 471, by decide⟩
  | .wAC => ⟨246, 978, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨214, 689, by decide⟩

theorem A_s4c1_lit_pos : ∀ e, 0 < (A_s4c1_lit e).F := by intro e; cases e <;> decide

/-- Box chain over `[0, 1]` (60 boxes) at `u = 39/94`. -/
def pts_s4c1_lit : List Pt := [(7512266435, 1077668157), (109733291, 24484437), (13116952589, 4062916595), (12270982203, 4908886981), (11474774781, 5705094403), (10711742669, 6468126515), (624904595, 448837229), (9334967335, 7844901849), (2176159115, 2118808181), (4070328101, 4519606491), (474578975, 599162849), (7095633961, 10084235223), (414448727, 659293097), (1549975153, 2744992143), (5801796901, 11378072283), (5420280845, 11759588339), (5055352443, 12124516741), (294188231, 779553593), (2195923129, 6394011463), (4093268475, 13086600709), (1905639173, 6684295419), (110808621, 426062291), (3297061053, 13882808131), (95776059, 441094853), (1424597189, 7165337403), (2650142523, 14529726661), (2451090667, 14728778517), (2285214121, 14894655063), (2119337575, 15060531609), (993318169, 7596616423), (113797487, 959944337), (1688058555, 15491810629), (777678659, 7812255933), (179905467, 1967578181), (83732363, 990009461), (1256779535, 15923089649), (1157253607, 16022615577), (1041140025, 16138729159), (958201751, 16221667433), (437631739, 8152302853), (792325205, 16387543979), (177346733, 4117620563), (321518157, 8268416435), (576685695, 16603183489), (510335077, 16669534107), (460572113, 16719297071), (410809149, 16769060035), (23602115, 1050139709), (344458531, 16835410653), (294695567, 16885173617), (244932603, 16934936581), (57086237, 4237881059), (105878647, 8484055945), (5580687, 531290225), (145406675, 17034462509), (56115683, 8533818909), (79056057, 17100813127), (45880747, 17133988437), (0, 1)]
def sp_s4c1_lit : List (List Nat) := [[631, 73, 334, 68, 276, 1383]]

theorem chain_s4c1_lit : chainOK A_s4c1_lit 39 94 sp_s4c1_lit (1, 0) ((16052967457, 1126901727) :: pts_s4c1_lit) = true := by
  decide +kernel
theorem last_s4c1_lit : lastPt (16052967457, 1126901727) pts_s4c1_lit = (0, 1) := by decide +kernel

/-- `P(κ)·den²` for the binding vector `[631, 73, 334, 68, 276]`, late 1383, binding early arc `wSt`:
the vector is realisable at some corner iff `P ≥ 0`. Its root in `[0, 1]` is
κ_ex ≈ 0.4148922141 (irrational: discriminant 2419882341777 is not a square). -/
def P_s4c1_lit (k : Kappa) : Int :=
  39702 * (k.num : Int) * k.num + 1522653 * (k.num : Int) * k.den + -638571 * (k.den : Int) * k.den
/-- **κ < κ_ex** (`P < 0` below `u = 39/94`). -/
def Below_s4c1_lit (k : Kappa) : Prop := k.num * 94 < 39 * k.den ∧ P_s4c1_lit k < 0
instance (k : Kappa) : Decidable (Below_s4c1_lit k) := inferInstanceAs (Decidable (_ ∧ _))

theorem kill_s4c1_lit {k : Kappa} (hb : Below_s4c1_lit k) (c : Corner) (h1 : Scat k c (A_s4c1_lit .wSt) 631)
    (h2 : Scat k c (A_s4c1_lit .wAC) 1383) : False := by
  obtain ⟨hk, hP⟩ := hb
  unfold P_s4c1_lit at hP
  obtain ⟨w0, w1, hw⟩ := c
  simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s4c1_lit] at h1 h2
  have hN := k.num_le
  generalize k.num = N at *
  generalize k.den = D at *
  obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Nat.add_sub_cancel_left] at h1 h2
  have j1 := Int.ofNat_le.mpr h1.1
  have j2 := Int.ofNat_le.mpr h2.2
  push_cast at j1 j2
  simp only [Int.natCast_add] at hP
  have i1 : (w0 : Int) * ((L : Int) * 312 - (N + L) * 631) + (w1 : Int) * ((L : Int) * 1079 - (N + L) * 631) ≤ 0 := by
    grind
  have i2 : (w0 : Int) * (((N : Int) + L) * 1383 - (N + N + L) * 246) +
      (w1 : Int) * (((N : Int) + L) * 1383 - (N + N + L) * 978) ≤ 0 := by
    grind
  have := elim2 (by omega) (by omega) (by omega) (by omega) (by omega) i1 i2
  grind

theorem safe_s4c1_lit (k : Kappa) (H_BELOW : Below_s4c1_lit k) (c : Corner) (d : Arc → Nat)
    (H_SCAT : ∀ e, Scat k c (A_s4c1_lit e) (d e)) : Safe F1 G1 false (dlOf d) := by
  apply safe1_of_le
  rcases cover_sound (A_s4c1_lit_pos) (by decide) (by decide) chain_s4c1_lit last_s4c1_lit H_BELOW.1 c d H_SCAT with h | h
  · exact h
  · exfalso
    simp only [sp_s4c1_lit, vec, List.mem_singleton, List.cons.injEq, and_true] at h
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h
    have s1 := H_SCAT .wSt
    have s2 := H_SCAT .wAC
    rw [e1] at s1
    rw [e6] at s2
    exact kill_s4c1_lit H_BELOW c s1 s2

/-- The violating assignment (binding vector, other arcs at their slow endpoint). -/
def dW_s4c1_lit : Arc → Nat
  | .c => 522 | .wSt => 631 | .aSt => 73 | .wQf => 288 | .wQG => 334 | .aG => 68 | .wGC => 276 | .wAC => 1383 | .aC => 124 | .wCf => 689

/-- Between `u` and `κ_fix = 448/1079`, `P ≥ 0` (Bernstein certificate). -/
theorem pos_s4c1_lit (k : Kappa) (hfix : k.num * 1079 < 448 * k.den) (hb : ¬ Below_s4c1_lit k) : 0 ≤ P_s4c1_lit k := by
  unfold Below_s4c1_lit at hb
  by_cases hu : k.num * 94 < 39 * k.den
  · have := (not_and.mp hb) hu
    omega
  · unfold P_s4c1_lit
    obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 39) (q0 := 94) (p1 := 448) (q1 := 1079)
      (by omega) (by omega)
    grind

/-- `P ≥ 0` forces `κ ≥ κ_lo = 3221/7764` (`P < 0` on `[0, κ_lo)`, Bernstein certificate). -/
theorem lo_s4c1_lit (k : Kappa) (hP : 0 ≤ P_s4c1_lit k) : 3221 * k.den ≤ 7764 * k.num := by
  apply Classical.byContradiction; intro h
  unfold P_s4c1_lit at hP
  have hv : (0 : Int) < 3221 * (k.den : Int) - 7764 * k.num := by omega
  have hv2 := Int.mul_pos hv hv
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 0) (q0 := 1) (p1 := 3221) (q1 := 7764)
    (by omega) (by omega)
  grind

/-- On `[κ_lo, κ_fix]` with `P ≥ 0`: the binding vector is realised at the corner where the
late arc is exactly at `(1+κ)·nominal` (`w0 = (den+num)·978 − den·1383`, `w1 = den·1383 − (den+num)·246`). -/
theorem wit_s4c1_lit (k : Kappa) (hlo : 3221 * k.den ≤ 7764 * k.num) (hfix : k.num * 1079 ≤ 448 * k.den)
    (hP : 0 ≤ P_s4c1_lit k) (hpos : 0 < (978 * k.num - 405 * k.den) + (1137 * k.den - 246 * k.num)) :
    ∀ e, Scat k ⟨978 * k.num - 405 * k.den, 1137 * k.den - 246 * k.num, hpos⟩ (A_s4c1_lit e) (dW_s4c1_lit e) := by
  intro e
  have hN := k.num_le
  have hD := k.den_pos
  unfold P_s4c1_lit at hP
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 3221) (q0 := 7764) (p1 := 448) (q1 := 1079)
    (by omega) (by omega)
  have hs0 : 246 * k.num ≤ 1137 * k.den := by omega
  have hs1 : 405 * k.den ≤ 978 * k.num := by omega
  cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s4c1_lit, dW_s4c1_lit] <;>
  (constructor <;> apply Int.ofNat_le.mp <;>
    push_cast [Int.ofNat_sub hs0, Int.ofNat_sub hs1, Int.ofNat_sub hN] <;> grind)

theorem unsafe_s4c1_lit (k : Kappa) (H_KAPPA : ¬ Below_s4c1_lit k) :
    ∃ c d, (∀ e, Scat k c (A_s4c1_lit e) (d e)) ∧ ¬ Safe F1 G1 false (dlOf d) := by
  by_cases hfix : 448 * k.den ≤ k.num * 1079
  · refine ⟨Corner.slow, dW_s4c1_lit, ?_, not_safe1 (by decide) (by decide) (by decide)⟩
    intro e; have := k.num_le
    cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, Corner.slow, A_s4c1_lit, dW_s4c1_lit] <;> omega
  · have hP := pos_s4c1_lit k (by omega) H_KAPPA
    have hlo := lo_s4c1_lit k hP
    have hD := k.den_pos
    exact ⟨_, dW_s4c1_lit, wit_s4c1_lit k hlo (by omega) hP (by omega), not_safe1 (by decide) (by decide) (by decide)⟩

/-- **Exact threshold, seed 4, client 1, `lit`.** Every assignment within κ at every corner is
safe iff `Below_s4c1_lit κ` (i.e. κ < κ_ex ≈ 0.4148922141); otherwise a violating whole-ps assignment exists. -/
theorem exact_s4c1_lit (k : Kappa) :
    (∀ c d, (∀ e, Scat k c (A_s4c1_lit e) (d e)) → Safe F1 G1 false (dlOf d)) ↔ Below_s4c1_lit k := by
  constructor
  · intro hs; apply Classical.byContradiction; intro hb
    obtain ⟨c, d, h1, h2⟩ := unsafe_s4c1_lit k hb
    exact h2 (hs c d h1)
  · intro hb c d h; exact safe_s4c1_lit k hb c d h

/-- Bracket: κ_ex ∈ (207446107/500000000, 4148922141/10000000000]. -/
theorem bracket_s4c1_lit : Below_s4c1_lit ⟨207446107, 500000000, by decide, by decide⟩ ∧
    ¬ Below_s4c1_lit ⟨4148922141, 10000000000, by decide, by decide⟩ := by decide
theorem nonvac_s4c1_lit : Below_s4c1_lit Kappa.zero := by decide

/-! ### Seed 4, client 2, `lit` -/

/-- Arc endpoints (F, S) ps, seed 4, client 2, `lit` (= `OnNetlistArbKappa.A_s4c2_lit`). -/
def A_s4c2_lit : Tab
  | .c => ⟨172, 522, by decide⟩
  | .wSt => ⟨312, 1079, by decide⟩
  | .aSt => ⟨45, 124, by decide⟩
  | .wQf => ⟨76, 288, by decide⟩
  | .wQG => ⟨172, 571, by decide⟩
  | .aG => ⟨45, 124, by decide⟩
  | .wGC => ⟨258, 863, by decide⟩
  | .wAC => ⟨256, 942, by decide⟩
  | .aC => ⟨45, 124, by decide⟩
  | .wCf => ⟨71, 274, by decide⟩

theorem A_s4c2_lit_pos : ∀ e, 0 < (A_s4c2_lit e).F := by intro e; cases e <;> decide

/-- Box chain over `[0, 1]` (78 boxes) at `u = 436452/887627`. -/
def pts_s4c2_lit : List Pt := [(15717201073, 1462668111), (7514435931, 1075498661), (14390908203, 2788960981), (13752944545, 3426924639), (6582673219, 2007261373), (12594536849, 4585332335), (12040515777, 5139353407), (5751641611, 2838292981), (10982839185, 6197029999), (10479183665, 6700685519), (10009105179, 7170764005), (9555815211, 7624053973), (4568051139, 4021883453), (8716389345, 8463479839), (4165126723, 4424807869), (7960906065, 9218963119), (7591558683, 9588310501), (7238999819, 9940869365), (6886440955, 10293428229), (6584247643, 10595621541), (6282054331, 10897814853), (5979861019, 11200008165), (5694456225, 11485412959), (5425839947, 11754029237), (2578611835, 6011322757), (4922184427, 12257684757), (4687145185, 12492723999), (2226052971, 6363881621), (2125321867, 6464612725), (4032393009, 13147476175), (1923859659, 6666074933), (1823128555, 6766806037), (3461583419, 13718285765), (3310486763, 13869382421), (3125813073, 14054056111), (2974716417, 14205152767), (2806831243, 14373037941), (2655734587, 14524134597), (2521426449, 14658442735), (2370329793, 14809539391), (1118010827, 7471923765), (1067645275, 7522289317), (2000982411, 15178886773), (941731395, 7648203197), (891365843, 7698568749), (1698789099, 15481080085), (790634739, 7799299853), (740269187, 7849665405), (1396595787, 15783273397), (664720859, 7925213733), (1262287649, 15917581535), (1161556545, 16018312639), (538806979, 8051127613), (1010459889, 16169409295), (943305819, 16236563365), (438075875, 8151858717), (842574715, 16337294469), (758632129, 16421237055), (337344771, 8252589821), (607535473, 16572333711), (557169921, 16622699263), (261796443, 8328138149), (236613667, 8353320925), (439650299, 16740218885), (186248115, 8403686477), (338919195, 16840949989), (288553643, 16891315541), (254976609, 16924892575), (204611057, 16975258127), (187822539, 16992046645), (137456987, 17042412197), (103879953, 17075989231), (35151459, 8554783133), (53514401, 17126354783), (9968683, 8579965909), (3148849, 17176720335), (0, 1)]
def sp_s4c2_lit : List (List Nat) := [[548, 63, 290, 63, 438, 1403]]

theorem chain_s4c2_lit : chainOK A_s4c2_lit 436452 887627 sp_s4c2_lit (1, 0) ((8219553659, 370380933) :: pts_s4c2_lit) = true := by
  decide +kernel
theorem last_s4c2_lit : lastPt (8219553659, 370380933) pts_s4c2_lit = (0, 1) := by decide +kernel

/-- `P(κ)·den²` for the binding vector `[548, 63, 290, 63, 438]`, late 1403, binding early arc `wGC`:
the vector is realisable at some corner iff `P ≥ 0`. Its root in `[0, 1]` is
κ_ex ≈ 0.4917064237 (irrational: discriminant 1371297890649 is not a square). -/
def P_s4c2_lit (k : Kappa) : Int :=
  22108 * (k.num : Int) * k.num + 1149283 * (k.num : Int) * k.den + -570455 * (k.den : Int) * k.den
/-- **κ < κ_ex** (`P < 0` below `u = 436452/887627`). -/
def Below_s4c2_lit (k : Kappa) : Prop := k.num * 887627 < 436452 * k.den ∧ P_s4c2_lit k < 0
instance (k : Kappa) : Decidable (Below_s4c2_lit k) := inferInstanceAs (Decidable (_ ∧ _))

theorem kill_s4c2_lit {k : Kappa} (hb : Below_s4c2_lit k) (c : Corner) (h1 : Scat k c (A_s4c2_lit .wGC) 438)
    (h2 : Scat k c (A_s4c2_lit .wAC) 1403) : False := by
  obtain ⟨hk, hP⟩ := hb
  unfold P_s4c2_lit at hP
  obtain ⟨w0, w1, hw⟩ := c
  simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s4c2_lit] at h1 h2
  have hN := k.num_le
  generalize k.num = N at *
  generalize k.den = D at *
  obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Nat.add_sub_cancel_left] at h1 h2
  have j1 := Int.ofNat_le.mpr h1.1
  have j2 := Int.ofNat_le.mpr h2.2
  push_cast at j1 j2
  simp only [Int.natCast_add] at hP
  have i1 : (w0 : Int) * ((L : Int) * 258 - (N + L) * 438) + (w1 : Int) * ((L : Int) * 863 - (N + L) * 438) ≤ 0 := by
    grind
  have i2 : (w0 : Int) * (((N : Int) + L) * 1403 - (N + N + L) * 256) +
      (w1 : Int) * (((N : Int) + L) * 1403 - (N + N + L) * 942) ≤ 0 := by
    grind
  have := elim2 (by omega) (by omega) (by omega) (by omega) (by omega) i1 i2
  grind

theorem safe_s4c2_lit (k : Kappa) (H_BELOW : Below_s4c2_lit k) (c : Corner) (d : Arc → Nat)
    (H_SCAT : ∀ e, Scat k c (A_s4c2_lit e) (d e)) : Safe F2 G2 true (dlOf d) := by
  apply safe2_of_le
  rcases cover_sound (A_s4c2_lit_pos) (by decide) (by decide) chain_s4c2_lit last_s4c2_lit H_BELOW.1 c d H_SCAT with h | h
  · exact h
  · exfalso
    simp only [sp_s4c2_lit, vec, List.mem_singleton, List.cons.injEq, and_true] at h
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h
    have s1 := H_SCAT .wGC
    have s2 := H_SCAT .wAC
    rw [e5] at s1
    rw [e6] at s2
    exact kill_s4c2_lit H_BELOW c s1 s2

/-- The violating assignment (binding vector, other arcs at their slow endpoint). -/
def dW_s4c2_lit : Arc → Nat
  | .c => 522 | .wSt => 548 | .aSt => 63 | .wQf => 288 | .wQG => 290 | .aG => 63 | .wGC => 438 | .wAC => 1403 | .aC => 124 | .wCf => 274

/-- Between `u` and `κ_fix = 425/863`, `P ≥ 0` (Bernstein certificate). -/
theorem pos_s4c2_lit (k : Kappa) (hfix : k.num * 863 < 425 * k.den) (hb : ¬ Below_s4c2_lit k) : 0 ≤ P_s4c2_lit k := by
  unfold Below_s4c2_lit at hb
  by_cases hu : k.num * 887627 < 436452 * k.den
  · have := (not_and.mp hb) hu
    omega
  · unfold P_s4c2_lit
    obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 436452) (q0 := 887627) (p1 := 425) (q1 := 863)
      (by omega) (by omega)
    grind

/-- `P ≥ 0` forces `κ ≥ κ_lo = 59/120` (`P < 0` on `[0, κ_lo)`, Bernstein certificate). -/
theorem lo_s4c2_lit (k : Kappa) (hP : 0 ≤ P_s4c2_lit k) : 59 * k.den ≤ 120 * k.num := by
  apply Classical.byContradiction; intro h
  unfold P_s4c2_lit at hP
  have hv : (0 : Int) < 59 * (k.den : Int) - 120 * k.num := by omega
  have hv2 := Int.mul_pos hv hv
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 0) (q0 := 1) (p1 := 59) (q1 := 120)
    (by omega) (by omega)
  grind

/-- On `[κ_lo, κ_fix]` with `P ≥ 0`: the binding vector is realised at the corner where the
late arc is exactly at `(1+κ)·nominal` (`w0 = (den+num)·942 − den·1403`, `w1 = den·1403 − (den+num)·256`). -/
theorem wit_s4c2_lit (k : Kappa) (hlo : 59 * k.den ≤ 120 * k.num) (hfix : k.num * 863 ≤ 425 * k.den)
    (hP : 0 ≤ P_s4c2_lit k) (hpos : 0 < (942 * k.num - 461 * k.den) + (1147 * k.den - 256 * k.num)) :
    ∀ e, Scat k ⟨942 * k.num - 461 * k.den, 1147 * k.den - 256 * k.num, hpos⟩ (A_s4c2_lit e) (dW_s4c2_lit e) := by
  intro e
  have hN := k.num_le
  have hD := k.den_pos
  unfold P_s4c2_lit at hP
  obtain ⟨b0, b1, b2⟩ := bern (k.num : Int) (k.den : Int) (p0 := 59) (q0 := 120) (p1 := 425) (q1 := 863)
    (by omega) (by omega)
  have hs0 : 256 * k.num ≤ 1147 * k.den := by omega
  have hs1 : 461 * k.den ≤ 942 * k.num := by omega
  cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, A_s4c2_lit, dW_s4c2_lit] <;>
  (constructor <;> apply Int.ofNat_le.mp <;>
    push_cast [Int.ofNat_sub hs0, Int.ofNat_sub hs1, Int.ofNat_sub hN] <;> grind)

theorem unsafe_s4c2_lit (k : Kappa) (H_KAPPA : ¬ Below_s4c2_lit k) :
    ∃ c d, (∀ e, Scat k c (A_s4c2_lit e) (d e)) ∧ ¬ Safe F2 G2 true (dlOf d) := by
  by_cases hfix : 425 * k.den ≤ k.num * 863
  · refine ⟨Corner.slow, dW_s4c2_lit, ?_, not_safe2 (by decide) (by decide) (by decide)⟩
    intro e; have := k.num_le
    cases e <;> simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, Corner.slow, A_s4c2_lit, dW_s4c2_lit] <;> omega
  · have hP := pos_s4c2_lit k (by omega) H_KAPPA
    have hlo := lo_s4c2_lit k hP
    have hD := k.den_pos
    exact ⟨_, dW_s4c2_lit, wit_s4c2_lit k hlo (by omega) hP (by omega), not_safe2 (by decide) (by decide) (by decide)⟩

/-- **Exact threshold, seed 4, client 2, `lit`.** Every assignment within κ at every corner is
safe iff `Below_s4c2_lit κ` (i.e. κ < κ_ex ≈ 0.4917064237); otherwise a violating whole-ps assignment exists. -/
theorem exact_s4c2_lit (k : Kappa) :
    (∀ c d, (∀ e, Scat k c (A_s4c2_lit e) (d e)) → Safe F2 G2 true (dlOf d)) ↔ Below_s4c2_lit k := by
  constructor
  · intro hs; apply Classical.byContradiction; intro hb
    obtain ⟨c, d, h1, h2⟩ := unsafe_s4c2_lit k hb
    exact h2 (hs c d h1)
  · intro hb c d h; exact safe_s4c2_lit k hb c d h

/-- Bracket: κ_ex ∈ (1229266059/2500000000, 4917064237/10000000000]. -/
theorem bracket_s4c2_lit : Below_s4c2_lit ⟨1229266059, 2500000000, by decide, by decide⟩ ∧
    ¬ Below_s4c2_lit ⟨4917064237, 10000000000, by decide, by decide⟩ := by decide
theorem nonvac_s4c2_lit : Below_s4c2_lit Kappa.zero := by decide

/-! ## 7. Verdicts at the reference κ, and the audit point -/

/-- Rule A's κ = 1/11 and rule E's / the guardband's κE = 383/1927. -/
def κA : Kappa := ⟨1, 11, by decide, by decide⟩
def κE : Kappa := ⟨383, 1927, by decide, by decide⟩

/-- At κ = 1/11 all 16 (pair, reading) are exactly safe. -/
theorem verdict_κA :
    Below_s1c1_cons κA ∧ Below_s1c2_cons κA ∧ Below_s2c1_cons κA ∧ Below_s2c2_cons κA ∧
    Below_s3c1_cons κA ∧ Below_s3c2_cons κA ∧ Below_s4c1_cons κA ∧ Below_s4c2_cons κA ∧
    Below_s1c1_lit κA ∧ Below_s1c2_lit κA ∧ Below_s2c1_lit κA ∧ Below_s2c2_lit κA ∧
    Below_s3c1_lit κA ∧ Below_s3c2_lit κA ∧ Below_s4c1_lit κA ∧ Below_s4c2_lit κA := by
  decide

/-- At κE = 383/1927: 15/16 safe; s1 client 2 `cons` is not. -/
theorem verdict_κE :
    Below_s1c1_cons κE ∧ ¬ Below_s1c2_cons κE ∧ Below_s2c1_cons κE ∧ Below_s2c2_cons κE ∧
    Below_s3c1_cons κE ∧ Below_s3c2_cons κE ∧ Below_s4c1_cons κE ∧ Below_s4c2_cons κE ∧
    Below_s1c1_lit κE ∧ Below_s1c2_lit κE ∧ Below_s2c1_lit κE ∧ Below_s2c2_lit κE ∧
    Below_s3c1_lit κE ∧ Below_s3c2_lit κE ∧ Below_s4c1_lit κE ∧ Below_s4c2_lit κE := by
  decide

/-- The auditor's point κ = 200/1103 (inside `OnNetlistArbKappa`'s undecided gap
(197/1103, 203/1103)): CONFIRMED unsafe, with the auditor's own assignment at the fast corner
(late 535 > early 215+37+100+37+145 = 534). -/
def k200 : Kappa := ⟨200, 1103, by decide, by decide⟩

theorem audit_s1c2_cons_200 :
    ¬ Below_s1c2_cons k200 ∧
    (∀ e, Scat k200 Corner.fast (A_s1c2_cons e) (dW_s1c2_cons e)) ∧
      ¬ Safe F2 G2 true (dlOf dW_s1c2_cons) :=
  ⟨by decide, by intro e; cases e <;> decide, not_safe2 (by decide) (by decide) (by decide)⟩

/-- The exact threshold is NOT the fast-corner one: at κ = 1807/10000 (between
κ_ex ≈ 0.1806787 and the fast-corner whole-ps threshold 82/453 ≈ 0.1810155) every
fast-corner assignment is safe, yet the pair is unsafe (at an interior corner, `unsafe_*`). -/
def k1807 : Kappa := ⟨1807, 10000, by decide, by decide⟩

theorem interior_s1c2_cons :
    (∀ d : Arc → Nat, (∀ e, Scat k1807 Corner.fast (A_s1c2_cons e) (d e)) →
      Safe F2 G2 true (dlOf d)) ∧
    ∃ c d, (∀ e, Scat k1807 c (A_s1c2_cons e) (d e)) ∧ ¬ Safe F2 G2 true (dlOf d) := by
  refine ⟨fun d h => safe2_of_le ?_, unsafe_s1c2_cons k1807 (by decide)⟩
  have h1 := h .wSt; have h2 := h .aSt; have h3 := h .wQG; have h4 := h .aG; have h5 := h .wGC
  have h6 := h .wAC
  simp only [Scat, Kappa.lo, Kappa.hi, nom, Corner.W, Corner.fast, A_s1c2_cons, k1807] at h1 h2 h3 h4 h5 h6
  omega

/-- Non-vacuity of the safe side: at κ = 0 the fast endpoints realise every table. -/
theorem realizes_fast_zero (A : Tab) : ∀ e, Scat Kappa.zero Corner.fast (A e) (A e).F := by
  intro e
  simp only [Scat, Kappa.zero, Kappa.lo, Kappa.hi, nom, Corner.fast, Corner.W]
  omega

/-! ## 8. Bridge to A's `CornerNat` and `OnNetlistArbKappa`'s tables

`Scat` is definitionally A's (`scat_iff`, `Iff.rfl`), the tables are equal arc by arc (`tab_*`,
`rfl`), so `exact_*` holds verbatim in `OnNetlistArbKappa`'s vocabulary (`Bridge.exact_*`). -/

namespace Bridge

open Formal.Cells.ArbA0Fork
abbrev OA := Formal.Cells.OnNetlistArbKappa.Arc
abbrev NA := Formal.Cells.OnNetlistArbKappaExact.Arc

def toK (k : Formal.Core.Substrate.Kappa) : Formal.Cells.OnNetlistArbKappaExact.Kappa :=
  ⟨k.num, k.den, k.den_pos, k.num_le⟩
def toC (c : Formal.Core.Substrate.Corner) : Formal.Cells.OnNetlistArbKappaExact.Corner :=
  ⟨c.w0, c.w1, c.pos⟩
def ofC (c : Formal.Cells.OnNetlistArbKappaExact.Corner) : Formal.Core.Substrate.Corner :=
  ⟨c.w0, c.w1, c.pos⟩
def toA (a : Formal.Core.Substrate.CArc) : Formal.Cells.OnNetlistArbKappaExact.CArc :=
  ⟨a.F, a.S, a.F_le_S⟩

def fwd : OA → NA
  | .c => .c | .wSt => .wSt | .aSt => .aSt | .wQf => .wQf | .wQG => .wQG | .aG => .aG
  | .wGC => .wGC | .wAC => .wAC | .aC => .aC | .wCf => .wCf
def bwd : NA → OA
  | .c => .c | .wSt => .wSt | .aSt => .aSt | .wQf => .wQf | .wQG => .wQG | .aG => .aG
  | .wGC => .wGC | .wAC => .wAC | .aC => .aC | .wCf => .wCf

/-- `Scat` is the same predicate (definitionally). -/
theorem scat_iff (k : Formal.Core.Substrate.Kappa) (c : Formal.Core.Substrate.Corner)
    (a : Formal.Core.Substrate.CArc) (d : Nat) :
    Formal.Core.Substrate.Scat k c a d ↔ Formal.Cells.OnNetlistArbKappaExact.Scat (toK k) (toC c) (toA a) d :=
  Iff.rfl

/-- Transfer of the universally quantified safety statement. -/
theorem transfer (k : Formal.Core.Substrate.Kappa) (Ao : OA → Formal.Core.Substrate.CArc)
    (An : NA → Formal.Cells.OnNetlistArbKappaExact.CArc) (hA : ∀ e, toA (Ao e) = An (fwd e))
    (Q : Dl → Prop) :
    (∀ c d, (∀ e, Formal.Core.Substrate.Scat k c (Ao e) (d e)) →
        Q (Formal.Cells.OnNetlistArbKappa.dlOf d)) ↔
      (∀ c d, (∀ e, Formal.Cells.OnNetlistArbKappaExact.Scat (toK k) c (An e) (d e)) →
        Q (Formal.Cells.OnNetlistArbKappaExact.dlOf d)) := by
  constructor
  · intro h c d hS
    have := h (ofC c) (fun e => d (fwd e)) (fun e => by
      rw [scat_iff, hA e]; exact hS (fwd e))
    exact this
  · intro h c d hS
    have := h (toC c) (fun e => d (bwd e)) (fun e => by
      have := hS (bwd e); rw [scat_iff, hA (bwd e)] at this
      cases e <;> exact this)
    exact this

theorem tab_s1c1_cons : ∀ e, toA (Formal.Cells.OnNetlistArbKappa.A_s1c1_cons e) =
    Formal.Cells.OnNetlistArbKappaExact.A_s1c1_cons (fwd e) := by intro e; cases e <;> rfl
/-- `exact_s1c1_cons` in `OnNetlistArbKappa`'s vocabulary (A's `CornerNat`). -/
theorem exact_s1c1_cons (k : Formal.Core.Substrate.Kappa) :
    (∀ c d, (∀ e, Formal.Core.Substrate.Scat k c (Formal.Cells.OnNetlistArbKappa.A_s1c1_cons e) (d e)) →
      Safe F1 G1 false (Formal.Cells.OnNetlistArbKappa.dlOf d)) ↔
    Formal.Cells.OnNetlistArbKappaExact.Below_s1c1_cons (toK k) :=
  (transfer k _ _ tab_s1c1_cons _).trans (Formal.Cells.OnNetlistArbKappaExact.exact_s1c1_cons (toK k))

theorem tab_s1c2_cons : ∀ e, toA (Formal.Cells.OnNetlistArbKappa.A_s1c2_cons e) =
    Formal.Cells.OnNetlistArbKappaExact.A_s1c2_cons (fwd e) := by intro e; cases e <;> rfl
/-- `exact_s1c2_cons` in `OnNetlistArbKappa`'s vocabulary (A's `CornerNat`). -/
theorem exact_s1c2_cons (k : Formal.Core.Substrate.Kappa) :
    (∀ c d, (∀ e, Formal.Core.Substrate.Scat k c (Formal.Cells.OnNetlistArbKappa.A_s1c2_cons e) (d e)) →
      Safe F2 G2 true (Formal.Cells.OnNetlistArbKappa.dlOf d)) ↔
    Formal.Cells.OnNetlistArbKappaExact.Below_s1c2_cons (toK k) :=
  (transfer k _ _ tab_s1c2_cons _).trans (Formal.Cells.OnNetlistArbKappaExact.exact_s1c2_cons (toK k))

theorem tab_s2c1_cons : ∀ e, toA (Formal.Cells.OnNetlistArbKappa.A_s2c1_cons e) =
    Formal.Cells.OnNetlistArbKappaExact.A_s2c1_cons (fwd e) := by intro e; cases e <;> rfl
/-- `exact_s2c1_cons` in `OnNetlistArbKappa`'s vocabulary (A's `CornerNat`). -/
theorem exact_s2c1_cons (k : Formal.Core.Substrate.Kappa) :
    (∀ c d, (∀ e, Formal.Core.Substrate.Scat k c (Formal.Cells.OnNetlistArbKappa.A_s2c1_cons e) (d e)) →
      Safe F1 G1 false (Formal.Cells.OnNetlistArbKappa.dlOf d)) ↔
    Formal.Cells.OnNetlistArbKappaExact.Below_s2c1_cons (toK k) :=
  (transfer k _ _ tab_s2c1_cons _).trans (Formal.Cells.OnNetlistArbKappaExact.exact_s2c1_cons (toK k))

theorem tab_s2c2_cons : ∀ e, toA (Formal.Cells.OnNetlistArbKappa.A_s2c2_cons e) =
    Formal.Cells.OnNetlistArbKappaExact.A_s2c2_cons (fwd e) := by intro e; cases e <;> rfl
/-- `exact_s2c2_cons` in `OnNetlistArbKappa`'s vocabulary (A's `CornerNat`). -/
theorem exact_s2c2_cons (k : Formal.Core.Substrate.Kappa) :
    (∀ c d, (∀ e, Formal.Core.Substrate.Scat k c (Formal.Cells.OnNetlistArbKappa.A_s2c2_cons e) (d e)) →
      Safe F2 G2 true (Formal.Cells.OnNetlistArbKappa.dlOf d)) ↔
    Formal.Cells.OnNetlistArbKappaExact.Below_s2c2_cons (toK k) :=
  (transfer k _ _ tab_s2c2_cons _).trans (Formal.Cells.OnNetlistArbKappaExact.exact_s2c2_cons (toK k))

theorem tab_s3c1_cons : ∀ e, toA (Formal.Cells.OnNetlistArbKappa.A_s3c1_cons e) =
    Formal.Cells.OnNetlistArbKappaExact.A_s3c1_cons (fwd e) := by intro e; cases e <;> rfl
/-- `exact_s3c1_cons` in `OnNetlistArbKappa`'s vocabulary (A's `CornerNat`). -/
theorem exact_s3c1_cons (k : Formal.Core.Substrate.Kappa) :
    (∀ c d, (∀ e, Formal.Core.Substrate.Scat k c (Formal.Cells.OnNetlistArbKappa.A_s3c1_cons e) (d e)) →
      Safe F1 G1 false (Formal.Cells.OnNetlistArbKappa.dlOf d)) ↔
    Formal.Cells.OnNetlistArbKappaExact.Below_s3c1_cons (toK k) :=
  (transfer k _ _ tab_s3c1_cons _).trans (Formal.Cells.OnNetlistArbKappaExact.exact_s3c1_cons (toK k))

theorem tab_s3c2_cons : ∀ e, toA (Formal.Cells.OnNetlistArbKappa.A_s3c2_cons e) =
    Formal.Cells.OnNetlistArbKappaExact.A_s3c2_cons (fwd e) := by intro e; cases e <;> rfl
/-- `exact_s3c2_cons` in `OnNetlistArbKappa`'s vocabulary (A's `CornerNat`). -/
theorem exact_s3c2_cons (k : Formal.Core.Substrate.Kappa) :
    (∀ c d, (∀ e, Formal.Core.Substrate.Scat k c (Formal.Cells.OnNetlistArbKappa.A_s3c2_cons e) (d e)) →
      Safe F2 G2 true (Formal.Cells.OnNetlistArbKappa.dlOf d)) ↔
    Formal.Cells.OnNetlistArbKappaExact.Below_s3c2_cons (toK k) :=
  (transfer k _ _ tab_s3c2_cons _).trans (Formal.Cells.OnNetlistArbKappaExact.exact_s3c2_cons (toK k))

theorem tab_s4c1_cons : ∀ e, toA (Formal.Cells.OnNetlistArbKappa.A_s4c1_cons e) =
    Formal.Cells.OnNetlistArbKappaExact.A_s4c1_cons (fwd e) := by intro e; cases e <;> rfl
/-- `exact_s4c1_cons` in `OnNetlistArbKappa`'s vocabulary (A's `CornerNat`). -/
theorem exact_s4c1_cons (k : Formal.Core.Substrate.Kappa) :
    (∀ c d, (∀ e, Formal.Core.Substrate.Scat k c (Formal.Cells.OnNetlistArbKappa.A_s4c1_cons e) (d e)) →
      Safe F1 G1 false (Formal.Cells.OnNetlistArbKappa.dlOf d)) ↔
    Formal.Cells.OnNetlistArbKappaExact.Below_s4c1_cons (toK k) :=
  (transfer k _ _ tab_s4c1_cons _).trans (Formal.Cells.OnNetlistArbKappaExact.exact_s4c1_cons (toK k))

theorem tab_s4c2_cons : ∀ e, toA (Formal.Cells.OnNetlistArbKappa.A_s4c2_cons e) =
    Formal.Cells.OnNetlistArbKappaExact.A_s4c2_cons (fwd e) := by intro e; cases e <;> rfl
/-- `exact_s4c2_cons` in `OnNetlistArbKappa`'s vocabulary (A's `CornerNat`). -/
theorem exact_s4c2_cons (k : Formal.Core.Substrate.Kappa) :
    (∀ c d, (∀ e, Formal.Core.Substrate.Scat k c (Formal.Cells.OnNetlistArbKappa.A_s4c2_cons e) (d e)) →
      Safe F2 G2 true (Formal.Cells.OnNetlistArbKappa.dlOf d)) ↔
    Formal.Cells.OnNetlistArbKappaExact.Below_s4c2_cons (toK k) :=
  (transfer k _ _ tab_s4c2_cons _).trans (Formal.Cells.OnNetlistArbKappaExact.exact_s4c2_cons (toK k))

theorem tab_s1c1_lit : ∀ e, toA (Formal.Cells.OnNetlistArbKappa.A_s1c1_lit e) =
    Formal.Cells.OnNetlistArbKappaExact.A_s1c1_lit (fwd e) := by intro e; cases e <;> rfl
/-- `exact_s1c1_lit` in `OnNetlistArbKappa`'s vocabulary (A's `CornerNat`). -/
theorem exact_s1c1_lit (k : Formal.Core.Substrate.Kappa) :
    (∀ c d, (∀ e, Formal.Core.Substrate.Scat k c (Formal.Cells.OnNetlistArbKappa.A_s1c1_lit e) (d e)) →
      Safe F1 G1 false (Formal.Cells.OnNetlistArbKappa.dlOf d)) ↔
    Formal.Cells.OnNetlistArbKappaExact.Below_s1c1_lit (toK k) :=
  (transfer k _ _ tab_s1c1_lit _).trans (Formal.Cells.OnNetlistArbKappaExact.exact_s1c1_lit (toK k))

theorem tab_s1c2_lit : ∀ e, toA (Formal.Cells.OnNetlistArbKappa.A_s1c2_lit e) =
    Formal.Cells.OnNetlistArbKappaExact.A_s1c2_lit (fwd e) := by intro e; cases e <;> rfl
/-- `exact_s1c2_lit` in `OnNetlistArbKappa`'s vocabulary (A's `CornerNat`). -/
theorem exact_s1c2_lit (k : Formal.Core.Substrate.Kappa) :
    (∀ c d, (∀ e, Formal.Core.Substrate.Scat k c (Formal.Cells.OnNetlistArbKappa.A_s1c2_lit e) (d e)) →
      Safe F2 G2 true (Formal.Cells.OnNetlistArbKappa.dlOf d)) ↔
    Formal.Cells.OnNetlistArbKappaExact.Below_s1c2_lit (toK k) :=
  (transfer k _ _ tab_s1c2_lit _).trans (Formal.Cells.OnNetlistArbKappaExact.exact_s1c2_lit (toK k))

theorem tab_s2c1_lit : ∀ e, toA (Formal.Cells.OnNetlistArbKappa.A_s2c1_lit e) =
    Formal.Cells.OnNetlistArbKappaExact.A_s2c1_lit (fwd e) := by intro e; cases e <;> rfl
/-- `exact_s2c1_lit` in `OnNetlistArbKappa`'s vocabulary (A's `CornerNat`). -/
theorem exact_s2c1_lit (k : Formal.Core.Substrate.Kappa) :
    (∀ c d, (∀ e, Formal.Core.Substrate.Scat k c (Formal.Cells.OnNetlistArbKappa.A_s2c1_lit e) (d e)) →
      Safe F1 G1 false (Formal.Cells.OnNetlistArbKappa.dlOf d)) ↔
    Formal.Cells.OnNetlistArbKappaExact.Below_s2c1_lit (toK k) :=
  (transfer k _ _ tab_s2c1_lit _).trans (Formal.Cells.OnNetlistArbKappaExact.exact_s2c1_lit (toK k))

theorem tab_s2c2_lit : ∀ e, toA (Formal.Cells.OnNetlistArbKappa.A_s2c2_lit e) =
    Formal.Cells.OnNetlistArbKappaExact.A_s2c2_lit (fwd e) := by intro e; cases e <;> rfl
/-- `exact_s2c2_lit` in `OnNetlistArbKappa`'s vocabulary (A's `CornerNat`). -/
theorem exact_s2c2_lit (k : Formal.Core.Substrate.Kappa) :
    (∀ c d, (∀ e, Formal.Core.Substrate.Scat k c (Formal.Cells.OnNetlistArbKappa.A_s2c2_lit e) (d e)) →
      Safe F2 G2 true (Formal.Cells.OnNetlistArbKappa.dlOf d)) ↔
    Formal.Cells.OnNetlistArbKappaExact.Below_s2c2_lit (toK k) :=
  (transfer k _ _ tab_s2c2_lit _).trans (Formal.Cells.OnNetlistArbKappaExact.exact_s2c2_lit (toK k))

theorem tab_s3c1_lit : ∀ e, toA (Formal.Cells.OnNetlistArbKappa.A_s3c1_lit e) =
    Formal.Cells.OnNetlistArbKappaExact.A_s3c1_lit (fwd e) := by intro e; cases e <;> rfl
/-- `exact_s3c1_lit` in `OnNetlistArbKappa`'s vocabulary (A's `CornerNat`). -/
theorem exact_s3c1_lit (k : Formal.Core.Substrate.Kappa) :
    (∀ c d, (∀ e, Formal.Core.Substrate.Scat k c (Formal.Cells.OnNetlistArbKappa.A_s3c1_lit e) (d e)) →
      Safe F1 G1 false (Formal.Cells.OnNetlistArbKappa.dlOf d)) ↔
    Formal.Cells.OnNetlistArbKappaExact.Below_s3c1_lit (toK k) :=
  (transfer k _ _ tab_s3c1_lit _).trans (Formal.Cells.OnNetlistArbKappaExact.exact_s3c1_lit (toK k))

theorem tab_s3c2_lit : ∀ e, toA (Formal.Cells.OnNetlistArbKappa.A_s3c2_lit e) =
    Formal.Cells.OnNetlistArbKappaExact.A_s3c2_lit (fwd e) := by intro e; cases e <;> rfl
/-- `exact_s3c2_lit` in `OnNetlistArbKappa`'s vocabulary (A's `CornerNat`). -/
theorem exact_s3c2_lit (k : Formal.Core.Substrate.Kappa) :
    (∀ c d, (∀ e, Formal.Core.Substrate.Scat k c (Formal.Cells.OnNetlistArbKappa.A_s3c2_lit e) (d e)) →
      Safe F2 G2 true (Formal.Cells.OnNetlistArbKappa.dlOf d)) ↔
    Formal.Cells.OnNetlistArbKappaExact.Below_s3c2_lit (toK k) :=
  (transfer k _ _ tab_s3c2_lit _).trans (Formal.Cells.OnNetlistArbKappaExact.exact_s3c2_lit (toK k))

theorem tab_s4c1_lit : ∀ e, toA (Formal.Cells.OnNetlistArbKappa.A_s4c1_lit e) =
    Formal.Cells.OnNetlistArbKappaExact.A_s4c1_lit (fwd e) := by intro e; cases e <;> rfl
/-- `exact_s4c1_lit` in `OnNetlistArbKappa`'s vocabulary (A's `CornerNat`). -/
theorem exact_s4c1_lit (k : Formal.Core.Substrate.Kappa) :
    (∀ c d, (∀ e, Formal.Core.Substrate.Scat k c (Formal.Cells.OnNetlistArbKappa.A_s4c1_lit e) (d e)) →
      Safe F1 G1 false (Formal.Cells.OnNetlistArbKappa.dlOf d)) ↔
    Formal.Cells.OnNetlistArbKappaExact.Below_s4c1_lit (toK k) :=
  (transfer k _ _ tab_s4c1_lit _).trans (Formal.Cells.OnNetlistArbKappaExact.exact_s4c1_lit (toK k))

theorem tab_s4c2_lit : ∀ e, toA (Formal.Cells.OnNetlistArbKappa.A_s4c2_lit e) =
    Formal.Cells.OnNetlistArbKappaExact.A_s4c2_lit (fwd e) := by intro e; cases e <;> rfl
/-- `exact_s4c2_lit` in `OnNetlistArbKappa`'s vocabulary (A's `CornerNat`). -/
theorem exact_s4c2_lit (k : Formal.Core.Substrate.Kappa) :
    (∀ c d, (∀ e, Formal.Core.Substrate.Scat k c (Formal.Cells.OnNetlistArbKappa.A_s4c2_lit e) (d e)) →
      Safe F2 G2 true (Formal.Cells.OnNetlistArbKappa.dlOf d)) ↔
    Formal.Cells.OnNetlistArbKappaExact.Below_s4c2_lit (toK k) :=
  (transfer k _ _ tab_s4c2_lit _).trans (Formal.Cells.OnNetlistArbKappaExact.exact_s4c2_lit (toK k))

end Bridge

end Formal.Cells.OnNetlistArbKappaExact
