-- Bsa4 mutant M05 of Formal/Cells/Necessity5Arb.lean: one change, 'theorem formA_run (h : d5 + L + 1 ≤ d6)' -> 'theorem formA_run (h : d5 + L ≤ d6)'. Expected: FAIL.
import Formal.Cells.ArbBinary

/-!
# Necessity5Arb: `bd_arbcell.grant_skew` is EXACT; settled exclusion's exact condition

Probe Bnx5 (shard B). Row `bd_arbcell.grant_skew` (`|d6 - d5| ≤ L`, two
forms, margin 0, no strict +1) was "sufficient", backed by
`ArbBinary.exclusion_transport`. Bsx3's `Necessity3Arb` refuted it at one
parameter point per form (`L = 4`, `(d5, d6) = (1, 6)` and `(6, 1)`).
This file generalises those two runs to EVERY violating delay triple.

Model (unchanged, `ArbBinary` section 4): `bd_arbcell` in discrete time with
constant transport delays, the REAL INITs (state `bd_c2n_set` `FFB2..`,
rst = 0; grant LUT6_2 `0C0C_0C0C_A0A0_A0A0`, `O5 = g1`, `O6 = g2`), one loop
delay `L` for q (state LUT arc + the one feedback net that reaches both LUTs'
`I2`), grant arcs `d5`, `d6`; hypotheses H_INIT_SETTLED and H_REQ_SEP
(request edges more than `L` apart).

* **Assumed:** `0 < L`; the gate relations `Sat` hold at every instant.
* **Proved:** `grant_skew_exact`: for every `D` with `0 < D.L`,
  (every trace with `Sat`, H_INIT_SETTLED, H_REQ_SEP has `g1 ∧ g2` false at
  every `T ≥ d5, d6`) **iff** `H_GRANT_SKEW D`. The `←` side is the shipped
  `exclusion_transport`; the `→` side is `formA_run` / `formB_run`: for any
  `d6 ≥ d5 + L + 1` (resp. the mirror) an opposite-sense handover with
  request edges exactly `L + 1` apart overlaps both grants at
  `T = a + 2L + 1 + d5` (resp. `+ d6`). Each run is a real handover (q
  moves: `formA_handover`, `formB_handover`). Per form: `formA_iff`,
  `formB_iff` (each form alone is exact given the other).
* **Settled exclusion** (`bd_arbcell.settled_exclusion`): the identity
  `g1 ∧ g2 = false` needs both grant outputs to read the SAME q. Exact
  condition when they read `qa` (g1) and `qb` (g2): `settled_iff` — exclusion
  for every request vector iff `¬ (qa = 1 ∧ qb = 0)`. The overlap needs
  `r1 = r2 = 1` (`settled_overlap_needs_both`).
* **NOT covered:** Kleene X on q (a metastable q reaches both grants,
  `ArbBinary.kleene_x_reaches_both`); routing skew between the two `I2`
  branches of the q net and request-routing skew (the model has one q delay
  and requests arriving at both LUTs together); involution / inertial
  channels (`bd_arbcell.bbm`); non-constant delays (a bounded-delay box
  contains these constant-delay runs, so the necessity side carries over to
  any box containing a violating triple; sufficiency over a box is not
  re-proved here).

The row's JSON form has margin 0 and no strict field, so the iff covers the
JSON form as written (in this binary model).

Core Lean only.
-/

namespace Formal.Cells.Necessity5Arb
open Formal.Cells Formal.Cells.ArbBinary

/-- The conclusion of `exclusion_transport` for all admissible traces. -/
def Excl (D : Delays) : Prop :=
  ∀ tr : Trace, Sat D tr → H_INIT_SETTLED D tr → H_REQ_SEP D tr →
    ∀ T, D.d5 ≤ T → D.d6 ≤ T → (tr.g1 T && tr.g2 T) = false

/-- Grant outputs defined from the inputs by their transport relations. -/
def gOut (d : Nat) (f : Bool → Bool → Bool → Bool) (r1 r2 q : Nat → Bool) (t : Nat) : Bool :=
  if t < d then false else f (r1 (t - d)) (r2 (t - d)) (q (t - d))

theorem gOut_rel (d : Nat) (f : Bool → Bool → Bool → Bool) (r1 r2 q : Nat → Bool) (t : Nat) :
    gOut d f r1 r2 q (t + d) = f (r1 t) (r2 t) (q t) := by
  simp [gOut]

/-! ## Form A violated: `d6 ≥ d5 + L + 1`

r2 is being served (q = 0). r1 rises at `a`, r2 falls at `a + L + 1`
(edges at `a - 1` and `a + L`: exactly `L + 1` apart). q rises at
`a + 2L + 1`. With `a = d6 + L + 1`. -/

section formA
variable (L d5 d6 : Nat)

def r1A (t : Nat) : Bool := decide ((d6 + L + 1) ≤ t)
def r2A (t : Nat) : Bool := decide (t ≤ (d6 + L + 1) + L)
def qA (t : Nat) : Bool := decide ((d6 + L + 1) + 2 * L + 1 ≤ t)
def trA : Trace :=
  ⟨r1A L d6, r2A L d6, qA L d6, gOut d5 gr1 (r1A L d6) (r2A L d6) (qA L d6),
    gOut d6 gr2 (r1A L d6) (r2A L d6) (qA L d6)⟩
def DA : Delays := ⟨L, d5, d6⟩

theorem A_sat : Sat (DA L d5 d6) (trA L d5 d6) where
  hq := by
    intro t; simp only [trA, DA, qA, r1A, r2A, stF_eq]; arbbin_omega
  hg1 := fun t => gOut_rel _ _ _ _ _ t
  hg2 := fun t => gOut_rel _ _ _ _ _ t

theorem A_init : H_INIT_SETTLED (DA L d5 d6) (trA L d5 d6) := by
  refine ⟨fun t ht => ?_, ?_⟩
  · simp only [trA, DA, r1A, r2A, qA] at *
    refine ⟨?_, ?_, ?_⟩ <;> arbbin_omega
  · simp only [trA, r1A, r2A, qA, stF_eq]; arbbin_omega

theorem A_sep : H_REQ_SEP (DA L d5 d6) (trA L d5 d6) := by
  intro i j hij hi hj
  simp only [redge, trA, r1A, r2A, DA, ne_eq] at *
  arbbin_omega

/-- The run is a real handover: q moves from 0 (r2 served) to 1. -/
theorem formA_handover : qA L d6 0 = false ∧ qA L d6 ((d6 + L + 1) + 2 * L + 1) = true := by
  simp [qA]

/-- Both grants high at `T = a + 2L + 1 + d5` whenever `d6 ≥ d5 + L + 1`. -/
theorem formA_overlap (h : d5 + L + 1 ≤ d6) :
    ((trA L d5 d6).g1 ((d6 + L + 1) + 2 * L + 1 + d5) &&
      (trA L d5 d6).g2 ((d6 + L + 1) + 2 * L + 1 + d5)) = true := by
  have e : (d6 + L + 1) + 2 * L + 1 + d5 = ((d6 + L + 1) + 2 * L + 1 + d5 - d6) + d6 := by
    omega
  show (gOut d5 gr1 _ _ _ ((d6 + L + 1) + 2 * L + 1 + d5) && gOut d6 gr2 _ _ _ _) = true
  rw [gOut_rel, e, gOut_rel, gr1_eq, gr2_eq]
  simp only [r1A, r2A, qA]
  arbbin_omega

theorem formA_run (h : d5 + L ≤ d6) : ¬ Excl (DA L d5 d6) := by
  intro hE
  have := hE _ (A_sat L d5 d6) (A_init L d5 d6) (A_sep L d5 d6) ((d6 + L + 1) + 2 * L + 1 + d5)
    (by simp [DA]) (by simp only [DA]; omega)
  rw [formA_overlap L d5 d6 h] at this; exact absurd this (by decide)

end formA

/-! ## Form B violated: `d5 ≥ d6 + L + 1` (the mirror) -/

section formB
variable (L d5 d6 : Nat)

def r1B (t : Nat) : Bool := decide (t ≤ (d5 + L + 1) + L)
def r2B (t : Nat) : Bool := decide ((d5 + L + 1) ≤ t)
def qB (t : Nat) : Bool := decide (t < (d5 + L + 1) + 2 * L + 1)
def trB : Trace :=
  ⟨r1B L d5, r2B L d5, qB L d5, gOut d5 gr1 (r1B L d5) (r2B L d5) (qB L d5),
    gOut d6 gr2 (r1B L d5) (r2B L d5) (qB L d5)⟩

theorem B_sat : Sat (DA L d5 d6) (trB L d5 d6) where
  hq := by
    intro t; simp only [trB, DA, qB, r1B, r2B, stF_eq]; arbbin_omega
  hg1 := fun t => gOut_rel _ _ _ _ _ t
  hg2 := fun t => gOut_rel _ _ _ _ _ t

theorem B_init : H_INIT_SETTLED (DA L d5 d6) (trB L d5 d6) := by
  refine ⟨fun t ht => ?_, ?_⟩
  · simp only [trB, DA, r1B, r2B, qB] at *
    refine ⟨?_, ?_, ?_⟩ <;> arbbin_omega
  · simp only [trB, r1B, r2B, qB, stF_eq]; arbbin_omega

theorem B_sep : H_REQ_SEP (DA L d5 d6) (trB L d5 d6) := by
  intro i j hij hi hj
  simp only [redge, trB, r1B, r2B, DA, ne_eq] at *
  arbbin_omega

theorem formB_handover : qB L d5 0 = true ∧ qB L d5 ((d5 + L + 1) + 2 * L + 1) = false := by
  simp [qB]

theorem formB_overlap (h : d6 + L + 1 ≤ d5) :
    ((trB L d5 d6).g1 ((d5 + L + 1) + 2 * L + 1 + d6) &&
      (trB L d5 d6).g2 ((d5 + L + 1) + 2 * L + 1 + d6)) = true := by
  have e : (d5 + L + 1) + 2 * L + 1 + d6 = ((d5 + L + 1) + 2 * L + 1 + d6 - d5) + d5 := by
    omega
  show (gOut d5 gr1 _ _ _ ((d5 + L + 1) + 2 * L + 1 + d6) && gOut d6 gr2 _ _ _ _) = true
  rw [e, gOut_rel, ← e, gOut_rel, gr1_eq, gr2_eq]
  simp only [r1B, r2B, qB]
  arbbin_omega

theorem formB_run (h : d6 + L + 1 ≤ d5) : ¬ Excl (DA L d5 d6) := by
  intro hE
  have := hE _ (B_sat L d5 d6) (B_init L d5 d6) (B_sep L d5 d6) ((d5 + L + 1) + 2 * L + 1 + d6)
    (by simp only [DA]; omega) (by simp [DA])
  rw [formB_overlap L d5 d6 h] at this; exact absurd this (by decide)

end formB

/-! ## The iff -/

/-- **`bd_arbcell.grant_skew` is exact** in the transport model: exclusion for
every admissible trace holds iff `d6 ≤ d5 + L ∧ d5 ≤ d6 + L`. -/
theorem grant_skew_exact (D : Delays) (hL : 0 < D.L) : Excl D ↔ H_GRANT_SKEW D := by
  obtain ⟨L, d5, d6⟩ := D
  constructor
  · intro hE
    refine ⟨?_, ?_⟩
    · show d6 ≤ d5 + L
      rcases Nat.lt_or_ge (d5 + L) d6 with h | h
      · exact absurd hE (formA_run L d5 d6 (by omega))
      · exact h
    · show d5 ≤ d6 + L
      rcases Nat.lt_or_ge (d6 + L) d5 with h | h
      · exact absurd hE (formB_run L d5 d6 (by omega))
      · exact h
  · intro hSk tr hS hI hSep T h5 h6
    exact exclusion_transport hL hS hI hSep hSk T h5 h6

/-- Form A alone is exact (given form B). -/
theorem formA_iff (D : Delays) (hL : 0 < D.L) (hB : D.d5 ≤ D.d6 + D.L) :
    Excl D ↔ D.d6 ≤ D.d5 + D.L := by
  rw [grant_skew_exact D hL]; exact ⟨fun h => h.1, fun h => ⟨h, hB⟩⟩

/-- Form B alone is exact (given form A). -/
theorem formB_iff (D : Delays) (hL : 0 < D.L) (hA : D.d6 ≤ D.d5 + D.L) :
    Excl D ↔ D.d5 ≤ D.d6 + D.L := by
  rw [grant_skew_exact D hL]; exact ⟨fun h => h.2, fun h => ⟨hA, h⟩⟩

/-- Non-vacuity of the `←` side: a clean contended handover in which both
clients are served, meeting every hypothesis (`ArbBinary.ho_*`). -/
theorem nonvacuous : H_GRANT_SKEW runtD ∧ Sat runtD hoTrace ∧ H_INIT_SETTLED runtD hoTrace ∧
    H_REQ_SEP runtD hoTrace ∧ hoG1 11 = true ∧ hoG2 24 = true :=
  ⟨runt_skew, ho_sat, ho_init, ho_sep, ho_serves⟩

/-- Bsx3's point runs are instances: `(L, d5, d6) = (4, 1, 6)` and `(4, 6, 1)`. -/
theorem bsx3_points : ¬ Excl ⟨4, 1, 6⟩ ∧ ¬ Excl ⟨4, 6, 1⟩ :=
  ⟨formA_run 4 1 6 (by decide), formB_run 4 6 1 (by decide)⟩

/-! ## Settled exclusion: the exact structural condition -/

/-- With g1 reading `qa` and g2 reading `qb`, the grants exclude for every
request vector iff NOT (`qa = 1` and `qb = 0`). `qa = qb` (one q pin) is the
shipped `settled_exclusion`. -/
theorem settled_iff (qa qb : Bool) :
    (∀ r1 r2 : Bool, (gr1 r1 r2 qa && gr2 r1 r2 qb) = false) ↔ ¬ (qa = true ∧ qb = false) := by
  cases qa <;> cases qb <;> decide

/-- An overlap with split q also needs both requests up. -/
theorem settled_overlap_needs_both (r1 r2 qa qb : Bool)
    (h : (gr1 r1 r2 qa && gr2 r1 r2 qb) = true) : r1 = true ∧ r2 = true ∧ qa = true ∧ qb = false := by
  cases r1 <;> cases r2 <;> cases qa <;> cases qb <;> simp_all [gr1_eq, gr2_eq]

end Formal.Cells.Necessity5Arb
