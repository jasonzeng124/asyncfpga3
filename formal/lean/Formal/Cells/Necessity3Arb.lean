import Formal.Cells.ArbBinary

/-!
# Necessity3Arb: `bd_arbcell.grant_skew` (H_GRANT_SKEW) is tight to 1 tick

Probe Bsx3 (shard B). Row `bd_arbcell.grant_skew` (`|d6 - d5| ≤ L`, two
forms) was "sufficient". Its theorem is `ArbBinary.exclusion_transport`:
transport model of `bd_arbcell` with the REAL INITs (state `bd_c2n_set`
`FFB2..`, rst = 0; grant LUT6_2 `0C0C_0C0C_A0A0_A0A0`, `O5 = g1`, `O6 = g2`),
constant loop delay `L ≥ 1`, grant arcs `d5`, `d6`, hypotheses
H_INIT_SETTLED, H_REQ_SEP (request edges more than `L` apart) and
H_GRANT_SKEW `d6 ≤ d5 + L ∧ d5 ≤ d6 + L`.

`SkewClaim sA sB` is that theorem with the first form weakened by `sA` and
the second by `sB`. `skew0 : SkewClaim 0 0` is the shipped theorem.
`formA_false : ¬ SkewClaim 1 0` and `formB_false : ¬ SkewClaim 0 1`.

Counter-runs (`L = 4`; every other hypothesis holds, the form is off by
exactly 1, `*_viol`). Both are OPPOSITE-sense handovers, which
`opposite_sense_exclusion` shows are clean under the skew bound:

* A (`d5 = 1`, `d6 = 6 = d5 + L + 1`): r2 is being served (q = 0); r1
  rises at 6, r2 falls at 11, edges 5 > L apart. q rises at 15. At
  `T = 16` g1 (O5) already reads the new q (15) while g2 (O6) still reads
  the instant 10, where r2 was high and q low: both grants high.
* B (`d6 = 1`, `d5 = 6`): the mirror (r1 served, r2 rises at 6, r1 falls
  at 11, q falls at 15): both grants high at 16.

At equality (`d6 = d5 + L`) the two outputs read q at instants `L` apart,
and a q edge is at least `L` after the request edge that caused it, which
is the slack the proof uses. So the Lean `≤` form is **necessary at the
boundary** (one parameter point per form). Binary model; no Kleene X.

Core Lean only.
-/

namespace Formal.Cells.Necessity3Arb
open Formal.Cells Formal.Cells.ArbBinary

/-- `exclusion_transport` with H_GRANT_SKEW's two forms weakened by `sA`, `sB`. -/
def SkewClaim (sA sB : Nat) : Prop :=
  ∀ (D : Delays) (tr : Trace), 0 < D.L → Sat D tr → H_INIT_SETTLED D tr → H_REQ_SEP D tr →
    (D.d6 ≤ D.d5 + D.L + sA ∧ D.d5 ≤ D.d6 + D.L + sB) →
    ∀ T, D.d5 ≤ T → D.d6 ≤ T → (tr.g1 T && tr.g2 T) = false

theorem skew0 : SkewClaim 0 0 := by
  intro D tr hL hS hI hSep hSk T h5 h6
  exact exclusion_transport hL hS hI hSep ⟨by have := hSk.1; omega, by have := hSk.2; omega⟩ T h5 h6

/-! ## Form A: `d6 = d5 + L + 1` -/

def DA : Delays := ⟨4, 1, 6⟩
def aR1 (t : Nat) : Bool := decide (6 ≤ t)
def aR2 (t : Nat) : Bool := decide (t ≤ 10)
def aQ (t : Nat) : Bool := decide (15 ≤ t)
def aG1 (t : Nat) : Bool := if t < 1 then false else gr1 (aR1 (t - 1)) (aR2 (t - 1)) (aQ (t - 1))
def aG2 (t : Nat) : Bool := if t < 6 then false else gr2 (aR1 (t - 6)) (aR2 (t - 6)) (aQ (t - 6))
def trA : Trace := ⟨aR1, aR2, aQ, aG1, aG2⟩

theorem A_sat : Sat DA trA where
  hq := by intro t; simp only [trA, DA, aQ, aR1, aR2, stF_eq]; arbbin_omega
  hg1 := by intro t; simp [trA, DA, aG1]
  hg2 := by intro t; simp [trA, DA, aG2]

theorem A_init : H_INIT_SETTLED DA trA := by
  refine ⟨fun t ht => ?_, rfl⟩
  simp only [trA, DA, aR1, aR2, aQ] at *
  refine ⟨?_, ?_, ?_⟩ <;> arbbin_omega

/-- Two request edges, at 5 (r1 rises) and 10 (r2 falls): 5 > L apart. -/
theorem A_sep : H_REQ_SEP DA trA := by
  intro i j hij hi hj
  simp only [redge, trA, aR1, aR2, DA, ne_eq] at *
  arbbin_omega

/-- Form A holds with slack 1 and fails by exactly 1 without it; form B holds. -/
theorem A_viol : DA.d6 = DA.d5 + DA.L + 1 ∧ DA.d5 ≤ DA.d6 + DA.L := by decide

/-- Both grants high at 16. -/
theorem A_overlap : (trA.g1 16 && trA.g2 16) = true := by decide

theorem formA_false : ¬ SkewClaim 1 0 := by
  intro h
  have := h DA trA (by decide) A_sat A_init A_sep ⟨by decide, by decide⟩ 16 (by decide) (by decide)
  rw [A_overlap] at this; exact absurd this (by decide)

/-! ## Form B: `d5 = d6 + L + 1` -/

def DB : Delays := ⟨4, 6, 1⟩
def bR1 (t : Nat) : Bool := decide (t ≤ 10)
def bR2 (t : Nat) : Bool := decide (6 ≤ t)
def bQ (t : Nat) : Bool := decide (t < 15)
def bG1 (t : Nat) : Bool := if t < 6 then false else gr1 (bR1 (t - 6)) (bR2 (t - 6)) (bQ (t - 6))
def bG2 (t : Nat) : Bool := if t < 1 then false else gr2 (bR1 (t - 1)) (bR2 (t - 1)) (bQ (t - 1))
def trB : Trace := ⟨bR1, bR2, bQ, bG1, bG2⟩

theorem B_sat : Sat DB trB where
  hq := by intro t; simp only [trB, DB, bQ, bR1, bR2, stF_eq]; arbbin_omega
  hg1 := by intro t; simp [trB, DB, bG1]
  hg2 := by intro t; simp [trB, DB, bG2]

theorem B_init : H_INIT_SETTLED DB trB := by
  refine ⟨fun t ht => ?_, rfl⟩
  simp only [trB, DB, bR1, bR2, bQ] at *
  refine ⟨?_, ?_, ?_⟩ <;> arbbin_omega

theorem B_sep : H_REQ_SEP DB trB := by
  intro i j hij hi hj
  simp only [redge, trB, bR1, bR2, DB, ne_eq] at *
  arbbin_omega

theorem B_viol : DB.d5 = DB.d6 + DB.L + 1 ∧ DB.d6 ≤ DB.d5 + DB.L := by decide

theorem B_overlap : (trB.g1 16 && trB.g2 16) = true := by decide

theorem formB_false : ¬ SkewClaim 0 1 := by
  intro h
  have := h DB trB (by decide) B_sat B_init B_sep ⟨by decide, by decide⟩ 16 (by decide) (by decide)
  rw [B_overlap] at this; exact absurd this (by decide)

/-! ## Non-vacuity at slack 0: `ArbBinary.ho_exclusion` (a clean contended
handover meeting every hypothesis, both clients served). -/

end Formal.Cells.Necessity3Arb
