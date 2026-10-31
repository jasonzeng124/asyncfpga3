import Formal.Core.XAudit.Events9ArbB1

/-!
P14 audit (A): `Events9ArbNet.grant_fall_after_req_fall` (commit 330acc4a).

1. `w_*`: a concrete trace where the B1 row FAILS (hi Dr + 2 = 7 > lo Q + lo Dq = 2), the grant
   falls through its q pin while its own request pin still reads the request high, all the
   theorem's hypotheses hold, and the theorem's conclusion is obtained (non-vacuous, exercises the
   interesting q-pin branch). In the same trace the C-element hold clause (RdOK clause B1) FAILS,
   so the B1 row really is what separates the AND grant from the core's C-element grant.
2. `x_*`: dropping `hnore` (NoReReq) the conclusion fails: a re-request between ustate's low read
   and the grant's late fall.
-/

open Formal.Core.TraceDiscrete (Sig Warp Mono)

namespace AuditP14A

theorem warpSub (k : Nat) : Warp k k (fun t => t - k) :=
  ⟨fun a b h => by omega, fun t => by omega, fun t => by omega⟩

/-! ## 1. Witness: B1 row fails, q-pin fall, conclusion holds -/

def ws : Sig := fun t => decide (2 ≤ t ∧ t < 20)
def we : Sig := fun t => decide (t < 21)
def wy : Sig := fun t => ws (t - 5) && we (t - 1)

theorem w_hy : ∀ t, wy t = (ws ((fun t => t - 5) t) && we ((fun t => t - 1) t)) := fun _ => rfl

theorem w_flip : ∀ τ, 1 ≤ τ → we (τ - 1) = true → we τ = false → ws ((fun t => t - 1) τ) = false := by
  intro τ h1 h2 h3
  simp only [we, decide_eq_true_eq, decide_eq_false_iff_not] at h2 h3
  have : τ = 21 := by omega
  subst this; decide

theorem w_nore : ∀ τ, 1 ≤ τ → we (τ - 1) = true → we τ = false →
    ∀ v, (fun t => t - 1) τ ≤ v → v + 5 < τ + 1 + 2 → ws v = false := by
  intro τ h1 h2 h3 v hv hv2
  simp only [we, decide_eq_true_eq, decide_eq_false_iff_not] at h2 h3
  simp only at hv
  omega

/-- The B1 row of `ArbRowsOK` (`hi Dr + 2 ≤ lo Q + lo Dq`) fails in this instance. -/
theorem w_row_fails : ¬ (5 + 2 ≤ 1 + 1) := by decide

/-- The grant falls at t = 22 while its request pin reads high (fall through the q pin). -/
theorem w_fall : wy 21 = true ∧ wy 22 = false ∧ ws (22 - 5) = true := by decide

/-- Their theorem applies (no B1 row needed). -/
theorem w_concl : ∃ u, (fun t => t - 5) (22 - 1) < u ∧ ws u = false ∧ u + min 5 (1 + 1) ≤ 22 :=
  Formal.Core.XAudit.Events9ArbNet.grant_fall_after_req_fall (s := ws) (e := we) (y := wy)
    (hiDr := 5) (hiDq := 1) (hiQ := 1)
    w_hy (warpSub 5) (warpSub 1) (warpSub 1) w_flip w_nore 22 (by decide) (by decide) (by decide)

/-- The C-element hold clause (RdOK clause 1, what `b1_of` proves from the row) fails here:
request read high, literal read lost at t = 23, yet the grant was still high at t - 2 = 21. -/
theorem w_rdok_b1_fails : ws (23 - 5) = true ∧ we (23 - 1) = false ∧ wy (23 - 2) = true := by decide

/-! ## 2. Drop `hnore`: counterexample -/

def xs : Sig := fun t => decide ((2 ≤ t ∧ t < 10) ∨ 11 ≤ t)
def xe : Sig := fun t => decide (t < 15)
def xy : Sig := fun t => xs (t - 1) && xe (t - 1)

theorem x_hy : ∀ t, xy t = (xs ((fun t => t - 1) t) && xe ((fun t => t - 1) t)) := fun _ => rfl

theorem x_flip : ∀ τ, 1 ≤ τ → xe (τ - 1) = true → xe τ = false → xs ((fun t => t - 5) τ) = false := by
  intro τ h1 h2 h3
  simp only [xe, decide_eq_true_eq, decide_eq_false_iff_not] at h2 h3
  have : τ = 15 := by omega
  subst this; decide

/-- `hnore` fails (the request rises again at 11, inside the window [10, 17)). -/
theorem x_nore_fails : ¬ (∀ τ, 1 ≤ τ → xe (τ - 1) = true → xe τ = false →
    ∀ v, (fun t => t - 5) τ ≤ v → v + 1 < τ + 1 + 2 → xs v = false) := by
  intro h
  have := h 15 (by decide) (by decide) (by decide) 11 (by decide) (by decide)
  exact absurd this (by decide)

/-- Grant falls at 16 (t ≥ loDr + loQ + loDq + 1 = 8) and the conclusion fails. -/
theorem x_concl_fails : 1 + 5 + 1 + 1 ≤ 16 ∧ xy (16 - 1) = true ∧ xy 16 = false ∧
    ¬ ∃ u, (fun t => t - 1) (16 - 1) < u ∧ xs u = false ∧ u + min 1 (5 + 1) ≤ 16 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  rintro ⟨u, h1, h2, h3⟩
  simp only at h1
  have : u = 15 := by omega
  subst this; exact absurd h2 (by decide)

/-- Packaged: the theorem's statement without `hnore` is false. -/
theorem drop_nore_false : ¬ (∀ (s e y : Sig) (wr wq fQ : Nat → Nat) (loDr hiDr loDq hiDq loQ hiQ : Nat),
    (∀ t, y t = (s (wr t) && e (wq t))) → Warp loDr hiDr wr → Warp loDq hiDq wq → Warp loQ hiQ fQ →
    (∀ τ, 1 ≤ τ → e (τ - 1) = true → e τ = false → s (fQ τ) = false) →
    ∀ t, loDr + loQ + loDq + 1 ≤ t → y (t - 1) = true → y t = false →
      ∃ u, wr (t - 1) < u ∧ s u = false ∧ u + min loDr (loQ + loDq) ≤ t) := by
  intro h
  obtain ⟨_, _, _, _, hc⟩ := x_concl_fails
  exact hc (h xs xe xy _ _ _ 1 1 1 1 5 5 x_hy (warpSub 1) (warpSub 1) (warpSub 5) x_flip 16
    (by decide) (by decide) (by decide))

end AuditP14A

#print axioms AuditP14A.w_concl
#print axioms AuditP14A.drop_nore_false
#print axioms AuditP14A.w_rdok_b1_fails
