import Formal.Core.XAudit.Events9FullArb

/-!
P18 audit (A): `Events9ArbB1.ArbEnv` and `Events9FullArb.design_verdict9arbnet_env` (formal 2f2e632d).

Part 1: statements and axioms (#check / #print).
Part 2 (`pt_of_fall`): the band C window (`RdEdge.fall`, in ArbEdge/ArbEdgeS) implies the pointwise C condition
  (`ArbEdgeSP.c1` shape) for any warps in the bands, so the pointwise form is a genuine weakening (the _ordSP / _env
  verdicts strictly generalize _ordS on this clause).
Part 3 (`c_needed`): at the reader level the pointwise clause cannot be dropped: a concrete AND-reader with a
  request fall, A0 read low and q constant (Settled) violates RdOK's C clause, and violates the pointwise clause.
Part 4 (`pt_is_C_clause`): the pointwise clause, restated: it is RdOK's C clause with `Settled` replaced by its
  first conjunct (A0 read low), i.e. close to the conclusion it is used for.
Part 5 (`env_of_idle`): ArbEnv is not self-contradictory: an arbiter whose requests are always low, q constant
  and A0 always high meets every field (given the arithmetic `hi`). The witness is vacuous: nothing computes.
-/

namespace AuditP18A

open Formal.Core
open Formal.Core.TraceDiscrete (Sig Warp Mono)
open Formal.Core.XAudit
open Formal.Core.XAudit.Events6
open Formal.Core.XAudit.Events9Arb
open Formal.Core.XAudit.Events9ArbNet

/-! ## Part 1 -/

#print Formal.Core.XAudit.Events9ArbNet.ArbEnv
#print Formal.Core.XAudit.Events9ArbNet.RdEdgeNF
#check @Formal.Core.XAudit.Events9FullArb.design_verdict9arbnet_env
#check @Formal.Core.XAudit.Events9ArbNet.arbEdgeSP_of_env
#check @Formal.Core.XAudit.Events9ArbNet.c_of_pt
#print axioms Formal.Core.XAudit.Events9FullArb.design_verdict9arbnet_env
#print axioms Formal.Core.XAudit.Events9FullArb.design_verdict9arbnet_ordSP
#print axioms Formal.Core.XAudit.Events9ArbNet.arbEdgeSP_of_env
#print axioms Formal.Core.XAudit.Events9ArbNet.arbCond_of_ordSP
#print axioms Formal.Core.XAudit.Events9ArbNet.c_of_pt

/-! ## Part 2: band window ⇒ pointwise -/

/-- A Bool signal that is true at `a` and false at `b > a` has a falling step in `(a, b]`. -/
theorem fall_between (s : Sig) : ∀ (k a : Nat), s a = true → s (a + k) = false →
    ∃ σ, a < σ ∧ σ ≤ a + k ∧ s (σ - 1) = true ∧ s σ = false := by
  intro k
  induction k with
  | zero => intro a ha hb; simp at hb; rw [ha] at hb; exact absurd hb (by decide)
  | succ k ih =>
    intro a ha hb
    cases h : s (a + k) with
    | false =>
      obtain ⟨σ, h1, h2, h3, h4⟩ := ih a ha h
      exact ⟨σ, h1, by omega, h3, h4⟩
    | true =>
      refine ⟨a + k + 1, by omega, by omega, ?_, ?_⟩
      · have : a + k + 1 - 1 = a + k := by omega
        rw [this]; exact h
      · have : a + k + 1 = a + (k + 1) := by omega
        rw [this]; exact hb

theorem pt_of_fall {s a : Sig} {wr wq f4 : Nat → Nat} {loDr hiDr loDq hiDq T0 : Nat}
    (hwr : Warp loDr hiDr wr) (hwq : Warp loDq hiDq wq) (hT : loDq ≤ T0)
    (hfall : ∀ σ, 1 ≤ σ → s (σ - 1) = true → s σ = false →
      ∀ u, σ + loDr ≤ u + hiDq → u + loDq < σ + hiDr + 2 → a (f4 u) = true) :
    ∀ t, T0 < t → s (wr (t - 2)) = true → s (wr t) = false → a (f4 (wq t)) = true := by
  intro t ht h2 h0
  have m := hwr.mono (t - 2) t (by omega)
  have hk : wr t = wr (t - 2) + (wr t - wr (t - 2)) := by omega
  rw [hk] at h0
  obtain ⟨σ, hσ1, hσ2, hσ3, hσ4⟩ := fall_between s _ _ h2 h0
  have l1 := hwr.le_late t
  have l2 := hwr.early_le (t - 2)
  have l3 := hwq.le_late t
  have l4 := hwq.early_le t
  exact hfall σ (by omega) hσ3 hσ4 (wq t) (by omega) (by omega)

/-! ## Part 3: the pointwise clause cannot be dropped (reader level) -/

/-- RdOK's C clause for an AND reader, alone. -/
def CClause (a q : Sig) (f4 : Nat → Nat) (s e y : Sig) (wr wq : Nat → Nat) (T0 : Nat) : Prop :=
  ∀ t, T0 < t → s (wr t) = false → Settled a q f4 (wq t) → e (wq t) = true → y (t - 2) = false

def sX : Sig := fun t => decide (t < 5)
def eX : Sig := fun _ => true
def aX : Sig := fun _ => false
def qX : Sig := fun _ => true

theorem c_needed :
    ¬ CClause aX qX id sX eX (fun t => sX t && eX t) id id 0 ∧
    ¬ (∀ t, 0 < t → sX (id (t - 2)) = true → sX (id t) = false → aX (id (id t)) = true) := by
  constructor
  · intro h
    have hs : Settled aX qX id (id 6) := ⟨rfl, fun _ _ _ => rfl⟩
    have := h 6 (by decide) (by decide) hs rfl
    exact absurd this (by decide)
  · intro h
    have := h 6 (by decide) (by decide) (by decide)
    exact absurd this (by decide)

/-! ## Part 4: what the pointwise clause says -/

/-- For an AND reader `y t = s (wr t) && e (wq t)`, RdOK's C clause is equivalent to: whenever the request read
fell in the last two steps, ustate time `wq t` is not (Settled with `e (wq t)` and `e (wq (t-2))`). The pointwise
clause (`hcp`) demands the stronger "A0 read high at `wq t`", which falsifies the first conjunct of Settled. -/
theorem pt_is_C_clause {a q s e : Sig} {f4 wr wq : Nat → Nat} {T0 : Nat} :
    CClause a q f4 s e (fun t => s (wr t) && e (wq t)) wr wq T0 ↔
    ∀ t, T0 < t → s (wr (t - 2)) = true → s (wr t) = false →
      ¬ (Settled a q f4 (wq t) ∧ e (wq t) = true ∧ e (wq (t - 2)) = true) := by
  constructor
  · intro h t ht h2 h0 ⟨hs, he, he2⟩
    have := h t ht h0 hs he
    simp only [h2, he2, Bool.and_self] at this
    exact absurd this (by decide)
  · intro h t ht h0 hs he
    show (s (wr (t - 2)) && e (wq (t - 2))) = false
    cases h2 : s (wr (t - 2)) with
    | false => rfl
    | true =>
      cases he2 : e (wq (t - 2)) with
      | false => rfl
      | true => exact absurd ⟨hs, he, he2⟩ (h t ht h2 h0)

theorem C_of_pt {a q s e : Sig} {f4 wr wq : Nat → Nat} {T0 : Nat}
    (hcp : ∀ t, T0 < t → s (wr (t - 2)) = true → s (wr t) = false → a (f4 (wq t)) = true) :
    CClause a q f4 s e (fun t => s (wr t) && e (wq t)) wr wq T0 := by
  rw [pt_is_C_clause]
  intro t ht h2 h0 ⟨hs, _, _⟩
  have := hcp t ht h2 h0
  rw [hs.1] at this
  exact absurd this (by decide)

/-! ## Part 5: ArbEnv is consistent (vacuous idle witness) -/

section
variable {N : Nat} {d : Design} {x : Fin d.n → Sig} (hsat : SatPinW d plG x) (rn : Fin N → RNode) (a : ArbD N)

theorem env_of_idle {T0 H : Nat}
    (hr1 : ∀ t, r1S (x := x) a t = false) (hr2 : ∀ t, r2S (x := x) a t = false)
    (hq : ∀ t, qS (x := x) a t = qS (x := x) a 0) (ha : ∀ t, aS (x := x) rn a t = true)
    (hH : H + kOf (bandsOf d a) + ((bandsOf d a).st 4).2 ≤ 10 ^ 15) :
    ArbEnv hsat rn a T0 H := by
  have flipq : ∀ τ, 1 ≤ τ → qS (x := x) a (τ - 1) = qS (x := x) a τ := fun τ _ => by rw [hq τ, hq (τ - 1)]
  refine ⟨fun t _ => ⟨hr1 _, hr2 _⟩, fun v => ⟨v, Nat.le_refl _, by omega, Or.inr (Or.inl (ha _))⟩, hH,
    ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (intro _ _ _ _ _ _ _; exact hr1 _)
    | (intro _ _ _ _ _ _ _; exact hr2 _)
    | (intro σ _ _ h; rw [hr1 σ] at h; exact absurd h (by decide))
    | (intro σ _ _ h; rw [hr2 σ] at h; exact absurd h (by decide))
    | (intro τ h1 hp hn; have := flipq τ h1; simp only [this] at hp; rw [hp] at hn; exact absurd hn (by decide))
    | (intro t _ h _; rw [hr1] at h; exact absurd h (by decide))
    | (intro t _ h _; rw [hr2] at h; exact absurd h (by decide))

end

#print axioms pt_of_fall
#print axioms c_needed
#print axioms pt_is_C_clause
#print axioms C_of_pt
#print axioms env_of_idle

end AuditP18A
