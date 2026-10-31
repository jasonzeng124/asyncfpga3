import Formal.Core.XAudit.Events9FullArb
import Formal.Core.XAudit.Events9ArbNetMain

/-!
P17 audit (A): is the P15a obstruction gone after SatPinW (formal 464c5ea7)?

P15a: `ArbOrd hsat a T0` was an inequality on `Classical.choose` warps, so at a B1-failing reader it
could not be proved for any behaviour with idle stretches (some admissible witness violates it).
Since 19195024 the verdicts take `hsat : SatPinW d plG x`, a structure whose field `f` IS the warp
family; `wf hsat = hsat.f`.

Part 1 (`arbOrd_congr`): ArbOrd depends on the supplied warp data `hsat.f` only.
Part 2 (`arbOrd_transport_iff`): for a SatPinW behaviour with fixed per-pin delays `D`, ArbOrd at an
arbiter HOLDS IFF the four path-delay rows hold (both directions; no `T0` side condition is needed,
the committed `arbOrd_of_transport` carries a superfluous `hT`: `arbOrd_of_rows`).
Part 3 (`pathD_lo`, `pathD_hi`, `warp_fixed`): a fixed delay at any point of the gate's band is an
admissible warp; at the all-lo / all-hi points `pathD` is `plo` / `phi`.
Part 4 (`b1Corr_*`): the committed xarbnet diagnostic `b1Corr`'s lo-end / hi-end entries are exactly
the margins of the four rows at the all-lo / all-hi fixed-delay behaviours.
Part 5: merge6.uarb1 g1 (xan_4_slow numbers): rows hold at all-lo and all-hi, fail at the mixed
fixed-delay point (request at hi, ustate paths at lo), so ArbOrd is decided by which fixed-delay
behaviour is supplied.
Part 6: #check / #print axioms.
-/

namespace AuditP17A

open Formal.Core
open Formal.Core.TraceDiscrete (Sig Warp Mono)
open Formal.Core.XAudit
open Formal.Core.XAudit.Events6
open Formal.Core.XAudit.Events9ArbNet

section
variable {N : Nat} {d : Design} {x : Fin d.n → Sig}

/-! ## Part 1 -/

theorem arbOrd_congr (h1 h2 : SatPinW d plG x) (hf : h1.f = h2.f) (a : ArbD N) (T0 : Nat) :
    ArbOrd h1 a T0 ↔ ArbOrd h2 a T0 := by
  cases h1; cases h2; cases hf; exact Iff.rfl

/-! ## Part 2 -/

/-- The four rows of `arbOrd_of_transport`, as one proposition. -/
def Rows (D : Nat → Nat → Nat) (a : ArbD N) : Prop :=
  pathD D (P1g1 a) + 2 ≤ pathD D (P1Q a) + pathD D (Pqg1 a) ∧
  pathD D (P2g2 a) + 2 ≤ pathD D (P2Q a) + pathD D (Pqg2 a) ∧
  pathD D (P1R a) + 2 ≤ pathD D (P1Q a) + pathD D (PqR a) ∧
  pathD D (P2R a) + 2 ≤ pathD D (P2Q a) + pathD D (PqR a)

/-- `arbOrd_of_transport` without its `hT` premise (it is not needed). -/
theorem arbOrd_of_rows (hsat : SatPinW d plG x) {D : Nat → Nat → Nat}
    (hD : ∀ gi i t, wf hsat gi i t = t - D gi i) (a : ArbD N) (T0 : Nat) (h : Rows D a) :
    ArbOrd hsat a T0 := by
  have tt := tau_transport hsat hD
  obtain ⟨r1, r2, r3, r4⟩ := h
  refine ⟨fun t _ => ?_, fun t _ => ?_, fun t _ => ?_, fun t _ => ?_⟩
  · show tau hsat (P1Q a) (tau hsat (Pqg1 a) t) ≤ tau hsat (P1g1 a) (t - 2)
    rw [tt, tt, tt]; omega
  · show tau hsat (P2Q a) (tau hsat (Pqg2 a) t) ≤ tau hsat (P2g2 a) (t - 2)
    rw [tt, tt, tt]; omega
  · show tau hsat (P1Q a) (tau hsat (PqR a) (t + 2)) ≤ tau hsat (P1R a) (t - 2 + 2)
    rw [tt, tt, tt]; omega
  · show tau hsat (P2Q a) (tau hsat (PqR a) (t + 2)) ≤ tau hsat (P2R a) (t - 2 + 2)
    rw [tt, tt, tt]; omega

/-- Converse: for a fixed-delay SatPinW behaviour, ArbOrd forces the four rows. -/
theorem rows_of_arbOrd (hsat : SatPinW d plG x) {D : Nat → Nat → Nat}
    (hD : ∀ gi i t, wf hsat gi i t = t - D gi i) (a : ArbD N) (T0 : Nat) (h : ArbOrd hsat a T0) :
    Rows D a := by
  have tt := tau_transport hsat hD
  -- a time after T0 far beyond every path delay: no truncation
  let t := T0 + 1 + pathD D (P1g1 a) + pathD D (P2g2 a) + pathD D (P1R a) + pathD D (P2R a) +
    pathD D (P1Q a) + pathD D (P2Q a) + pathD D (Pqg1 a) + pathD D (Pqg2 a) + pathD D (PqR a) + 4
  have ht : T0 < t := by omega
  have h1 : tau hsat (P1Q a) (tau hsat (Pqg1 a) t) ≤ tau hsat (P1g1 a) (t - 2) := h.o1 t ht
  have h2 : tau hsat (P2Q a) (tau hsat (Pqg2 a) t) ≤ tau hsat (P2g2 a) (t - 2) := h.o2 t ht
  have h3 : tau hsat (P1Q a) (tau hsat (PqR a) (t + 2)) ≤ tau hsat (P1R a) (t - 2 + 2) := h.o3 t ht
  have h4 : tau hsat (P2Q a) (tau hsat (PqR a) (t + 2)) ≤ tau hsat (P2R a) (t - 2 + 2) := h.o4 t ht
  rw [tt, tt, tt] at h1 h2 h3 h4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem arbOrd_transport_iff (hsat : SatPinW d plG x) {D : Nat → Nat → Nat}
    (hD : ∀ gi i t, wf hsat gi i t = t - D gi i) (a : ArbD N) (T0 : Nat) :
    ArbOrd hsat a T0 ↔ Rows D a :=
  ⟨rows_of_arbOrd hsat hD a T0, arbOrd_of_rows hsat hD a T0⟩

end

/-! ## Part 3 -/

/-- A fixed delay at any point of a band is an admissible warp of that band. -/
theorem warp_fixed {lo hi D : Nat} (h1 : lo ≤ D) (h2 : D ≤ hi) : Warp lo hi (fun t => t - D) :=
  ⟨fun a b h => by omega, fun t => by omega, fun t => by omega⟩

theorem pathD_lo (d : Design) : ∀ P : Path, pathD (fun gi _ => (gt d gi).lo) P = plo d P
  | [] => rfl
  | (gi, i) :: r => by simp only [pathD, plo, pathD_lo d r]

theorem pathD_hi (d : Design) : ∀ P : Path, pathD (fun gi _ => (gt d gi).hi) P = phi d P
  | [] => rfl
  | (gi, i) :: r => by simp only [pathD, phi, pathD_hi d r]

/-- At the all-lo fixed-delay behaviour, ArbOrd iff the four rows in `plo` form. -/
theorem arbOrd_lo_iff {N : Nat} {d : Design} {x : Fin d.n → Sig} (hsat : SatPinW d plG x)
    (hD : ∀ gi i t, wf hsat gi i t = t - (gt d gi).lo) (a : ArbD N) (T0 : Nat) :
    ArbOrd hsat a T0 ↔
      (plo d (P1g1 a) + 2 ≤ plo d (P1Q a) + plo d (Pqg1 a) ∧
       plo d (P2g2 a) + 2 ≤ plo d (P2Q a) + plo d (Pqg2 a) ∧
       plo d (P1R a) + 2 ≤ plo d (P1Q a) + plo d (PqR a) ∧
       plo d (P2R a) + 2 ≤ plo d (P2Q a) + plo d (PqR a)) := by
  rw [arbOrd_transport_iff hsat (D := fun gi _ => (gt d gi).lo) hD a T0]
  simp only [Rows, pathD_lo]

theorem arbOrd_hi_iff {N : Nat} {d : Design} {x : Fin d.n → Sig} (hsat : SatPinW d plG x)
    (hD : ∀ gi i t, wf hsat gi i t = t - (gt d gi).hi) (a : ArbD N) (T0 : Nat) :
    ArbOrd hsat a T0 ↔
      (phi d (P1g1 a) + 2 ≤ phi d (P1Q a) + phi d (Pqg1 a) ∧
       phi d (P2g2 a) + 2 ≤ phi d (P2Q a) + phi d (Pqg2 a) ∧
       phi d (P1R a) + 2 ≤ phi d (P1Q a) + phi d (PqR a) ∧
       phi d (P2R a) + 2 ≤ phi d (P2Q a) + phi d (PqR a)) := by
  rw [arbOrd_transport_iff hsat (D := fun gi _ => (gt d gi).hi) hD a T0]
  simp only [Rows, pathD_hi]

/-! ## Part 4: the committed b1Corr diagnostic computes these rows -/

open Formal.Core.XAudit.Events9ArbNetMain in
theorem b1Corr_eq {N : Nat} (d : Design) (a : ArbD N) :
    b1Corr d a =
      [("g1", ((plo d (P1Q a) : Int) + plo d (Pqg1 a) - plo d (P1g1 a) - 2,
               (phi d (P1Q a) : Int) + phi d (Pqg1 a) - phi d (P1g1 a) - 2)),
       ("g2", ((plo d (P2Q a) : Int) + plo d (Pqg2 a) - plo d (P2g2 a) - 2,
               (phi d (P2Q a) : Int) + phi d (Pqg2 a) - phi d (P2g2 a) - 2)),
       ("s1", ((plo d (P1Q a) : Int) + ((plo d (PqR a) - 2 : Nat) : Int) - ((plo d (P1R a) - 2 : Nat) : Int) - 2,
               (phi d (P1Q a) : Int) + ((phi d (PqR a) - 2 : Nat) : Int) - ((phi d (P1R a) - 2 : Nat) : Int) - 2)),
       ("s2", ((plo d (P2Q a) : Int) + ((plo d (PqR a) - 2 : Nat) : Int) - ((plo d (P2R a) - 2 : Nat) : Int) - 2,
               (phi d (P2Q a) : Int) + ((phi d (PqR a) - 2 : Nat) : Int) - ((phi d (P2R a) - 2 : Nat) : Int) - 2))] := by
  rfl

/-- The s1 entry is row r3's margin once the R0 paths have lower delay ≥ 2 (an `ArbRowsOKS`
conjunct, checked by xarbnet). -/
theorem s_entry_iff (Q qR rR : Nat) (h1 : 2 ≤ qR) (h2 : 2 ≤ rR) :
    (0 : Int) ≤ (Q : Int) + ((qR - 2 : Nat) : Int) - ((rR - 2 : Nat) : Int) - 2 ↔ rR + 2 ≤ Q + qR := by
  omega

theorem g_entry_iff (Q q r : Nat) : (0 : Int) ≤ (Q : Int) + q - r - 2 ↔ r + 2 ≤ Q + q := by
  omega

/-! ## Part 5: merge6.uarb1 g1, seed 4 slow (xan_4_slow: Dr1 g1 (2898, 3477), Dq g1 (342, 450),
P1Q band (2912, 3459): lo(P1Q) = 2912 from the printed lo-to-lo margin 356 and B1 margin -225;
hi(P1Q) = 3459 from the printed hi-end margin 430). Row r1 at three fixed-delay points. -/

-- all at lo: holds (margin 354 = the printed b1Corr lo-end entry)
example : 2898 + 2 ≤ 2912 + 342 ∧ (2912 : Int) + 342 - 2898 - 2 = 354 := by decide
-- all at hi: holds (margin 430 = the printed b1Corr hi-end entry)
example : 3477 + 2 ≤ 3459 + 450 ∧ (3459 : Int) + 450 - 3477 - 2 = 430 := by decide
-- request path at hi, ustate's request path and the q path at lo: fails (the B1 band row, -225)
example : ¬ (3477 + 2 ≤ 2912 + 342) ∧ (2912 : Int) + 342 - 3477 - 2 = -225 := by decide

/-! ## Part 6 -/

#check @SatPinW
#check @ArbOrd
#check @Formal.Core.XAudit.Events9ArbNet.arbOrd_of_transport
#check @Formal.Core.XAudit.Events9ArbNet.arb_low_of_reqlow
#print axioms arbOrd_congr
#print axioms arbOrd_transport_iff
#print axioms arbOrd_lo_iff
#print axioms arbOrd_hi_iff
#print axioms b1Corr_eq
#print axioms Formal.Core.XAudit.Events9ArbNet.arbOrd_of_transport
#print axioms Formal.Core.XAudit.Events9ArbNet.arb_low_of_reqlow
#print axioms Formal.Core.XAudit.Events9FullArb.design_verdict9arbnet_ord
#print axioms Formal.Core.XAudit.Events9FullArb.design_verdict9arbnet_ordq
#print axioms Formal.Core.XAudit.Events9FullArb.design_verdict9arbnet_ordS
#print axioms Formal.Core.XAudit.Events9FullArb.design_verdict9_full_arb
#print axioms Formal.Core.XAudit.Events9FullArb.design_verdict9arbnet_edge

end AuditP17A
