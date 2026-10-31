import Formal.Core.XAudit.Events9FullArb

/-!
P15 audit (A): statement shapes / axioms of the ArbOrd / QQuiet verdicts (formal f40e003a), and a
check of what kind of hypothesis `ArbOrd` is.

`ArbOrd hsat a T0` is an inequality between the warps `tau hsat ...`, and those warps are
`Classical.choose` of the per-gate `PinRel` existentials (`Events6Gate.wf`). It does not mention
any signal value. Part 1 shows, for one AND-grant reader on an idle stretch (request, q and
ustate's read of the request all constant), with the same shape as `b1_of_ord`'s `hy` / `hord`:
* whenever the B1 band row fails (`loQ + loDq < hiDr + 2`), there are warps inside the bands that
  satisfy the gate equation and VIOLATE the order at every `t > T0` (`viol_*`);
* when the band row's hi-lo version allows it, other warps satisfying the same gate equation
  SATISFY the order (`sat_*`).
So the order is not fixed by the behaviour. "ArbOrd for the chosen witness" can be proved only by
proving it for every witness, which `not_all_witnesses` refutes for an idle behaviour at a
B1-failing reader.

Part 2: `b1_of_ord` with `hord` dropped is false (a counterexample that meets all the other
hypotheses).

Part 3: #check / #print axioms.
-/

open Formal.Core.TraceDiscrete (Sig Warp Mono)

namespace AuditP15A

theorem warpSub (k : Nat) : Warp k k (fun t => t - k) :=
  ⟨fun a b h => by omega, fun t => by omega, fun t => by omega⟩

theorem warpSubIn {lo hi k : Nat} (h1 : lo ≤ k) (h2 : k ≤ hi) : Warp lo hi (fun t => t - k) :=
  ⟨fun a b h => by omega, fun t => by omega, fun t => by omega⟩

/-! ## 1. On an idle stretch the order is a property of the chosen warp, not of the behaviour -/

/-- An idle grant: request, state literal and grant constantly high. -/
def sI : Sig := fun _ => true
def eI : Sig := fun _ => true
def yI : Sig := fun _ => true

/-- The grant equation holds for ANY pair of warps on the idle stretch. -/
theorem idle_hy (wr wq : Nat → Nat) : ∀ t, yI t = (sI (wr t) && eI (wq t)) := fun _ => rfl

/-- Violating witness: request read late (`hi Dr`), q read early (`lo Dq`), ustate's request read early
(`lo Q`). If the B1 band row fails, the order `fQ (wq t) ≤ wr (t - 2)` fails at every t ≥ T0 large. -/
theorem viol_order {loDr hiDr loDq hiDq loQ hiQ T0 : Nat} (hfail : loQ + loDq < hiDr + 2)
    (hb : loDr ≤ hiDr) (hb2 : loDq ≤ hiDq) (hT : hiDr + hiDq + loQ + 2 ≤ T0) :
    Warp loDr hiDr (fun t => t - hiDr) ∧ Warp loDq hiDq (fun t => t - loDq) ∧
    (loQ ≤ hiQ → Warp loQ hiQ (fun t => t - loQ)) ∧
    (∀ t, yI t = (sI ((fun t => t - hiDr) t) && eI ((fun t => t - loDq) t))) ∧
    ∀ t, T0 < t → ¬ ((fun t => t - loQ) ((fun t => t - loDq) t) ≤ (fun t => t - hiDr) (t - 2)) := by
  refine ⟨⟨fun a b h => by omega, fun t => by omega, fun t => by omega⟩, ?_, ?_, idle_hy _ _, ?_⟩
  · exact ⟨fun a b h => by omega, fun t => by omega, fun t => by omega⟩
  · intro h; exact ⟨fun a b h => by omega, fun t => by omega, fun t => by omega⟩
  · intro t ht; simp only; omega

/-- Satisfying witness for the same idle behaviour: request read early, q and ustate's read late. -/
theorem sat_order {loDr hiDr loDq hiDq loQ hiQ T0 : Nat} (hok : loDr + 2 ≤ hiQ + hiDq)
    (hb : loDr ≤ hiDr) (hb2 : loDq ≤ hiDq) :
    Warp loDr hiDr (fun t => t - loDr) ∧ Warp loDq hiDq (fun t => t - hiDq) ∧
    (loQ ≤ hiQ → Warp loQ hiQ (fun t => t - hiQ)) ∧
    (∀ t, yI t = (sI ((fun t => t - loDr) t) && eI ((fun t => t - hiDq) t))) ∧
    ∀ t, T0 < t → (fun t => t - hiQ) ((fun t => t - hiDq) t) ≤ (fun t => t - loDr) (t - 2) := by
  refine ⟨⟨fun a b h => by omega, fun t => by omega, fun t => by omega⟩, ?_, ?_, idle_hy _ _, ?_⟩
  · exact ⟨fun a b h => by omega, fun t => by omega, fun t => by omega⟩
  · intro h; exact ⟨fun a b h => by omega, fun t => by omega, fun t => by omega⟩
  · intro t _; simp only; omega

/-- "The order holds for every witness of the idle behaviour" is FALSE at a B1-failing reader. Since
`tau hsat` is an unspecified `Classical.choose`, this is what a proof of `ArbOrd` for a concrete
behaviour would have to show (for an idle stretch of that behaviour). -/
theorem not_all_witnesses {loDr hiDr loDq hiDq loQ hiQ T0 : Nat} (hfail : loQ + loDq < hiDr + 2)
    (hb : loDr ≤ hiDr) (hb2 : loDq ≤ hiDq) (hQ : loQ ≤ hiQ) (hT : hiDr + hiDq + loQ + 2 ≤ T0) :
    ¬ (∀ wr wq fQ : Nat → Nat, Warp loDr hiDr wr → Warp loDq hiDq wq → Warp loQ hiQ fQ →
        (∀ t, yI t = (sI (wr t) && eI (wq t))) → ∀ t, T0 < t → fQ (wq t) ≤ wr (t - 2)) := by
  intro h
  obtain ⟨w1, w2, w3, w4, w5⟩ := viol_order (loDr := loDr) (hiQ := hiQ) hfail hb hb2 hT
  exact w5 (T0 + 1) (by omega) (h _ _ _ w1 w2 (w3 hQ) w4 (T0 + 1) (by omega))

/-- Instance with the committed numbers of a B1-failing reader (xan_4_slow.txt, merge6.uarb1 g1, slow
bands): Dr1 g1 = (2898, 3477), Dq g1 = (342, 450), printed B1 margin -225 = lo(P1Q) + lo Dq - hi Dr - 2,
so lo(P1Q) = 2912 (hi(P1Q) is not printed; 3600 is a placeholder >= lo, irrelevant to the result). -/
theorem merge6_instance : ¬ (∀ wr wq fQ : Nat → Nat, Warp 2898 3477 wr → Warp 342 450 wq →
    Warp 2912 3600 fQ → (∀ t, yI t = (sI (wr t) && eI (wq t))) →
    ∀ t, 30000 < t → fQ (wq t) ≤ wr (t - 2)) :=
  not_all_witnesses (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ## 2. `b1_of_ord` without `hord` is false -/

/-- Counterexample data: request high on [2, 19) and again from 30, read by the grant with delay 5;
literal high on [0, 21), read with delay 1; ustate's request read fQ = t - 1. B1 row fails (5 + 2 > 1 + 1).
The literal falls at 21 with ustate reading the request low (hflip), the grant still reads the stale
high request at t = 23 while its literal read is low, and the grant was high at 21. -/
def cs : Sig := fun t => decide ((2 ≤ t ∧ t < 19) ∨ 30 ≤ t)
def ce : Sig := fun t => decide (t < 21)
def cy : Sig := fun t => cs (t - 5) && ce (t - 1)

/-- All hypotheses of `b1_of_ord` except `hord` hold (T0 = 8, hi Dr + hi Dq + 2 = 8), but the
conclusion fails at t = 23. -/
theorem b1_without_ord_false :
    (∀ t, cy t = (cs ((fun t => t - 5) t) && ce ((fun t => t - 1) t))) ∧
    Warp 5 5 (fun t => t - 5) ∧ Warp 1 1 (fun t => t - 1) ∧ Mono (fun t => t - 1) ∧
    5 + 1 + 2 ≤ 8 ∧
    (∀ τ, 8 < τ + 1 + 2 → 1 ≤ τ → ce (τ - 1) = true → ce τ = false → cs ((fun t => t - 1) τ) = false) ∧
    (∀ τ, 1 ≤ τ → ce (τ - 1) = true → ce τ = false →
      ∀ v, (fun t => t - 1) τ ≤ v → v + 5 < τ + 1 + 2 → cs v = false) ∧
    -- the conclusion of b1_of_ord fails at t = 23:
    (8 < 23 ∧ cs ((fun t => t - 5) 23) = true ∧ ce ((fun t => t - 1) 23) = false ∧ cy (23 - 2) = true) ∧
    -- and `hord` indeed fails there:
    ¬ ((fun t => t - 1) ((fun t => t - 1) 23) ≤ (fun t => t - 5) (23 - 2)) := by
  refine ⟨fun _ => rfl, warpSub 5, warpSub 1, fun a b h => by simp only; omega, by decide, ?_, ?_, by decide, by decide⟩
  · intro τ _ h1 h2 h3
    simp only [ce, decide_eq_true_eq, decide_eq_false_iff_not] at h2 h3
    have : τ = 21 := by omega
    subst this; decide
  · intro τ h1 h2 h3 v hv hv2
    simp only [ce, decide_eq_true_eq, decide_eq_false_iff_not] at h2 h3
    simp only at hv
    have : τ = 21 := by omega
    subst this
    exfalso; omega

/-! ## 3. Shapes and axioms -/

open Formal.Core.XAudit.Events9ArbNet in
#check @ArbOrd
open Formal.Core.XAudit.Events9ArbNet in
#check @QQuiet
open Formal.Core.XAudit.Events9ArbNet in
#check @ArbEdgeS

end AuditP15A

#print axioms AuditP15A.not_all_witnesses
#print axioms AuditP15A.merge6_instance
#print axioms AuditP15A.b1_without_ord_false
#print axioms Formal.Core.XAudit.Events9FullArb.design_verdict9arbnet_ord
#print axioms Formal.Core.XAudit.Events9FullArb.design_verdict9arbnet_ordq
#print axioms Formal.Core.XAudit.Events9FullArb.design_verdict9arbnet_ordS
#print axioms Formal.Core.XAudit.Events9ArbNet.arbCond_of_ord
#print axioms Formal.Core.XAudit.Events9ArbNet.arbCond_of_ordS
#print axioms Formal.Core.XAudit.Events9ArbNet.qclean_of_quiet
#print axioms Formal.Core.XAudit.Events9ArbNet.qclean_of_arb
#print axioms Formal.Core.XAudit.Events9ArbNet.qcleanFrom_of_quiet
#print axioms Formal.Core.XAudit.Events9ArbNet.cleanS_of_arb
#print axioms Formal.Core.XAudit.Events9ArbNet.b1_of_ord
#print axioms Formal.Core.XAudit.Events9ArbNet.ord_of_row
#print axioms Formal.Core.XAudit.Events9ArbNet.ord_of_transport
#print axioms Formal.Core.XAudit.Events9ArbNet.corner_ord
#print axioms Formal.Core.XAudit.Events9ArbNet.st_stable
