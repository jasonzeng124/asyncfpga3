import Formal.Core.XAudit.Events9ArbNetEdge

/-!
# Formal.Core.XAudit.Events9ArbB1 — what a failing B1 row does and does not mean

Shard A, lead, 2026-10-31. Notes: `formal/notes/A-e9arbnet.md` (2026-10-31 section).

On the rebuilt gcd_hw routes the B1 row `hi Dr + 2 ≤ lo DrQ + lo Dq` of `ArbRowsOK` fails on 2-6
of 9 arbiters at slow/fast (xarbnet). B1 is what `b1_of` needs to show that the real grant
`y t = s (wr t) && e (wq t)` (an AND of its request read and its state-literal read) behaves as
the corrected core's grant, a C-element: with the request read high and the state literal lost,
the output must already have been low.

**Problem statement.** Without the B1 row, using only (i) the flip property of ustate O6 (a flip
of the literal away from the branch at `τ` happens only with ustate reading the request LOW at
`fQ τ`; proved from the real INIT in `flipAway1`/`flipAway2` under QClean) and (ii) no re-request
during the switch (`NoReReq` of `ArbEdge`), does the real grant still keep the four-phase order
"the grant falls only after its request has fallen"?

**Proved** (`grant_fall_after_req_fall`): at every fall of the grant (`y (t-1) = true`,
`y t = false`) at a time `t > lo Dr + lo Q + lo Dq`, there is a time `u` with `wr (t-1) < u` (after the grant's last high read of the
request), `s u = false` (the request is low), and `u + min lo Dr (lo Q + lo Dq) ≤ t`. So the
request has fallen, after the read that kept the grant high, at least `min(lo Dr, lo Q + lo Dq)`
before the grant falls, whether the fall came through the request pin or through the q pin.
The B1 row is not used. So a failing B1 row does not by itself break req↓ → grant↓; what it
breaks is the match with the C-element grant of the corrected core (`and_cel`'s hold clause).

NOT covered: exclusion, the rise side, what downstream readers of the grant need, and the
hypotheses themselves (QClean, NoReReq).
-/

namespace Formal.Core.XAudit.Events9ArbNet

open Formal.Core
open Formal.Core.TraceDiscrete (Sig Warp Mono)
open Formal.Core.XAudit
open Formal.Core.XAudit.Events2Pin (SatPin)
open Formal.Core.XAudit.Events5
open Formal.Core.XAudit.Events6
open Formal.Core.XAudit.Events8Arb
open Formal.Core.XAudit.Events9Arb
open Formal.Cells (o5B o6B)
open Formal.Cells.ArbBinary (ARB_ST GRANT)

theorem grant_fall_after_req_fall {s e y : Sig} {wr wq fQ : Nat → Nat}
    {loDr hiDr loDq hiDq loQ hiQ : Nat}
    (hy : ∀ t, y t = (s (wr t) && e (wq t)))
    (hwr : Warp loDr hiDr wr) (hwq : Warp loDq hiDq wq) (hfQ : Warp loQ hiQ fQ)
    (hflip : ∀ τ, 1 ≤ τ → e (τ - 1) = true → e τ = false → s (fQ τ) = false)
    (hnore : ∀ τ, 1 ≤ τ → e (τ - 1) = true → e τ = false →
      ∀ v, fQ τ ≤ v → v + loDr < τ + hiDq + 2 → s v = false) :
    ∀ t, loDr + loQ + loDq + 1 ≤ t → y (t - 1) = true → y t = false →
      ∃ u, wr (t - 1) < u ∧ s u = false ∧ u + min loDr (loQ + loDq) ≤ t := by
  intro t ht h1 h0
  rw [hy] at h1 h0
  have hs1 : s (wr (t - 1)) = true := by cases h : s (wr (t - 1)) <;> simp_all
  have he1 : e (wq (t - 1)) = true := by cases h : e (wq (t - 1)) <;> simp_all
  have a1 := hwr.le_late t
  cases hst : s (wr t)
  · -- the fall came through the request pin
    refine ⟨wr t, ?_, hst, by omega⟩
    have hm := hwr.mono (t - 1) t (by omega)
    rcases Nat.lt_or_eq_of_le hm with h | h
    · exact h
    · rw [h, hst] at hs1; exact absurd hs1 (by decide)
  · -- the fall came through the state literal
    have he0 : e (wq t) = false := by rw [hst] at h0; simpa using h0
    obtain ⟨τ, h2, h3, h4, h5⟩ := first_fall e he1 he0 (hwq.mono (t - 1) t (by omega))
    have hτ : 1 ≤ τ := by omega
    have hfl := hflip τ hτ h4 h5
    have b1 := hfQ.le_late τ
    have b2 := hwq.le_late t
    have b3 := hwq.early_le (t - 1)
    have b4 := hwr.le_late (t - 1)
    refine ⟨fQ τ, ?_, hfl, by omega⟩
    -- if ustate's low read came at or before the grant's high read, that is a re-request
    rcases Nat.lt_or_ge (wr (t - 1)) (fQ τ) with h | h
    · exact h
    · exfalso
      have := hnore τ hτ h4 h5 (wr (t - 1)) h (by omega)
      rw [hs1] at this; exact absurd this (by decide)

/-! ## B1 from a per-behaviour ordering (instead of the band row)

`b1_of` needs the BAND row `hi Dr + 2 ≤ lo Q + lo Dq`, i.e. the order for every choice of the
three delays inside their bands independently. `b1_of_ord` needs only the order on the behaviour
at hand (`HOrd`: ustate's request read at the grant's q-read time is no later than the grant's
request read two steps earlier). `ord_of_transport` and `corner_ord` give `HOrd` for fixed
(transport) path delays inside a corner model: delays within a factor `1 ± kn/kd` of nominals
`Pr, PQ, Pq` (a SHARED position inside each prjxray band) with `(kd+kn) Pr + 2 kd ≤ (kd-kn)(PQ+Pq)`.
That is the κ threshold xarbnet prints (`b1Kappa`, diagnostic). NOT covered: that the routed
design's delays obey this corner model (H_SPREAD_CORRELATED and the value of κ are hypotheses), and
the other ArbRowsOK conjuncts. -/

section
variable {s e y : Sig} {wr wq fQ : Nat → Nat} {loDr hiDr loDq hiDq T0 : Nat}

/-- **B1 from the behaviour's own read order.** -/
theorem b1_of_ord (hy : ∀ t, y t = (s (wr t) && e (wq t)))
    (hwr : Warp loDr hiDr wr) (hwq : Warp loDq hiDq wq) (hfQm : Mono fQ)
    (hT : hiDr + hiDq + 2 ≤ T0)
    (hord : ∀ t, T0 < t → fQ (wq t) ≤ wr (t - 2))
    (hflip : ∀ τ, T0 < τ + hiDq + 2 → 1 ≤ τ → e (τ - 1) = true → e τ = false → s (fQ τ) = false)
    (hnore : ∀ τ, 1 ≤ τ → e (τ - 1) = true → e τ = false →
      ∀ v, fQ τ ≤ v → v + loDr < τ + hiDq + 2 → s v = false) :
    ∀ t, T0 < t → s (wr t) = true → e (wq t) = false → y (t - 2) = false := by
  intro t ht hs he
  rw [hy]
  cases hs2 : s (wr (t - 2))
  · rfl
  · cases he2 : e (wq (t - 2))
    · rfl
    · exfalso
      obtain ⟨τ, h1, h2, h3, h4⟩ := first_fall e he2 he (hwq.mono _ _ (by omega))
      have a2 := hwq.le_late t
      have a3 := hwq.early_le (t - 2)
      have a5 := hwr.le_late (t - 2)
      have hq := hfQm τ (wq t) h2
      have l1 := warp_le hwr
      have ho := hord t ht
      have hfl := hflip τ (by omega) (by omega) h3 h4
      have := hnore τ (by omega) h3 h4 (wr (t - 2)) (by omega) (by omega)
      rw [hs2] at this; exact absurd this (by decide)

/-- The BAND row implies the order for every behaviour in the bands: so `ArbOrd` is a real
assumption only for readers whose band row fails. -/
theorem ord_of_row {loQ hiQ : Nat} (hwr : Warp loDr hiDr wr) (hwq : Warp loDq hiDq wq)
    (hfQ : Warp loQ hiQ fQ) (hT : hiDr + 2 ≤ T0) (hrow : hiDr + 2 ≤ loQ + loDq) :
    ∀ t, T0 < t → fQ (wq t) ≤ wr (t - 2) := by
  intro t ht
  have a := hfQ.le_late (wq t); have b := hwq.le_late t; have c := hwr.early_le (t - 2)
  omega

/-- Fixed path delays (transport, from `T0` on) give `HOrd` iff the delays are ordered. -/
theorem ord_of_transport {Dr DQ Dq : Nat} (hDr : ∀ t, wr t = t - Dr) (hDQ : ∀ t, fQ t = t - DQ)
    (hDq : ∀ t, wq t = t - Dq) (hle : Dr + 2 ≤ DQ + Dq) :
    ∀ t, T0 < t → fQ (wq t) ≤ wr (t - 2) := by
  intro t _; rw [hDr, hDQ, hDq]; omega

end

/-- **Corner-model sufficiency for the B1 order.** Delays within a factor `1 ± kn/kd` of shared
nominals (`kd·D` between `(kd−kn)·P` and `(kd+kn)·P`) with the κ-guarded nominal row give the
ordered delays `Dr + 2 ≤ DQ + Dq`. -/
theorem corner_ord {kn kd Pr PQ Pq Dr DQ Dq : Nat} (hkd : 0 < kd)
    (hr : kd * Dr ≤ (kd + kn) * Pr) (hQ : (kd - kn) * PQ ≤ kd * DQ) (hq : (kd - kn) * Pq ≤ kd * Dq)
    (hrow : (kd + kn) * Pr + 2 * kd ≤ (kd - kn) * (PQ + Pq)) : Dr + 2 ≤ DQ + Dq := by
  have e1 : (kd - kn) * (PQ + Pq) = (kd - kn) * PQ + (kd - kn) * Pq := Nat.mul_add _ _ _
  have e2 : kd * (Dr + 2) = kd * Dr + 2 * kd := by rw [Nat.mul_add, Nat.mul_comm kd 2]
  have e3 : kd * (DQ + Dq) = kd * DQ + kd * Dq := Nat.mul_add _ _ _
  have key : kd * (Dr + 2) ≤ kd * (DQ + Dq) := by
    rw [e2, e3]; rw [e1] at hrow
    generalize kd * Dr = a at *
    generalize kd * DQ = b at *
    generalize kd * Dq = c at *
    generalize (kd + kn) * Pr = x at *
    generalize (kd - kn) * PQ = y at *
    generalize (kd - kn) * Pq = z at *
    omega
  exact Nat.le_of_mul_le_mul_left key hkd

/-! ## The arbiter link with the read ORDER in place of the B1 band rows -/

section
variable {s e y : Sig} {wr wq fQ : Nat → Nat} {loDr hiDr loDq hiDq T0 : Nat}

/-- `rdOK_of` with `b1_of_ord` (behaviour order) instead of `b1_of` (band row). -/
theorem rdOK_of_ord {a q : Sig} {f4 : Nat → Nat} (hy : ∀ t, y t = (s (wr t) && e (wq t)))
    (hwr : Warp loDr hiDr wr) (hwq : Warp loDq hiDq wq) (hfQm : Mono fQ)
    (hT : hiDr + hiDq + 2 ≤ T0) (hord : ∀ t, T0 < t → fQ (wq t) ≤ wr (t - 2))
    (hflip : ∀ τ, T0 < τ + hiDq + 2 → 1 ≤ τ → e (τ - 1) = true → e τ = false → s (fQ τ) = false)
    (hnore : ∀ τ, 1 ≤ τ → e (τ - 1) = true → e τ = false →
      ∀ v, fQ τ ≤ v → v + loDr < τ + hiDq + 2 → s v = false)
    (hr : ∀ σ, 1 ≤ σ → s (σ - 1) = false → s σ = true →
      ∀ u, σ + loDr ≤ u + hiDq → u + loDq < σ + hiDr + 2 → e u = true → Settled a q f4 u)
    (hf : ∀ τ, 1 ≤ τ → e (τ - 1) = false → e τ = true →
      ∀ u, τ ≤ u → u + loDq < τ + hiDq + 2 → Settled a q f4 u)
    (hc : ∀ σ, 1 ≤ σ → s (σ - 1) = true → s σ = false →
      ∀ u, σ + loDr ≤ u + hiDq → u + loDq < σ + hiDr + 2 → a (f4 u) = true) :
    RdOK (Settled a q f4) s e y wr wq T0 := fun t ht =>
  ⟨b1_of_ord hy hwr hwq hfQm hT hord hflip hnore t ht, b2_of hy hwr hwq hT hr hf t ht,
    fun hs hst he => c_of (q := q) hy hwr hwq hT hc t ht hs hst he⟩

end

section
variable {N : Nat} (d : Design) (a : ArbD N)

/-- `ArbRowsOK` without its four B1 conjuncts: the start bounds and side conditions only (decidable). -/
def ArbRowsOKS (T T0 : Nat) : Prop :=
  let B := bandsOf d a
  (B.g1 0).2 + (B.g1 2).2 + 2 ≤ T0 ∧ (B.g2 1).2 + (B.g2 2).2 + 2 ≤ T0 ∧
  (B.r0 0).2 + (B.r0 2).2 + 2 ≤ T0 ∧ (B.r0 1).2 + (B.r0 2).2 + 2 ≤ T0 ∧
  T + phi d (PrQ a) + (B.g2 2).2 + 2 ≤ T0 ∧ T + phi d (PrQ a) + (B.r0 2).2 ≤ T0 ∧
  2 ≤ (B.r0 0).1 ∧ 2 ≤ (B.r0 1).1 ∧ 2 ≤ (B.r0 2).1

instance (T T0 : Nat) : Decidable (ArbRowsOKS d a T T0) := by unfold ArbRowsOKS; exact inferInstance

/-- `ArbRowsOK` is `ArbRowsOKS` plus the four B1 rows. -/
theorem rowsS_of_rows {T T0 : Nat} (h : ArbRowsOK d a T T0) : ArbRowsOKS d a T T0 := by
  obtain ⟨_, _, _, _, t1, t2, t3, t4, tr, tr', l0, l1, l2⟩ := h
  exact ⟨t1, t2, t3, t4, tr, tr', l0, l1, l2⟩

end

section
variable {N : Nat} {d : Design} {x : Fin d.n → Sig} (hsat : SatPin d plG x)

/-- **HOrd for the four readers of one arbiter** (a hypothesis on the behaviour's per-pin warps):
ustate's request read at the reader's q-read time is no later than the reader's request read two
steps earlier. `ord_of_transport` + `corner_ord` give it under fixed delays in a corner model. -/
structure ArbOrd (a : ArbD N) (T0 : Nat) : Prop where
  o1 : ∀ t, T0 < t → tau hsat (P1Q a) (f1Of hsat a 2 t) ≤ f1Of hsat a 0 (t - 2)
  o2 : ∀ t, T0 < t → tau hsat (P2Q a) (f2Of hsat a 2 t) ≤ f2Of hsat a 1 (t - 2)
  o3 : ∀ t, T0 < t → tau hsat (P1Q a) (frOf hsat a 2 (t + 2)) ≤ frOf hsat a 0 (t - 2 + 2)
  o4 : ∀ t, T0 < t → tau hsat (P2Q a) (frOf hsat a 2 (t + 2)) ≤ frOf hsat a 1 (t - 2 + 2)

end

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {fuel rw : Nat}
  {x : Fin d.n → Sig} (hsat : SatPin d plG x)
  (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
include h0 h1

/-- **`arbCond_of_ord`**: `arbCond_of_edge` with the four B1 band rows replaced by the behaviour's
read order `ArbOrd` (the start bounds stay checked, `ArbRowsOKS`). -/
theorem arbCond_of_ord {a : ArbD N} (hA : ArbOK d net b rn fuel rw a) {T T0 H : Nat}
    (hrst : ∀ t, x (d.wire rw) t = decide (t < T)) (hrows : ArbRowsOKS d a T T0)
    (he : ArbEdge hsat rn a T0 H) (ho : ArbOrd hsat a T0) : ArbCond hsat rn a T0 H := by
  obtain ⟨r11, r1q, s1, r22, r2q, s2, rR1, rR2, rRq, _sR, _hgQ, rQ1, rQ2, rQq, rQr, rQA, sQ, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hA
  obtain ⟨t1, t2, t3, t4, tr, tr', l0, l1, l2⟩ := hrows
  have wP : ∀ {gi i w : Nat} {p : Path}, RdP d fuel gi i p w → Warp (plo d ((gi, i) :: p)) (phi d ((gi, i) :: p))
      (tau hsat ((gi, i) :: p)) := fun h => tau_warp hsat _ h.2.2.1
  -- ustate O6's equation
  have hq : ∀ t, qS (x := x) a t = o6B ARB_ST [r1S (x := x) a (tau hsat (P1Q a) t), r2S (x := x) a (tau hsat (P2Q a) t),
      qS (x := x) a (tau hsat (PqQ a) t), x (d.wire rw) (tau hsat (PrQ a) t),
      aS (x := x) rn a (tau hsat (PA a) t), true] := by
    intro t
    rw [st_eq]
    show x (d.wire (gt d a.gQ).out) t = _
    rw [gate_spec hsat h0 h1 rQ1.1 sQ t]
    simp only
    rw [rdP_val hsat h0 h1 rQ1 t, rdP_val hsat h0 h1 rQ2 t, rdP_val hsat h0 h1 rQq t,
      rdP_val hsat h0 h1 rQr t, rdP_val hsat h0 h1 rQA t]
    rfl
  have hrs : ∀ τ, T + phi d (PrQ a) ≤ τ → x (d.wire rw) (tau hsat (PrQ a) τ) = false := by
    intro τ hτ
    rw [hrst]
    have := (wP rQr).early_le τ
    simp only [decide_eq_false_iff_not, Nat.not_lt]
    show T ≤ tau hsat ((a.gQ, a.irQ) :: a.prQ) τ
    simp only [PrQ] at hτ
    omega
  -- the reader equations
  have hg1 : ∀ t, g1S (x := x) a t = (r1S (x := x) a (f1Of hsat a 0 t) && qS (x := x) a (f1Of hsat a 2 t)) := by
    intro t
    unfold g1S
    rw [gate_spec hsat h0 h1 r11.1 s1 t]
    simp only
    rw [rdP_val hsat h0 h1 r11 t, rdP_val hsat h0 h1 r1q t]
    rfl
  have hg2 : ∀ t, g2S (x := x) a t = (r2S (x := x) a (f2Of hsat a 1 t) && !qS (x := x) a (f2Of hsat a 2 t)) := by
    intro t
    unfold g2S
    rw [gate_spec hsat h0 h1 r22.1 s2 t]
    simp only
    rw [rdP_val hsat h0 h1 r22 t, rdP_val hsat h0 h1 r2q t]
    rfl
  -- the flips
  have fl1 : ∀ τ, 1 ≤ τ → qS (x := x) a (τ - 1) = true → qS (x := x) a τ = false →
      r1S (x := x) a (tau hsat (P1Q a) τ) = false := fun τ h1' hp hn =>
    flipAway1 hq he.clean h1' hp hn
  have fl2 : ∀ τ, T + phi d (PrQ a) ≤ τ → 1 ≤ τ → (fun u => !qS (x := x) a u) (τ - 1) = true →
      (fun u => !qS (x := x) a u) τ = false → r2S (x := x) a (tau hsat (P2Q a) τ) = false := fun τ hτ h1' hp hn => by
    simp only [Bool.not_eq_true', Bool.not_eq_false'] at hp hn
    exact flipAway2 hq he.clean h1' (hrs τ hτ) hp hn
  -- the warps
  have wg10 : Warp ((bandsOf d a).g1 0).1 ((bandsOf d a).g1 0).2 (f1Of hsat a 0) := wP r11
  have wg12 : Warp ((bandsOf d a).g1 2).1 ((bandsOf d a).g1 2).2 (f1Of hsat a 2) := wP r1q
  have wg21 : Warp ((bandsOf d a).g2 1).1 ((bandsOf d a).g2 1).2 (f2Of hsat a 1) := wP r22
  have wg22 : Warp ((bandsOf d a).g2 2).1 ((bandsOf d a).g2 2).2 (f2Of hsat a 2) := wP r2q
  have wr0 : Warp ((bandsOf d a).r0 0).1 ((bandsOf d a).r0 0).2 (frOf hsat a 0) := wP rR1
  have wr1 : Warp ((bandsOf d a).r0 1).1 ((bandsOf d a).r0 1).2 (frOf hsat a 1) := wP rR2
  have wr2 : Warp ((bandsOf d a).r0 2).1 ((bandsOf d a).r0 2).2 (frOf hsat a 2) := wP rRq
  have wq1 : Warp (plo d (P1Q a)) (phi d (P1Q a)) (tau hsat (P1Q a)) := wP rQ1
  have wq2 : Warp (plo d (P2Q a)) (phi d (P2Q a)) (tau hsat (P2Q a)) := wP rQ2
  have lg12 := warp_le wg12
  have lg22 := warp_le wg22
  have lr2 := warp_le wr2
  refine ⟨he.low, by omega, by omega, by omega, he.stall, he.hi, ?_, ?_, ?_, ?_⟩
  · exact rdOK_of_ord hg1 wg10 wg12 wq1.mono t1 ho.o1 (fun τ _ h1' hp hn => fl1 τ h1' hp hn)
      he.e1.nore he.e1.rise he.e1.flip he.e1.fall
  · exact rdOK_of_ord hg2 wg21 wg22 wq2.mono t2 ho.o2 (fun τ hτ h1' hp hn => fl2 τ (by omega) h1' hp hn)
      he.e2.nore he.e2.rise he.e2.flip he.e2.fall
  · exact rdOK_of_ord (fun t => rfl) (sh2W wr0 l0) (sh2W wr2 l2) wq1.mono (by omega) ho.o3
      (fun τ _ h1' hp hn => fl1 τ h1' hp hn) he.e3.nore he.e3.rise he.e3.flip he.e3.fall
  · exact rdOK_of_ord (fun t => rfl) (sh2W wr1 l1) (sh2W wr2 l2) wq2.mono (by omega) ho.o4
      (fun τ hτ h1' hp hn => fl2 τ (by omega) h1' hp hn) he.e4.nore he.e4.rise he.e4.flip he.e4.fall


end

/-! ## ustate's INIT settles in one step -/

/-- **ustate O6 (the real `ARB_ST` INIT) is one-step stable**: for every value of its five other
inputs, feeding its own output back as the `q` input reproduces that output. So with all non-`q`
reads constant, `q` changes at most once and never oscillates; a violation of `QClean` (a `q` runt
shorter than its own loop) therefore needs one of ustate's other reads (requests, reset, A0) to
change within the loop delay of a `q` change. Kernel `decide` over 32 input vectors. This does not
derive `QClean`; it says which hypothesis it reduces to. -/
theorem st_stable : ∀ r1 r2 q rs a : Bool,
    o6B ARB_ST [r1, r2, o6B ARB_ST [r1, r2, q, rs, a, true], rs, a, true] =
      o6B ARB_ST [r1, r2, q, rs, a, true] := by decide

end Formal.Core.XAudit.Events9ArbNet
