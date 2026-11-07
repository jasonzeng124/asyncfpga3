import Formal.Cells.CertRaceAll

/-!
# Formal.Cells.ArbServer — the arbiter state settles before the server can answer (H_ARB(T), every behaviour)

Shard B, 2026-11-07. The server-path obligation that H_ARB(T) leaves open (`ArbTSpec.spec_double_ack`: with only
H_ARB(T), the server's A0 may act while the arbiter state q is still moving, and both clients get acknowledged).

## Problem, plainly
After the arbiter's state q starts to move, how long until A0 (the state LUT's hold input, driven by the server's
response) can change? If that is longer than the H_ARB settling time T, q has settled before A0 moves, which is what
the one-acknowledge argument (`GrantExcl`, `AckLow`) needs.

## Proved (standard axioms)
* `arbCertOK`: a chain certificate whose cause is q and whose last row is the copy gate driving one of the state
  LUT's inputs (`A.ins`: the A0 pin node).
* `q_settles`: with H_ARB(T) (`ArbOK T [A] x`), the certificate's premises (q unchanged on `[a, e]`), the state's
  other inputs constant on `[t1, t2]`, `t1` after the certificate's last window start and `t2 ≤ e + psum`: q is
  constant on `[t1 + T, t2]`. Reading: if q's first move after `t1` is at `e + 1 ≥ t1`, the A0 pin cannot change
  before `e + psum ≥ t1 + psum`, so whenever `T < psum` the state settles before the server's answer reaches it.
* `target_arbs_settle_of`: every row of a checked list, one corner, every behaviour of THE circuit.

## Not shown
The premises (order-level); the grants/acks assembly into one acknowledge per transaction; the four arbiters without
a post-reset chain certificate in the runs used.
-/

namespace Formal.Cells.ArbServer
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecChain Formal.Cells.CertPS Formal.Cells.RaceCertPS
  Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll

def arbCertOK (A : ArbNodes) (pc : Prem × List CRow) : Bool :=
  singlePath pc.2 && chainShape pc.2 && decide (1 ≤ pc.2.length) && pc.1.cn == A.q &&
  A.ins.contains (pc.2.getD (pc.2.length - 1) default).r.q

/-- **The arbiter state settles before the server's answer reaches it.** -/
theorem q_settles {p : DelayPar} {c : ℚ} {x : Beh} (hb : Behaves p (circuit net boundary) x) {T : Nat}
    {A : ArbNodes} (harb : ArbOK T [A] x) (pc : Prem × List CRow) (hc : certOK pc.1 pc.2 = true)
    (ha : arbCertOK A pc = true)
    (G : ∀ i, i < pc.2.length → CGateOK p c (pc.2.getD i default).r.g (pc.2.getD i default).r.src
      (pc.2.getD i default).r.arcs ((pc.2.getD i default).r.S p) x)
    (a e : Nat) (E : Nat → Nat) (PS : Nat)
    (hcause : ∀ t, a ≤ t → t ≤ e → x pc.1.cn t = pc.1.cv)
    (hstat : ∀ k, k < pc.1.sn.length → ∀ t, a ≤ t → t ≤ E k → x (pc.1.sn.getD k 0) t = pc.1.sv.getD k false)
    (hmem : ∀ i, i < pc.2.length → (pc.2.getD i default).r.mem = true →
      1 ≤ (pc.2.getD i default).r.lo p c (pc.2.getD i default).r.fb ∧
      ∀ t, (win p c a e E pc.2 i).1 ≤ t + (pc.2.getD i default).r.hi p c (pc.2.getD i default).r.fb →
        t < (win p c a e E pc.2 i).1 → x (pc.2.getD i default).r.q t = (pc.2.getD i default).r.w)
    (hPS : ∀ i, i < pc.2.length → psum p c pc.2 i ≤ PS) (hE : ∀ k, e + PS ≤ E k) (hB : e + PS ≤ BIG)
    {t1 t2 : Nat} (hothers : ∀ n ∈ A.ins, n ≠ (pc.2.getD (pc.2.length - 1) default).r.q → ConstOn (x n) t1 t2)
    (h1 : (win p c a e E pc.2 (pc.2.length - 1)).1 ≤ t1) (h2 : t2 ≤ e + psum p c pc.2 (pc.2.length - 1)) :
    ConstOn (x A.q) (t1 + T) t2 := by
  simp only [arbCertOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.contains_iff_mem] at ha
  obtain ⟨⟨⟨⟨hsp, hch⟩, hn⟩, hq⟩, -⟩ := ha
  have hw := win_end_ge (p := p) (c := c) pc.1 pc.2 hc hsp a e E PS hPS hE hB (pc.2.length - 1) (by omega)
  have hhold := cert_sound hb pc.1 pc.2 hc G a e E hcause hstat hmem (pc.2.length - 1) (by omega)
  refine harb A (List.mem_singleton.mpr rfl) t1 t2 (fun n hn' => ?_)
  by_cases hna : n = (pc.2.getD (pc.2.length - 1) default).r.q
  · subst hna
    intro t u1 u2
    rw [hhold t (by omega) (by omega), hhold t1 (by omega) (by omega)]
  · exact hothers n hn' hna

/-- An arbiter row: the arbiter's nodes and its certificate. -/
structure ARowS where
  A : ArbNodes
  pc : Prem × List CRow

/-- **Every checked arbiter row, in every behaviour of THE circuit** (one corner): with H_ARB(T) for THE target's
arbiter list, each row's state settles on `[t1 + T, t2]` under the row's premises. -/
theorem target_arbs_settle_of (L : List ARowS)
    (hL : ∀ r ∈ L, r.A ∈ arbs ∧ certOK r.pc.1 r.pc.2 = true ∧ arbCertOK r.A r.pc = true)
    {p : DelayPar} (hp : Formal.Timing.SpecSettle.Sane p) {x : Beh} (hb : Behaves p (circuit net boundary) x)
    {T : Nat} (harb : ArbOK T arbs x) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ r ∈ L, ∀ (a e : Nat) (E : Nat → Nat) (PS t1 t2 : Nat),
      (∀ t, a ≤ t → t ≤ e → x r.pc.1.cn t = r.pc.1.cv) →
      (∀ k, k < r.pc.1.sn.length → ∀ t, a ≤ t → t ≤ E k → x (r.pc.1.sn.getD k 0) t = r.pc.1.sv.getD k false) →
      (∀ i, i < r.pc.2.length → (r.pc.2.getD i default).r.mem = true →
        1 ≤ (r.pc.2.getD i default).r.lo p c (r.pc.2.getD i default).r.fb ∧
        ∀ t, (win p c a e E r.pc.2 i).1 ≤ t + (r.pc.2.getD i default).r.hi p c (r.pc.2.getD i default).r.fb →
          t < (win p c a e E r.pc.2 i).1 → x (r.pc.2.getD i default).r.q t = (r.pc.2.getD i default).r.w) →
      (∀ i, i < r.pc.2.length → psum p c r.pc.2 i ≤ PS) → (∀ k, e + PS ≤ E k) → e + PS ≤ BIG →
      (∀ n ∈ r.A.ins, n ≠ (r.pc.2.getD (r.pc.2.length - 1) default).r.q → ConstOn (x n) t1 t2) →
      (win p c a e E r.pc.2 (r.pc.2.length - 1)).1 ≤ t1 → t2 ≤ e + psum p c r.pc.2 (r.pc.2.length - 1) →
      ConstOn (x r.A.q) (t1 + T) t2 := by
  obtain ⟨c, hc0, hc1, hcol⟩ := Formal.Cells.ViewPS.view_collapse hp hb
    (L.flatMap fun r => (List.range r.pc.2.length).map fun i =>
      ((r.pc.2.getD i default).r.q, (r.pc.2.getD i default).r.pins)) (by
      simp only [List.all_eq_true, List.mem_flatMap, List.mem_map, List.mem_range]
      rintro e ⟨r, hr, i, hi, rfl⟩
      have hc := (hL r hr).2.1
      simp only [certOK, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hc
      exact (krow_facts hb (hc i hi).1).2.2.2.2.2)
  refine ⟨c, hc0, hc1, fun r hr a e E PS t1 t2 h1 h2 h3 h4 h5 h6 h7 h8 h9 => ?_⟩
  obtain ⟨hA, hc, ha⟩ := hL r hr
  have harb1 : ArbOK T [r.A] x := fun A' hA' => harb A' (by rw [List.mem_singleton.mp hA']; exact hA)
  exact q_settles hb harb1 r.pc hc ha
    (fun i hi => hcol _ (List.mem_flatMap.mpr ⟨r, hr, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩⟩))
    a e E PS h1 h2 h3 h4 h5 h6 h7 h8 h9

end Formal.Cells.ArbServer
