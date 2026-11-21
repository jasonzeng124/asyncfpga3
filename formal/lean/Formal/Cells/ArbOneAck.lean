import Formal.Cells.ArbServer
import Formal.Cells.CertSwitchAll

/-!
# Formal.Cells.ArbOneAck — the losing client is not acknowledged (generic; every behaviour, H_ARB(T))

Shard B, 2026-11-07. The proof of `ArbOneAckPS.target_arb0_one_ack`, for any arbiter row: a server-path certificate
`pc` (cause q, ending at the A0 pin node; its row `len-2` is A0's source), the losing acknowledge's two holds
(`kA`: held by A0 low and reset low with its feedback; `kG`: held by its grant low and reset low with its feedback),
and the losing grant's hold (`kGr`: held low by q at the winner's value). `oneAckOK` checks the wiring (Boolean).

`one_ack`: with the certificate's premises, the state's other inputs constant on [t1, t2] (t2 ≤ e + psum), q at the
winner's value at t1 + T, the reset low, the acknowledge at its value on its feedback window before s0, and the
overlap condition (T small enough), the losing acknowledge keeps its (low) value on [s0, t2 + lo + lo].
-/

namespace Formal.Cells.ArbOneAck
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecChain Formal.Cells.CertPS Formal.Cells.RaceCertPS
  Formal.Cells.CertMarginPS Formal.Cells.ArbServer Formal.Cells.SpecFbChain Formal.Cells.SpecCElemFact

structure OneAckRow where
  A : ArbNodes
  pc : Prem × List CRow
  kA : KRow
  kG : KRow
  kGr : KRow
  ja0 : Nat
  jrst : Nat
  jg : Nat
  jq : Nat

def oneAckOK (r : OneAckRow) : Bool :=
  krowOK r.kA && krowOK r.kG && krowOK r.kGr &&
  r.kA.P == [r.ja0, r.jrst] && r.kG.P == [r.jg, r.jrst] && r.kGr.P == [r.jq] &&
  r.kA.mem && r.kG.mem && !r.kGr.mem && r.kA.q == r.kG.q && r.kA.pins == r.kG.pins && r.kA.fb == r.kG.fb &&
  r.kA.w == r.kG.w && decide (2 ≤ r.pc.2.length) &&
  (r.kA.pins.getD r.ja0 ([], 0)).2 == (r.pc.2.getD (r.pc.2.length - 2) default).r.q &&
  fl r.kA.bv r.ja0 == (r.pc.2.getD (r.pc.2.length - 2) default).r.w &&
  (r.kA.pins.getD r.jrst ([], 0)).2 == 186905 && fl r.kA.bv r.jrst == false && fl r.kG.bv r.jrst == false &&
  (r.kG.pins.getD r.jg ([], 0)).2 == r.kGr.q && fl r.kG.bv r.jg == r.kGr.w &&
  (r.kGr.pins.getD r.jq ([], 0)).2 == r.A.q

theorem src_of {k : KRow} (h : krowOK k = true) {j : Nat} (hj : j ∈ k.P) : k.src j = (k.pins.getD j ([], 0)).2 := by
  simp only [krowOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hk, -⟩, -⟩, hP⟩, -⟩, -⟩, -⟩ := h
  exact ksrc_eq k (by have := hP j hj; omega)

/-- **The losing client is not acknowledged** (generic arbiter row, at a corner with the collapsed relations). -/
theorem one_ack {r : OneAckRow} (hok : oneAckOK r = true) (hc : certOK r.pc.1 r.pc.2 = true)
    (ha : arbCertOK r.A r.pc = true) (hA : r.A ∈ arbs) {p : DelayPar} {c : ℚ} {x : Beh}
    (hb : Behaves p (circuit net boundary) x) {T : Nat} (harb : ArbOK T arbs x)
    (G : ∀ i, i < r.pc.2.length → CGateOK p c (r.pc.2.getD i default).r.g (r.pc.2.getD i default).r.src
      (r.pc.2.getD i default).r.arcs ((r.pc.2.getD i default).r.S p) x)
    (GA : CGateOK p c r.kA.g r.kA.src r.kA.arcs (r.kA.S p) x)
    (GGr : CGateOK p c r.kGr.g r.kGr.src r.kGr.arcs (r.kGr.S p) x)
    (a e : Nat) (E : Nat → Nat) (PS t1 t2 s0 ar : Nat)
    (hcause : ∀ t, a ≤ t → t ≤ e → x r.pc.1.cn t = r.pc.1.cv)
    (hstat : ∀ k, k < r.pc.1.sn.length → ∀ t, a ≤ t → t ≤ E k → x (r.pc.1.sn.getD k 0) t = r.pc.1.sv.getD k false)
    (hmem : ∀ i, i < r.pc.2.length → (r.pc.2.getD i default).r.mem = true →
      1 ≤ (r.pc.2.getD i default).r.lo p c (r.pc.2.getD i default).r.fb ∧
      ∀ t, (win p c a e E r.pc.2 i).1 ≤ t + (r.pc.2.getD i default).r.hi p c (r.pc.2.getD i default).r.fb →
        t < (win p c a e E r.pc.2 i).1 → x (r.pc.2.getD i default).r.q t = (r.pc.2.getD i default).r.w)
    (hPS : ∀ i, i < r.pc.2.length → psum p c r.pc.2 i ≤ PS) (hE : ∀ k, e + PS ≤ E k) (hB : e + PS ≤ BIG)
    (hoth : ∀ n ∈ r.A.ins, n ≠ (r.pc.2.getD (r.pc.2.length - 1) default).r.q → ConstOn (x n) t1 t2)
    (h1 : (win p c a e E r.pc.2 (r.pc.2.length - 1)).1 ≤ t1) (h2 : t2 ≤ e + psum p c r.pc.2 (r.pc.2.length - 1))
    (hq0 : x r.A.q (t1 + T) = fl r.kGr.bv r.jq)
    (hrst : ∀ t, ar ≤ t → x 186905 t = false)
    (hS0 : r.kA.S p ≤ s0) (hrs0 : ar + r.kA.hi p c r.jrst ≤ s0)
    (hpre1 : ∀ t, s0 ≤ t + r.kA.hi p c r.kA.fb → t < s0 → x r.kA.q t = r.kA.w) (hlo : 1 ≤ r.kA.lo p c r.kA.fb)
    (hw6 : (win p c a e E r.pc.2 (r.pc.2.length - 2)).1 + r.kA.hi p c r.ja0 ≤ s0)
    (hSg : r.kGr.S p ≤ t1 + T)
    (hpre2 : s0 + r.kA.hi p c r.kA.fb ≤ t1 + T + r.kGr.hi p c r.jq + r.kA.hi p c r.jg)
    (hov : t1 + T + r.kGr.hi p c r.jq + r.kA.hi p c r.jg ≤
      e + psum p c r.pc.2 (r.pc.2.length - 2) + r.kA.lo p c r.ja0 + 1) :
    ∀ t, s0 ≤ t → t ≤ t2 + r.kGr.lo p c r.jq + r.kA.lo p c r.jg → x r.kA.q t = r.kA.w := by
  simp only [oneAckOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨okA, okG⟩, okGr⟩, hPA⟩, hPG⟩, hPGr⟩, mA⟩, mG⟩, mGr⟩, eq_q⟩, eq_pins⟩, eq_fb⟩, eq_w⟩, hlen⟩, w2⟩, w6⟩, w3⟩, b3⟩, b3'⟩, w1⟩, b1⟩, w0⟩ := hok
  have harbc0 := ha
  simp only [arbCertOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.contains_iff_mem] at harbc0
  obtain ⟨⟨⟨⟨hsp, -⟩, -⟩, -⟩, -⟩ := harbc0
  obtain ⟨hgG, hsG, haG, hloG, hhiG, hSG⟩ := Formal.Cells.CertSwitchAll.krow_congr eq_q.symm eq_pins.symm
  have sA0 : r.kA.src r.ja0 = (r.pc.2.getD (r.pc.2.length - 2) default).r.q := by
    rw [src_of okA (by rw [hPA]; simp)]; exact w2
  have sArst : r.kA.src r.jrst = 186905 := by rw [src_of okA (by rw [hPA]; simp)]; exact w3
  have sGg : r.kG.src r.jg = r.kGr.q := by rw [src_of okG (by rw [hPG]; simp)]; exact w1
  have sGrst : r.kG.src r.jrst = 186905 := by rw [hsG]; exact sArst
  have sGrq : r.kGr.src r.jq = r.A.q := by rw [src_of okGr (by rw [hPGr]; simp)]; exact w0
  have hw := win_end_ge (p := p) (c := c) r.pc.1 r.pc.2 hc hsp a e E PS hPS hE hB (r.pc.2.length - 2) (by omega)
  have hold6 := cert_sound hb r.pc.1 r.pc.2 hc G a e E hcause hstat hmem (r.pc.2.length - 2) (by omega)
  have hset := q_settles hb (A := r.A) (fun A' hA' => harb A' (by rw [List.mem_singleton.mp hA']; exact hA)) r.pc hc ha
    G a e E PS hcause hstat hmem hPS hE hB hoth h1 h2
  have qv : ∀ t, t1 + T ≤ t → t ≤ t2 → x r.A.q t = fl r.kGr.bv r.jq := fun t u1 u2 => by rw [hset t u1 u2, hq0]
  have glow : ∀ t, t1 + T + r.kGr.hi p c r.jq ≤ t → t ≤ t2 + r.kGr.lo p c r.jq → x r.kGr.q t = r.kGr.w :=
    fun t u1 u2 => krow_set hb okGr mGr GGr (fun _ => t1 + T) (fun _ => t2) (fun j hj u v1 v2 => by
        rw [hPGr, List.mem_singleton] at hj; subst hj; rw [sGrq]; exact qv u v1 v2) t (by omega) (fun j hj => by
        rw [hPGr, List.mem_singleton] at hj; subst hj; exact ⟨u1, u2⟩)
  have a1 : ∀ t, s0 ≤ t → t ≤ e + psum p c r.pc.2 (r.pc.2.length - 2) + r.kA.lo p c r.ja0 → x r.kA.q t = r.kA.w :=
    krow_mem hb okA mA GA hlo hS0 hpre1 (fun j hj u v1 v2 => by
      rw [hPA] at hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl
      · rw [sA0, w6]; exact hold6 u (by omega) (by omega)
      · rw [sArst, b3]; exact hrst u (by omega))
  have GG : CGateOK p c r.kG.g r.kG.src r.kG.arcs (r.kG.S p) x := by rw [hgG, hsG, haG, hSG]; exact GA
  have a2 : ∀ t, t1 + T + r.kGr.hi p c r.jq + r.kA.hi p c r.jg ≤ t → t ≤ t2 + r.kGr.lo p c r.jq + r.kA.lo p c r.jg →
      x r.kG.q t = r.kG.w :=
    krow_mem hb okG mG GG (by rw [hloG, ← eq_fb]; exact hlo) (by rw [hSG]; omega)
      (fun t v1 v2 => by
        rw [hhiG, ← eq_fb] at v1
        have := a1 t (by omega) (by omega)
        rw [← eq_q, ← eq_w]; exact this)
      (fun j hj u v1 v2 => by
        rw [hhiG] at v1; rw [hloG] at v2
        rw [hPG] at hj
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · rw [sGg, b1]; exact glow u (by omega) (by omega)
        · rw [sGrst, b3']; exact hrst u (by omega))
  intro t u1 u2
  by_cases ht : t ≤ e + psum p c r.pc.2 (r.pc.2.length - 2) + r.kA.lo p c r.ja0
  · exact a1 t u1 ht
  · have := a2 t (by omega) u2; rw [← eq_q, ← eq_w] at this; exact this

/-- **Every checked one-acknowledge row, in every behaviour of THE circuit** (one corner for all rows, H_ARB(T)). -/
theorem one_ack_of (L : List OneAckRow)
    (hL : ∀ r ∈ L, oneAckOK r = true ∧ certOK r.pc.1 r.pc.2 = true ∧ arbCertOK r.A r.pc = true ∧ r.A ∈ arbs)
    {p : DelayPar} (hp : Formal.Timing.SpecSettle.Sane p) {x : Beh} (hb : Behaves p (circuit net boundary) x)
    {T : Nat} (harb : ArbOK T arbs x) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ r ∈ L, ∀ (a e : Nat) (E : Nat → Nat) (PS t1 t2 s0 ar : Nat),
      (∀ t, a ≤ t → t ≤ e → x r.pc.1.cn t = r.pc.1.cv) →
      (∀ k, k < r.pc.1.sn.length → ∀ t, a ≤ t → t ≤ E k → x (r.pc.1.sn.getD k 0) t = r.pc.1.sv.getD k false) →
      (∀ i, i < r.pc.2.length → (r.pc.2.getD i default).r.mem = true →
        1 ≤ (r.pc.2.getD i default).r.lo p c (r.pc.2.getD i default).r.fb ∧
        ∀ t, (win p c a e E r.pc.2 i).1 ≤ t + (r.pc.2.getD i default).r.hi p c (r.pc.2.getD i default).r.fb →
          t < (win p c a e E r.pc.2 i).1 → x (r.pc.2.getD i default).r.q t = (r.pc.2.getD i default).r.w) →
      (∀ i, i < r.pc.2.length → psum p c r.pc.2 i ≤ PS) → (∀ k, e + PS ≤ E k) → e + PS ≤ BIG →
      (∀ n ∈ r.A.ins, n ≠ (r.pc.2.getD (r.pc.2.length - 1) default).r.q → ConstOn (x n) t1 t2) →
      (win p c a e E r.pc.2 (r.pc.2.length - 1)).1 ≤ t1 → t2 ≤ e + psum p c r.pc.2 (r.pc.2.length - 1) →
      x r.A.q (t1 + T) = fl r.kGr.bv r.jq →
      (∀ t, ar ≤ t → x 186905 t = false) →
      r.kA.S p ≤ s0 → ar + r.kA.hi p c r.jrst ≤ s0 →
      (∀ t, s0 ≤ t + r.kA.hi p c r.kA.fb → t < s0 → x r.kA.q t = r.kA.w) → 1 ≤ r.kA.lo p c r.kA.fb →
      (win p c a e E r.pc.2 (r.pc.2.length - 2)).1 + r.kA.hi p c r.ja0 ≤ s0 →
      r.kGr.S p ≤ t1 + T →
      s0 + r.kA.hi p c r.kA.fb ≤ t1 + T + r.kGr.hi p c r.jq + r.kA.hi p c r.jg →
      t1 + T + r.kGr.hi p c r.jq + r.kA.hi p c r.jg ≤ e + psum p c r.pc.2 (r.pc.2.length - 2) + r.kA.lo p c r.ja0 + 1 →
      ∀ t, s0 ≤ t → t ≤ t2 + r.kGr.lo p c r.jq + r.kA.lo p c r.jg → x r.kA.q t = r.kA.w := by
  obtain ⟨c, hc0, hc1, hcol⟩ := Formal.Cells.ViewPS.view_collapse hp hb
    (L.flatMap fun r => (r.kA.q, r.kA.pins) :: (r.kGr.q, r.kGr.pins) :: (List.range r.pc.2.length).map fun i =>
      ((r.pc.2.getD i default).r.q, (r.pc.2.getD i default).r.pins)) (by
      simp only [List.all_eq_true, List.mem_flatMap, List.mem_cons, List.mem_map, List.mem_range]
      rintro e ⟨r, hr, he⟩
      obtain ⟨hok, hc, -, -⟩ := hL r hr
      simp only [oneAckOK, Bool.and_eq_true] at hok
      rcases he with rfl | rfl | ⟨i, hi, rfl⟩
      · exact (krow_facts hb hok.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1).2.2.2.2.2
      · exact (krow_facts hb hok.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2).2.2.2.2.2
      · simp only [certOK, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hc
        exact (krow_facts hb (hc i hi).1).2.2.2.2.2)
  refine ⟨c, hc0, hc1, fun r hr a e E PS t1 t2 s0 ar h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 => ?_⟩
  obtain ⟨hok, hc, ha, hA⟩ := hL r hr
  exact one_ack hok hc ha hA hb harb
    (fun i hi => hcol _ (List.mem_flatMap.mpr ⟨r, hr, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))⟩))
    (hcol _ (List.mem_flatMap.mpr ⟨r, hr, List.mem_cons_self⟩))
    (hcol _ (List.mem_flatMap.mpr ⟨r, hr, List.mem_cons_of_mem _ List.mem_cons_self⟩))
    a e E PS t1 t2 s0 ar h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19

end Formal.Cells.ArbOneAck
