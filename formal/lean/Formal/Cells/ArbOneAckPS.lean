import Formal.Cells.ArbServerPS

/-!
# Formal.Cells.ArbOneAckPS — arbiter 0 does not acknowledge the losing client (every behaviour, H_ARB(T))

Shard B, 2026-11-07. ucontrol_merge10.uarb1 (`arbs[0]`, state SLICE_X38Y51.B6 = node 144471), the transaction in
which its state q falls (client 2 wins, as in `CertArbPS.c000`): the losing side's acknowledge A1
(SLICE_X39Y51.D6, node 146522 = C(g1, A0)) stays low for the whole transaction.

## Problem, plainly
`ArbTSpec.spec_double_ack`: with H_ARB(T) alone, both clients can be acknowledged. Here, in every behaviour of THE
circuit with H_ARB(T): A1 is held low first by A0 low (the server cannot answer before the server path's delay after
q moved: the certificate `c000`), and from then on by its grant g1 = r1·q low (q settled at the winner's value:
`ArbServer.q_settles`), the two holds overlapping when T is small enough (premise `hov`).

## Proved (standard axioms)
`target_arb0_one_ack`: the statement below; rows `kA1` (A1 held by A0 low and reset low, feedback), `kG1` (A1 held by
g1 low and reset low, feedback), `kGr1` (g1 held low by q low), kernel-checked (`krowOK`) on the netlist's own gates,
with the wiring facts (`wiring`).

## Not shown
The premises (order-level and the timing condition `hov`); the other transaction direction and the other arbiters
(same pattern); that A1 was low before (premise `hpre1`).
-/

namespace Formal.Cells.ArbOneAckPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecChain Formal.Cells.CertPS Formal.Cells.RaceCertPS
  Formal.Cells.CertMarginPS Formal.Cells.ArbServer Formal.Cells.CertArbPS Formal.Cells.SpecFbChain
  Formal.Cells.SpecCElemFact

def kA1 : KRow := ⟨146522, [([146507, 146506, 144432], 144435), ([146510, 146509, 146508, 146511], 144448), ([146513, 146512, 144460, 144459, 144465], 144585), ([146515, 146514, 144532, 144531, 140810, 127324, 87313, 87312, 9573, 5001, 2383, 1181, 1180, 1179, 1185], 186905), ([146518, 146517, 146516, 146519], 146522), ([146521, 146520, 144432], 144435)], [2, 3], [false, false, false, false, false, false], false, 4, true, [true, false, false, false, false, true], [false, false, false, false, false, false]⟩
def kG1 : KRow := ⟨146522, [([146507, 146506, 144432], 144435), ([146510, 146509, 146508, 146511], 144448), ([146513, 146512, 144460, 144459, 144465], 144585), ([146515, 146514, 144532, 144531, 140810, 127324, 87313, 87312, 9573, 5001, 2383, 1181, 1180, 1179, 1185], 186905), ([146518, 146517, 146516, 146519], 146522), ([146521, 146520, 144432], 144435)], [1, 3], [false, false, false, false, false, false], false, 4, true, [true, false, false, false, false, true], [false, false, false, false, false, false]⟩
def kGr1 : KRow := ⟨144448, [([144425, 144424, 144423, 144422, 144426], 144471), ([144430, 144429, 144428, 144427, 144431], 144547), ([144434, 144433, 144432], 144435), ([144440, 144439, 144438, 144437, 144436, 144441], 151633), ([144443, 144442], 144444)], [0], [false, false, false, false, false], false, 5, false, [false, false, true, false, true], [false, false, false, false, true]⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rows_ok : krowOK kA1 = true ∧ krowOK kG1 = true ∧ krowOK kGr1 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The wiring: A1 reads A0's source (the certificate's row 6) on pin 2, the reset on pin 3, g1 on pin 1; g1 reads q
on pin 0; the certificate's row 6 holds low; q is arbiter 0's state. -/
theorem wiring : kA1.src 2 = (c000.2.getD 6 default).r.q ∧ (c000.2.getD 6 default).r.w = false ∧
    kA1.src 3 = 186905 ∧ kG1.src 1 = kGr1.q ∧ kG1.src 3 = 186905 ∧ kGr1.src 0 = 144471 ∧
    (arbs.getD 0 ⟨0, []⟩).q = 144471 ∧ c000.2.length = 8 ∧ kA1.q = 146522 ∧ kG1.q = 146522 := by decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- **Arbiter 0: the losing client is not acknowledged** (q falls; A1 is the losing side's acknowledge). -/
theorem target_arb0_one_ack {p : DelayPar} (hp : Formal.Timing.SpecSettle.Sane p) {x : Beh}
    (hb : Behaves p (circuit net boundary) x) {T : Nat} (harb : ArbOK T arbs x) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ (a e : Nat) (E : Nat → Nat) (PS t1 t2 s0 ar : Nat),
      (∀ t, a ≤ t → t ≤ e → x c000.1.cn t = c000.1.cv) →
      (∀ k, k < c000.1.sn.length → ∀ t, a ≤ t → t ≤ E k → x (c000.1.sn.getD k 0) t = c000.1.sv.getD k false) →
      (∀ i, i < c000.2.length → (c000.2.getD i default).r.mem = true →
        1 ≤ (c000.2.getD i default).r.lo p c (c000.2.getD i default).r.fb ∧
        ∀ t, (win p c a e E c000.2 i).1 ≤ t + (c000.2.getD i default).r.hi p c (c000.2.getD i default).r.fb →
          t < (win p c a e E c000.2 i).1 → x (c000.2.getD i default).r.q t = (c000.2.getD i default).r.w) →
      (∀ i, i < c000.2.length → psum p c c000.2 i ≤ PS) → (∀ k, e + PS ≤ E k) → e + PS ≤ BIG →
      (∀ n ∈ (arbs.getD 0 ⟨0, []⟩).ins, n ≠ (c000.2.getD 7 default).r.q → ConstOn (x n) t1 t2) →
      (win p c a e E c000.2 7).1 ≤ t1 → t2 ≤ e + psum p c c000.2 7 →
      x 144471 (t1 + T) = false →
      (∀ t, ar ≤ t → x 186905 t = false) →
      kA1.S p ≤ s0 → ar + kA1.hi p c 3 ≤ s0 →
      (∀ t, s0 ≤ t + kA1.hi p c 4 → t < s0 → x 146522 t = false) → 1 ≤ kA1.lo p c 4 →
      (win p c a e E c000.2 6).1 + kA1.hi p c 2 ≤ s0 →
      kGr1.S p ≤ t1 + T →
      s0 + kA1.hi p c 4 ≤ t1 + T + kGr1.hi p c 0 + kA1.hi p c 1 →
      t1 + T + kGr1.hi p c 0 + kA1.hi p c 1 ≤ e + psum p c c000.2 6 + kA1.lo p c 2 + 1 →
      ∀ t, s0 ≤ t → t ≤ t2 + kGr1.lo p c 0 + kA1.lo p c 1 → x 146522 t = false := by
  obtain ⟨okA1, okG1, okGr1⟩ := rows_ok
  obtain ⟨w2, w6, w3, w1, w3', w0, wq, wlen, wqa, wqg⟩ := wiring
  have hcert : certOK c000.1 c000.2 = true :=
    (List.all_eq_true.1 certs_ok) _ (by simp [certs, certs00, certs01, certs02, certs03])
  have harbc : arbCertOK (arbs.getD 0 ⟨0, []⟩) c000 = true :=
    (List.all_eq_true.1 Formal.Cells.ArbServerPS.rowsA_arb) ⟨arbs.getD 0 ⟨0, []⟩, c000⟩ (by simp [Formal.Cells.ArbServerPS.rowsA])
  have hA : arbs.getD 0 ⟨0, []⟩ ∈ arbs := Formal.Cells.ArbServerPS.getD_mem (by decide)
  obtain ⟨c, hc0, hc1, hcol⟩ := Formal.Cells.ViewPS.view_collapse hp hb
    (((List.range c000.2.length).map fun i => ((c000.2.getD i default).r.q, (c000.2.getD i default).r.pins)) ++
      [(kA1.q, kA1.pins), (kGr1.q, kGr1.pins)]) (by
      simp only [List.all_append, List.all_eq_true, List.mem_map, List.mem_range, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · rintro e ⟨i, hi, rfl⟩
        have h := hcert
        simp only [certOK, List.all_eq_true, List.mem_range, Bool.and_eq_true] at h
        exact (krow_facts hb (h i hi).1).2.2.2.2.2
      · intro e he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · exact (krow_facts hb okA1).2.2.2.2.2
        · exact (krow_facts hb okGr1).2.2.2.2.2)
  have G : ∀ i, i < c000.2.length → CGateOK p c (c000.2.getD i default).r.g (c000.2.getD i default).r.src
      (c000.2.getD i default).r.arcs ((c000.2.getD i default).r.S p) x := fun i hi =>
    hcol _ (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)))
  have GA1 : CGateOK p c kA1.g kA1.src kA1.arcs (kA1.S p) x := hcol (kA1.q, kA1.pins) (by simp)
  have GG1 : CGateOK p c kG1.g kG1.src kG1.arcs (kG1.S p) x := GA1
  have GGr1 : CGateOK p c kGr1.g kGr1.src kGr1.arcs (kGr1.S p) x := hcol (kGr1.q, kGr1.pins) (by simp)
  refine ⟨c, hc0, hc1, fun a e E PS t1 t2 s0 ar hcause hstat hmem hPS hE hB hoth h1 h2 hq0 hrst hS0 hrs0 hpre1
    hlo4 hw6 hSg hpre2 hov => ?_⟩
  have harbc0 := harbc
  simp only [arbCertOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.contains_iff_mem] at harbc0
  obtain ⟨⟨⟨⟨hsp, -⟩, -⟩, -⟩, -⟩ := harbc0
  -- 1. A0's source (row 6) holds low on [win6.1, e + psum6]
  have hw := win_end_ge (p := p) (c := c) c000.1 c000.2 hcert hsp a e E PS hPS hE hB 6 (by omega)
  have hold6 := cert_sound hb c000.1 c000.2 hcert G a e E hcause hstat hmem 6 (by omega)
  rw [w6] at hold6
  -- 2. q settles low on [t1 + T, t2]
  have hset := q_settles hb (A := arbs.getD 0 ⟨0, []⟩)
    (fun A' hA' => harb A' (by rw [List.mem_singleton.mp hA']; exact hA)) c000 hcert harbc G a e E PS hcause hstat
    hmem hPS hE hB hoth h1 h2
  rw [wq] at hset
  have qlow : ∀ t, t1 + T ≤ t → t ≤ t2 → x 144471 t = false := fun t u1 u2 => by rw [hset t u1 u2, hq0]
  -- 3. g1 is low on [t1 + T + hi, t2 + lo]
  have glow : ∀ t, t1 + T + kGr1.hi p c 0 ≤ t → t ≤ t2 + kGr1.lo p c 0 → x kGr1.q t = false := fun t u1 u2 =>
    krow_set hb okGr1 rfl GGr1 (fun _ => t1 + T) (fun _ => t2) (fun j hj u v1 v2 => by
        have : j = 0 := by simpa [kGr1] using hj
        subst this; rw [w0]; exact qlow u v1 v2) t (by omega) (fun j hj => by
        have : j = 0 := by simpa [kGr1] using hj
        subst this; exact ⟨u1, u2⟩)
  -- 4. A1 is low on [s0, e + psum6 + lo] (A0 low, reset low)
  have hlo4' : 1 ≤ kA1.lo p c kA1.fb := hlo4
  have a1low : ∀ t, s0 ≤ t → t ≤ e + psum p c c000.2 6 + kA1.lo p c 2 → x kA1.q t = kA1.w :=
    krow_mem hb okA1 rfl GA1 hlo4' hS0 (by rw [wqa]; exact hpre1) (fun j hj u v1 v2 => by
      have : j = 2 ∨ j = 3 := by simpa [kA1] using hj
      rcases this with rfl | rfl
      · rw [w2]; exact hold6 u (by omega) (by omega)
      · rw [w3]; exact hrst u (by omega))
  -- 5. A1 is low on [s2, t2 + lo + lo] (g1 low, reset low)
  have eqhi : kG1.hi p c = kA1.hi p c := rfl
  have eqlo : kG1.lo p c = kA1.lo p c := rfl
  have a1low2 : ∀ t, t1 + T + kGr1.hi p c 0 + kA1.hi p c 1 ≤ t → t ≤ t2 + kGr1.lo p c 0 + kA1.lo p c 1 →
      x kG1.q t = kG1.w :=
    krow_mem hb okG1 rfl GG1 (by rw [eqlo]; exact hlo4') (by show kA1.S p ≤ _; omega)
      (fun t v1 v2 => by
        rw [eqhi, show kG1.fb = 4 from rfl] at v1
        have := a1low t (by omega) (by omega)
        rw [wqa] at this; rw [wqg]; exact this)
      (fun j hj u v1 v2 => by
        rw [eqhi] at v1; rw [eqlo] at v2
        have : j = 1 ∨ j = 3 := by simpa [kG1] using hj
        rcases this with rfl | rfl
        · rw [w1]; exact glow u (by omega) (by omega)
        · rw [w3']; exact hrst u (by omega))
  intro t u1 u2
  by_cases ht : t ≤ e + psum p c c000.2 6 + kA1.lo p c 2
  · have := a1low t u1 ht; rw [wqa] at this; exact this
  · have := a1low2 t (by omega) u2; rw [wqg] at this; exact this

end Formal.Cells.ArbOneAckPS
