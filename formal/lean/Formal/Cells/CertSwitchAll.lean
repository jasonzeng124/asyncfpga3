import Formal.Cells.CertRaceAll

/-!
# Formal.Cells.CertSwitchAll — a checked race row makes its storage node switch cleanly (every behaviour)

Shard B, 2026-11-07. Generalises `RaceCertPS.target_b_switch` (one node) to any race row of `CertRaceAll`.

## Problem, plainly
A storage node of THE target that starts to switch (its force condition holds) should reach its new value and keep
it, with no runt and no fall-back, in every behaviour. `SpecFbChain.cfb_switch` reduces that to: the force condition
holds for the node's feedback-loop upper delay. The force condition reads the acknowledge pin, which the race row's
certificate keeps at its old value for exactly that long (`race_row`).

## Proved (standard axioms)
* `SwRow`, `swOK`: a race row plus the node's force row `F` (INIT = w' whenever its controlling pins, the acknowledge
  pin among them at the old acknowledge value, show their values; feedback free) and confirm row `C` (INIT = w'
  whenever its pins and the feedback (= w') show their values; acknowledge free), on the node's own pins.
* `switch_row`: in a behaviour at a corner, with the certificate's premises (the node old until `s - 1`), the other
  force pins' sources holding their values over the reads in `[s, e']`, the confirm pins' likewise, and the timing
  conditions (`s + hi(feedback) ≤ e' + 1`, the certificate window started `hi(ack)` before `s`), the node is `w'` on
  all of `[s, e']`.
* `target_switches_of`: every row of a checked list, one corner, every behaviour of THE circuit (g = 1, κ ≤ 83/200).
-/

namespace Formal.Cells.CertSwitchAll
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecChain Formal.Cells.CertPS Formal.Cells.RaceCertPS
  Formal.Cells.CertMarginPS Formal.Cells.CertRaceAll Formal.Cells.SpecFbChain Formal.Cells.SpecCElemFact

structure SwRow where
  rr : RaceRow
  F : KRow
  C : KRow

def swOK (s : SwRow) : Bool :=
  krowOK s.F && krowOK s.C && s.F.q == s.rr.node.q && s.C.q == s.rr.node.q &&
  s.F.pins == s.rr.node.pins && s.C.pins == s.rr.node.pins &&
  !s.F.mem && s.C.mem && s.C.fb == s.rr.jf && s.F.w == s.C.w &&
  s.F.P.contains s.rr.ja && fl s.F.bv s.rr.ja == (s.rr.pc.2.getD (s.rr.pc.2.length - 1) default).r.w &&
  !(s.F.P.contains s.rr.jf) && !(fl s.F.held s.rr.jf) && !(s.C.P.contains s.rr.jf) && !(fl s.C.held s.rr.jf)

theorem krow_congr {F n : KRow} (hq : F.q = n.q) (hp : F.pins = n.pins) :
    F.g = n.g ∧ F.src = n.src ∧ F.arcs = n.arcs ∧ (∀ p c, F.lo p c = n.lo p c) ∧ (∀ p c, F.hi p c = n.hi p c) ∧
      (∀ p, F.S p = n.S p) := by
  have hg : F.g = n.g := by simp only [KRow.g, hq]
  refine ⟨hg, ?_, ?_, ?_, ?_, ?_⟩
  · funext i; simp only [KRow.src, hp]
  · simp only [KRow.arcs, hg, hp]
  · intro p c; funext i; simp only [KRow.lo, KRow.arcs, hg, hp]
  · intro p c; funext i; simp only [KRow.hi, KRow.arcs, hg, hp]
  · intro p; simp only [KRow.S, hg, hp]

/-- **A checked switch row: the storage node switches cleanly** (in a behaviour at a corner). -/
theorem switch_row {s : SwRow} (hc : certOK s.rr.pc.1 s.rr.pc.2 = true) (hr : raceOK s.rr = true)
    (hs : swOK s = true) {κ : ℚ} (hk0 : 0 ≤ κ) (hk : κ ≤ 83 / 200) {x : Beh}
    (hb : Behaves ⟨1, κ⟩ (circuit net boundary) x) {c : ℚ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (G : ∀ i, i < s.rr.pc.2.length → CGateOK ⟨1, κ⟩ c (s.rr.pc.2.getD i default).r.g (s.rr.pc.2.getD i default).r.src
      (s.rr.pc.2.getD i default).r.arcs ((s.rr.pc.2.getD i default).r.S ⟨1, κ⟩) x)
    (Gn : CGateOK ⟨1, κ⟩ c s.F.g s.F.src s.F.arcs (s.F.S ⟨1, κ⟩) x)
    (a : Nat) (E : Nat → Nat) (PS sT e' : Nat) (hs1 : 1 ≤ sT) (hSn : s.F.S ⟨1, κ⟩ ≤ sT)
    (hcause : ∀ t, a ≤ t → t ≤ sT - 1 → x s.rr.pc.1.cn t = s.rr.pc.1.cv)
    (hstat : ∀ k, k < s.rr.pc.1.sn.length → ∀ t, a ≤ t → t ≤ E k → x (s.rr.pc.1.sn.getD k 0) t = s.rr.pc.1.sv.getD k false)
    (hmem : ∀ i, i < s.rr.pc.2.length → (s.rr.pc.2.getD i default).r.mem = true →
      1 ≤ (s.rr.pc.2.getD i default).r.lo ⟨1, κ⟩ c (s.rr.pc.2.getD i default).r.fb ∧
      ∀ t, (win ⟨1, κ⟩ c a (sT - 1) E s.rr.pc.2 i).1 ≤ t + (s.rr.pc.2.getD i default).r.hi ⟨1, κ⟩ c (s.rr.pc.2.getD i default).r.fb →
        t < (win ⟨1, κ⟩ c a (sT - 1) E s.rr.pc.2 i).1 → x (s.rr.pc.2.getD i default).r.q t = (s.rr.pc.2.getD i default).r.w)
    (hPS : ∀ i, i < s.rr.pc.2.length → psum ⟨1, κ⟩ c s.rr.pc.2 i ≤ PS) (hE : ∀ k, sT - 1 + PS ≤ E k)
    (hB : sT - 1 + PS ≤ BIG)
    (hwst : (win ⟨1, κ⟩ c a (sT - 1) E s.rr.pc.2 (s.rr.pc.2.length - 1)).1 + s.F.hi ⟨1, κ⟩ c s.rr.ja ≤ sT)
    (hlo : 1 ≤ s.F.lo ⟨1, κ⟩ c s.rr.jf) (he' : sT + s.F.hi ⟨1, κ⟩ c s.rr.jf ≤ e' + 1)
    (hFp : ∀ j ∈ s.F.P, j ≠ s.rr.ja → ∀ u, sT ≤ u + s.F.hi ⟨1, κ⟩ c j → u + s.F.lo ⟨1, κ⟩ c j ≤ e' →
      x (s.F.src j) u = fl s.F.bv j)
    (hCp : ∀ j ∈ s.C.P, ∀ u, sT ≤ u + s.F.hi ⟨1, κ⟩ c j → u + s.F.lo ⟨1, κ⟩ c j ≤ e' →
      x (s.F.src j) u = fl s.C.bv j) :
    ∀ t, sT ≤ t → t ≤ e' → x s.rr.node.q t = s.F.w := by
  simp only [swOK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.contains_iff_mem] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hF, hC⟩, hFq⟩, hCq⟩, hFp'⟩, hCp'⟩, hFm⟩, hCm⟩, hCfb⟩, hw⟩, hjaP⟩, hjaV⟩, hjfF⟩, hjfFh⟩,
    hjfC⟩, hjfCh⟩ := hs
  obtain ⟨hgF, hsF, haF, hloF, hhiF, hSF⟩ := krow_congr hFq hFp'
  obtain ⟨hgC, hsC, haC, hloC, hhiC, hSC⟩ := krow_congr hCq hCp'
  have race := race_row hc hr hk0 hk hb hc0 hc1 G a (sT - 1) E PS hcause hstat hmem hPS hE hB
  obtain ⟨hja, hjf, -, R⟩ := race
  obtain ⟨-, hfbC, -, -, houtC, -⟩ := krow_facts hb hC
  obtain ⟨hfbk, hfbs⟩ := hfbC hCm
  rw [hCfb] at hfbk hfbs
  -- move C's view to F's (same gate, pins)
  have hgCF : s.C.g = s.F.g := by rw [hgC, hgF]
  have hsCF : s.C.src = s.F.src := by rw [hsC, hsF]
  have hloCF : ∀ p c, s.C.lo p c = s.F.lo p c := fun p c => by rw [hloC, hloF]
  have hhiCF : ∀ p c, s.C.hi p c = s.F.hi p c := fun p c => by rw [hhiC, hhiF]
  have hfb : s.F.src s.rr.jf = s.F.g.out := by rw [← hsCF, ← hgCF]; exact hfbs
  have hbd : CBands ⟨1, κ⟩ c s.F.g.k s.F.arcs (s.F.lo ⟨1, κ⟩ c) (s.F.hi ⟨1, κ⟩ c) := cbands_of_sums s.F.arcs
  have hjfk : s.rr.jf < s.F.g.k := by rw [← hgCF]; exact hfbk
  have hsrc_ja : s.F.src s.rr.ja = (s.rr.pc.2.getD (s.rr.pc.2.length - 1) default).r.q := by
    obtain ⟨hPF, -, -, -, -, -⟩ := krow_facts hb hF
    have hk := hPF _ hjaP
    have hklen : s.F.g.k = s.F.pins.length := by
      simp only [krowOK, Bool.and_eq_true, beq_iff_eq] at hF; exact hF.1.1.1.1.1.1
    rw [ksrc_eq s.F (by omega), hFp', hja]
  have key := cfb_switch Gn hbd (j := s.rr.jf) hjfk hfb hlo (s := sT) (e := sT + s.F.hi ⟨1, κ⟩ c s.rr.jf - 1)
    (e' := e') hSn (by omega) (cv := s.F.w)
    (fun t t1 t2 v hv => visible_fact hb hF s.rr.jf (by simpa [List.contains_iff_mem] using hjfF) hjfFh t (fun j hj u u1 u2 => by
        by_cases hjj : j = s.rr.ja
        · subst hjj
          rw [hsrc_ja, hjaV]
          refine R u (by omega) ?_
          rw [← hloF, ← hhiF]; omega
        · exact hFp j hj hjj u (by omega) (by omega)) v hv (by simp [hFm]))
    (fun t t1 t2 v hv0 hv => by
      have hv' : CVisible x s.C.g.k s.C.src (s.C.lo ⟨1, κ⟩ c) (s.C.hi ⟨1, κ⟩ c) s.rr.jf t v := by
        rw [hgCF, hsCF, hloCF, hhiCF]; exact hv
      have := visible_fact hb hC s.rr.jf (by simpa [List.contains_iff_mem] using hjfC) hjfCh t (fun j hj u u1 u2 => by
          rw [hsCF]; rw [hloCF] at u1; rw [hhiCF] at u2
          exact hCp j hj u (by omega) (by omega)) v hv' (fun _ => by rw [hCfb, hv0, hw])
      rw [hgCF, ← hw] at this; exact this)
  intro t t1 t2
  have := key t t1 t2
  obtain ⟨-, -, -, -, houtF, -⟩ := krow_facts hb hF
  rw [houtF, hFq] at this
  exact this

/-- **Every checked switch row, in every behaviour of THE circuit** (one corner for all rows, g = 1, κ ≤ 83/200):
each row's storage node, once its certificate premises and force/confirm premises hold from `sT` to `e'`, is at its
new value on all of `[sT, e']`. -/
theorem target_switches_of (L : List SwRow)
    (hL : ∀ s ∈ L, certOK s.rr.pc.1 s.rr.pc.2 = true ∧ raceOK s.rr = true ∧ swOK s = true)
    {κ : ℚ} (hk0 : 0 ≤ κ) (hk : κ ≤ 83 / 200) {x : Beh} (hb : Behaves ⟨1, κ⟩ (circuit net boundary) x) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ s ∈ L, ∀ (a : Nat) (E : Nat → Nat) (PS sT e' : Nat), 1 ≤ sT → s.F.S ⟨1, κ⟩ ≤ sT →
      (∀ t, a ≤ t → t ≤ sT - 1 → x s.rr.pc.1.cn t = s.rr.pc.1.cv) →
      (∀ k, k < s.rr.pc.1.sn.length → ∀ t, a ≤ t → t ≤ E k → x (s.rr.pc.1.sn.getD k 0) t = s.rr.pc.1.sv.getD k false) →
      (∀ i, i < s.rr.pc.2.length → (s.rr.pc.2.getD i default).r.mem = true →
        1 ≤ (s.rr.pc.2.getD i default).r.lo ⟨1, κ⟩ c (s.rr.pc.2.getD i default).r.fb ∧
        ∀ t, (win ⟨1, κ⟩ c a (sT - 1) E s.rr.pc.2 i).1 ≤ t + (s.rr.pc.2.getD i default).r.hi ⟨1, κ⟩ c (s.rr.pc.2.getD i default).r.fb →
          t < (win ⟨1, κ⟩ c a (sT - 1) E s.rr.pc.2 i).1 → x (s.rr.pc.2.getD i default).r.q t = (s.rr.pc.2.getD i default).r.w) →
      (∀ i, i < s.rr.pc.2.length → psum ⟨1, κ⟩ c s.rr.pc.2 i ≤ PS) → (∀ k, sT - 1 + PS ≤ E k) → sT - 1 + PS ≤ BIG →
      (win ⟨1, κ⟩ c a (sT - 1) E s.rr.pc.2 (s.rr.pc.2.length - 1)).1 + s.F.hi ⟨1, κ⟩ c s.rr.ja ≤ sT →
      1 ≤ s.F.lo ⟨1, κ⟩ c s.rr.jf → sT + s.F.hi ⟨1, κ⟩ c s.rr.jf ≤ e' + 1 →
      (∀ j ∈ s.F.P, j ≠ s.rr.ja → ∀ u, sT ≤ u + s.F.hi ⟨1, κ⟩ c j → u + s.F.lo ⟨1, κ⟩ c j ≤ e' →
        x (s.F.src j) u = fl s.F.bv j) →
      (∀ j ∈ s.C.P, ∀ u, sT ≤ u + s.F.hi ⟨1, κ⟩ c j → u + s.F.lo ⟨1, κ⟩ c j ≤ e' → x (s.F.src j) u = fl s.C.bv j) →
      ∀ t, sT ≤ t → t ≤ e' → x s.rr.node.q t = s.F.w := by
  have hp : Formal.Timing.SpecSettle.Sane ⟨1, κ⟩ := ⟨hk0, by linarith, by norm_num⟩
  obtain ⟨c, hc0, hc1, hcol⟩ := Formal.Cells.ViewPS.view_collapse hp hb
    (L.flatMap fun s => (s.F.q, s.F.pins) :: (List.range s.rr.pc.2.length).map fun i =>
      ((s.rr.pc.2.getD i default).r.q, (s.rr.pc.2.getD i default).r.pins)) (by
      simp only [List.all_eq_true, List.mem_flatMap, List.mem_cons, List.mem_map, List.mem_range]
      rintro e ⟨s, hs, he⟩
      rcases he with rfl | ⟨i, hi, rfl⟩
      · have h := (hL s hs).2.2
        simp only [swOK, Bool.and_eq_true] at h
        exact (krow_facts hb h.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1).2.2.2.2.2
      · have hc := (hL s hs).1
        simp only [certOK, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hc
        exact (krow_facts hb (hc i hi).1).2.2.2.2.2)
  refine ⟨c, hc0, hc1, fun s hs a E PS sT e' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 => ?_⟩
  obtain ⟨hc, hr, hw⟩ := hL s hs
  exact switch_row hc hr hw hk0 hk hb hc0 hc1
    (fun i hi => hcol _ (List.mem_flatMap.mpr ⟨s, hs, List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)⟩))
    (hcol _ (List.mem_flatMap.mpr ⟨s, hs, List.mem_cons_self⟩))
    a E PS sT e' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13

end Formal.Cells.CertSwitchAll
