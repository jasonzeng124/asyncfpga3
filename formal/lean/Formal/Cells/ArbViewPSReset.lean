import Formal.Cells.ArbViewPS

/-!
# Formal.Cells.ArbViewPSReset — the clear direction of a separated arbitration, every behaviour of THE circuit

Shard B, THE goal, S3/H_ARB. The mirror of `ArbViewPS.target_arb_clean_set`: if an arbiter state LUT's reads see r1
low, r2 high, reset low and A0 low for at least its routed feedback's longest delay, and r2 stays high (reset low)
afterwards, q = 0 on the whole window. `resetFact`/`zconfFact` (decidable, all 2^k addresses) with soundness
lemmas; `arows_reset_ok`: THE target's nine state LUTs (ArbViewPS.arows) meet both; `target_ps_arb_clean_reset`.
Not covered: as in ArbViewPS (separation of the target's arbitrations is simulation evidence only).
-/

namespace Formal.Cells.ArbViewPSReset
open Formal.Target Formal.Target.DecodedPS Formal.Cells.RaceLinkPS Formal.Timing.SpecSettle
  Formal.Timing.SpecChain Formal.Net.CViewPS Formal.Cells.ViewPS Formal.Cells.SpecFbChain
  Formal.Cells.ArbClean Formal.Cells.ArbCleanChain Formal.Cells.ArbViewPS

def resetFact (k init : Nat) (R : Roles) : Bool :=
  (List.range (2 ^ k)).all fun a =>
    let v := fun i => a.testBit i
    !(!v R.r1 && v R.r2 && !v R.rst && !v R.a0 && R.tied.all (fun jb => v jb.1 == jb.2)) || !init.testBit a

def zconfFact (k init : Nat) (R : Roles) : Bool :=
  (List.range (2 ^ k)).all fun a =>
    let v := fun i => a.testBit i
    !(v R.r2 && !v R.fb && !v R.rst && R.tied.all (fun jb => v jb.1 == jb.2)) || !init.testBit a

theorem hreset_of_fact {k init : Nat} {R : Roles} (h : resetFact k init R = true)
    (hk : R.r1 < k ∧ R.r2 < k ∧ R.rst < k ∧ R.a0 < k) (htk : ∀ jb ∈ R.tied, jb.1 < k) :
    ∀ v : Nat → Bool, v R.r1 = false → v R.r2 = true → v R.rst = false → v R.a0 = false →
      (∀ jb ∈ R.tied, v jb.1 = jb.2) → init.testBit (addr k v) = false := by
  intro v h1 h2 h3 h4 ht
  have ha := Formal.Cells.PrimTables.addr_lt k v
  have hb := fun i hi => Formal.Cells.PrimTables.addr_testBit k v i hi
  unfold resetFact at h
  have := List.all_eq_true.mp h (addr k v) (List.mem_range.mpr ha)
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
  rcases this with hc | hc
  · exfalso
    rw [hb _ hk.1, hb _ hk.2.1, hb _ hk.2.2.1, hb _ hk.2.2.2, h1, h2, h3, h4] at hc
    simp only [Bool.not_false, Bool.and_true, Bool.true_and] at hc
    have : (R.tied.all fun jb => (addr k v).testBit jb.1 == jb.2) = true := by
      rw [List.all_eq_true]; intro jb hj; rw [hb _ (htk jb hj), ht jb hj]; simp
    rw [this] at hc; exact Bool.false_ne_true hc.symm
  · exact hc

theorem hzconf_of_fact {k init : Nat} {R : Roles} (h : zconfFact k init R = true)
    (hk : R.r2 < k ∧ R.fb < k ∧ R.rst < k) (htk : ∀ jb ∈ R.tied, jb.1 < k) :
    ∀ v : Nat → Bool, v R.r2 = true → v R.fb = false → v R.rst = false →
      (∀ jb ∈ R.tied, v jb.1 = jb.2) → init.testBit (addr k v) = false := by
  intro v h1 h2 h3 ht
  have ha := Formal.Cells.PrimTables.addr_lt k v
  have hb := fun i hi => Formal.Cells.PrimTables.addr_testBit k v i hi
  unfold zconfFact at h
  have := List.all_eq_true.mp h (addr k v) (List.mem_range.mpr ha)
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at this
  rcases this with hc | hc
  · exfalso
    rw [hb _ hk.1, hb _ hk.2.1, hb _ hk.2.2, h1, h2, h3] at hc
    simp only [Bool.not_false, Bool.and_true, Bool.true_and] at hc
    have : (R.tied.all fun jb => (addr k v).testBit jb.1 == jb.2) = true := by
      rw [List.all_eq_true]; intro jb hj; rw [hb _ (htk jb hj), ht jb hj]; simp
    rw [this] at hc; exact Bool.false_ne_true hc.symm
  · exact hc

/-- **Clean clear through a routed feedback, any pin order.** -/
theorem cq_clean_reset_gen {p : DelayPar} {c : ℚ} {g : Gate} {src : Nat → Nat} {arcs : Nat → List Arc}
    {S : Nat} {x : Beh} (hg : CGateOK p c g src arcs S x) (R : Roles)
    (hk : R.r1 < g.k ∧ R.r2 < g.k ∧ R.fb < g.k ∧ R.rst < g.k ∧ R.a0 < g.k)
    (hne : R.r1 ≠ R.fb ∧ R.r2 ≠ R.fb ∧ R.rst ≠ R.fb ∧ R.a0 ≠ R.fb)
    (htk : ∀ jb ∈ R.tied, jb.1 < g.k ∧ jb.1 ≠ R.fb)
    (hreset : ∀ v : Nat → Bool, v R.r1 = false → v R.r2 = true → v R.rst = false → v R.a0 = false →
      (∀ jb ∈ R.tied, v jb.1 = jb.2) → g.init.testBit (addr g.k v) = false)
    (hzconf : ∀ v : Nat → Bool, v R.r2 = true → v R.fb = false → v R.rst = false →
      (∀ jb ∈ R.tied, v jb.1 = jb.2) → g.init.testBit (addr g.k v) = false)
    (hfb : src R.fb = g.out)
    {lo hi : Nat → Nat} (hb : CBands p c g.k arcs lo hi) (hlo : 1 ≤ lo R.fb) {s e e' : Nat}
    (hs : S ≤ s) (hlong : s + hi R.fb ≤ e + 1) (hee : e ≤ e')
    (htied : ∀ jb ∈ R.tied, OnReads x lo hi jb.1 (src jb.1) jb.2 s e')
    (hr1 : OnReads x lo hi R.r1 (src R.r1) false s e)
    (hr2 : OnReads x lo hi R.r2 (src R.r2) true s e')
    (hrs : OnReads x lo hi R.rst (src R.rst) false s e')
    (ha0 : OnReads x lo hi R.a0 (src R.a0) false s e) :
    ∀ t, s ≤ t → t ≤ e' → x g.out t = false := by
  apply cfb_switch hg hb (j := R.fb) hk.2.2.1 hfb hlo hs hlong
  · intro t h1 h2 v hv
    exact hreset v (cvisible_val hv hk.1 hne.1 h1 h2 hr1)
      (cvisible_val hv hk.2.1 hne.2.1 h1 (by omega) hr2)
      (cvisible_val hv hk.2.2.2.1 hne.2.2.1 h1 (by omega) hrs)
      (cvisible_val hv hk.2.2.2.2 hne.2.2.2 h1 h2 ha0)
      (fun jb hj => cvisible_val hv (htk jb hj).1 (htk jb hj).2 h1 (by omega) (htied jb hj))
  · intro t h1 h2 v hv2 hv
    exact hzconf v (cvisible_val hv hk.2.1 hne.2.1 (by omega) h2 hr2) hv2
      (cvisible_val hv hk.2.2.2.1 hne.2.2.1 (by omega) h2 hrs)
      (fun jb hj => cvisible_val hv (htk jb hj).1 (htk jb hj).2 (by omega) h2 (htied jb hj))

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem arows_reset_ok : arows.all (fun r => resetFact r.g.k r.g.init r.R && zconfFact r.g.k r.g.init r.R) = true := by
  decide +kernel

/-- **Separated clears are decided cleanly, for THE target's nine arbiters, in every behaviour of the circuit.** -/
theorem target_ps_arb_clean_reset {p : DelayPar} (hp : Sane p) {x : Beh} (hb : Behaves p (circuit net boundary) x) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ r ∈ arows, ∀ s e e' : Nat, r.S p ≤ s → s + r.hi p c r.R.fb ≤ e + 1 → e ≤ e' →
      1 ≤ r.lo p c r.R.fb →
      OnReads x (r.lo p c) (r.hi p c) r.R.r1 (r.src r.R.r1) false s e →
      OnReads x (r.lo p c) (r.hi p c) r.R.r2 (r.src r.R.r2) true s e' →
      OnReads x (r.lo p c) (r.hi p c) r.R.rst (r.src r.R.rst) false s e' →
      OnReads x (r.lo p c) (r.hi p c) r.R.a0 (r.src r.R.a0) false s e →
      ∀ t, s ≤ t → t ≤ e' → x r.q t = false := by
  obtain ⟨c, hc0, hc1, hcol⟩ := view_collapse hp hb (arows.map fun r => (r.q, r.pins)) (by
    have hL := arows_ok
    simp only [List.all_map, List.all_eq_true] at hL ⊢
    intro r hr
    have := hL r hr
    simp only [arowOK, Bool.and_eq_true] at this
    exact this.1.1.2)
  refine ⟨c, hc0, hc1, fun r hr s e e' hs hlong hee hlo h1 h2 h3 h4 => ?_⟩
  have hok : arowOK r = true := by have := arows_ok; simp only [List.all_eq_true] at this; exact this r hr
  have hrf : (resetFact r.g.k r.g.init r.R && zconfFact r.g.k r.g.init r.R) = true := by
    have := arows_reset_ok; simp only [List.all_eq_true] at this; exact this r hr
  simp only [Bool.and_eq_true] at hrf
  simp only [arowOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, bne_iff_ne, ne_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hk, k1⟩, k2⟩, k3⟩, k4⟩, k5⟩, n1⟩, n2⟩, n3⟩, n4⟩, ht⟩, -⟩, -⟩, -⟩, hfb⟩, hout⟩ := hok
  have hg : CGateOK p c r.g r.src r.arcs (r.S p) x := hcol _ (List.mem_map.mpr ⟨r, hr, rfl⟩)
  have hout' : r.g.out = r.q := hout
  have hfb' : r.src r.R.fb = r.g.out := by rw [ArbViewPS.src_eq r (by omega), hfb, hout']
  have htk : ∀ jb ∈ r.R.tied, jb.1 < r.g.k ∧ jb.1 ≠ r.R.fb := fun jb hj => ⟨(ht jb hj).1.1, (ht jb hj).1.2⟩
  have key := cq_clean_reset_gen hg r.R ⟨k1, k2, k3, k4, k5⟩ ⟨n1, n2, n3, n4⟩ htk
    (hreset_of_fact hrf.1 ⟨k1, k2, k4, k5⟩ (fun jb hj => (htk jb hj).1))
    (hzconf_of_fact hrf.2 ⟨k2, k3, k4⟩ (fun jb hj => (htk jb hj).1)) hfb' (cbands_of_sums r.arcs) hlo hs hlong hee
    (fun jb hj t u _ _ _ _ => by
      have h := (ht jb hj).2
      simp only [constAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨hs1, hs2⟩, hs3⟩, hs4⟩, hs5⟩ := h
      rw [ArbViewPS.src_eq r (by have := (htk jb hj).1; omega), const_hold hb hs1 hs2 hs3 hs4 u, hs5])
    h1 h2 h3 h4
  rw [hout'] at key
  exact key

end Formal.Cells.ArbViewPSReset
