import Formal.Cells.LatchHoldCert

/-!
# Formal.Cells.SelectHold — hold windows of latches that capture through a select mux (shard B, 2026-11-15)

**Problem, plainly.** (PROGRAM.md 2026-11-15, item 4; research's rule H for select links.) On THE target 1,070
latch bits capture the output of a 2:1 data mux (`bd_mux`'s datamux: `z = s ? y : x`) whose select `s` and inputs
`x`, `y` are latches of OTHER links (`tools-B/select/`, 933 of them `umux*.udat` with select and inputs latches).
The existing hold rows (`LatchHoldCert`) follow ONE chain from the latch's enable source to its data source; a mux
output depends on two nodes that both move. When does the mux output keep the captured value until the latch has
surely closed, for every delay in the band?

**Proved.**
* `SelRow`, `selOK`: a checkable row: two single-path chain certificates from the latch's enable source (the close
  event), one ending at the select node, one at the selected input; a mux row (`KRow`, not a storage node) whose
  two controlling pins read those two nodes with the values the certificates hold and force the mux's INIT
  (`kfact`, the other pins free); the latch row (`LRow`) whose data pin reads the mux; the two margin facts per
  chain, each with its own κ range `(1+κ)·kB ≤ kA·(1-κ)`.
* `select_hold_row` (g = 1, every corner, every behaviour of THE circuit): with both certificates' premises (cause
  showing the open value on `[a, e]`, static nodes, memory rows), the latch's data source shows the mux row's value
  on `[start, (e + 1) + hi e]`, where `start` is the later of the two chains' window starts plus the mux pin's upper
  band (and the mux's start). That is the hold half (`τ = e + 1`) of `LatchView.target_latch_close`'s data window.
  The deselected mux input is unconstrained (it may glitch).

**Not shown.** Any row for THE target (Python emitter not written); the certificates' own premises; the setup
half (rule I); completeness (every capture has a row).
-/

namespace Formal.Cells.SelectHold
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecChain Formal.Cells.CertPS Formal.Cells.RaceCertPS
  Formal.Cells.CertMarginPS Formal.Cells.RaceCornersPS Formal.Cells.CertRaceAll Formal.Cells.LatchView
  Formal.Cells.SpecCElemFact Formal.Cells.LatchHoldCert

/-- A select-hold row. -/
structure SelRow where
  c1 : Prem × List CRow   -- enable source → select node
  c2 : Prem × List CRow   -- enable source → selected input
  m : KRow                -- the mux: controlling pins p1 (select), p2 (selected input)
  p1 : Nat
  p2 : Nat
  l : LRow                -- the capturing latch
  kA1 : Nat
  kB1 : Nat
  kA2 : Nat
  kB2 : Nat

/-- The last row of a certificate. -/
def lastR (rows : List CRow) : CRow := rows.getD (rows.length - 1) default

def chainOK (pc : Prem × List CRow) : Bool :=
  singlePath pc.2 && chainShape pc.2 && decide (1 ≤ pc.2.length)

/-- The checks of a select-hold row besides the two `certOK`s. -/
def selOK (r : SelRow) : Bool :=
  chainOK r.c1 && chainOK r.c2 && lrowOK r.l && krowOK r.m && !r.m.mem && r.m.P == [r.p1, r.p2] &&
  decide (r.p1 < r.m.pins.length) && decide (r.p2 < r.m.pins.length) &&
  (r.m.pins.getD r.p1 ([], 0)).2 == (lastR r.c1.2).r.q && fl r.m.bv r.p1 == (lastR r.c1.2).r.w &&
  (r.m.pins.getD r.p2 ([], 0)).2 == (lastR r.c2.2).r.q && fl r.m.bv r.p2 == (lastR r.c2.2).r.w &&
  (r.l.pins.getD r.l.d ([], 0)).2 == r.m.q &&
  (r.l.pins.getD r.l.e ([], 0)).2 == r.c1.1.cn && r.c2.1.cn == r.c1.1.cn && r.c2.1.cv == r.c1.1.cv &&
  (r.c1.1.cv ^^ r.l.pe) &&
  decide (r.kA1 * (sFmax (r.l.arcs r.l.e) + 1) ≤ r.kB1 * sFmin (pathArcs r.c1.2)) &&
  decide (r.kA1 * (sSmax (r.l.arcs r.l.e) + 1) ≤ r.kB1 * sSmin (pathArcs r.c1.2)) && decide (0 < r.kB1) &&
  decide (r.kA2 * (sFmax (r.l.arcs r.l.e) + 1) ≤ r.kB2 * sFmin (pathArcs r.c2.2)) &&
  decide (r.kA2 * (sSmax (r.l.arcs r.l.e) + 1) ≤ r.kB2 * sSmin (pathArcs r.c2.2)) && decide (0 < r.kB2)

/-- **A checked select-hold row gives the latch's hold window through the mux.** -/
theorem select_hold_row {r : SelRow} (hc1 : certOK r.c1.1 r.c1.2 = true) (hc2 : certOK r.c2.1 r.c2.2 = true)
    (hr : selOK r = true) {κ : ℚ} (hk0 : 0 ≤ κ)
    (hk1 : (1 + κ) * (r.kB1 : ℚ) ≤ (r.kA1 : ℚ) * (1 - κ)) (hk2 : (1 + κ) * (r.kB2 : ℚ) ≤ (r.kA2 : ℚ) * (1 - κ))
    {x : Beh} (hb : Behaves ⟨1, κ⟩ (circuit net boundary) x) {c : ℚ} (hcc0 : 0 ≤ c) (hcc1 : c ≤ 1)
    (G1 : ∀ i, i < r.c1.2.length → CGateOK ⟨1, κ⟩ c (r.c1.2.getD i default).r.g (r.c1.2.getD i default).r.src
      (r.c1.2.getD i default).r.arcs ((r.c1.2.getD i default).r.S ⟨1, κ⟩) x)
    (G2 : ∀ i, i < r.c2.2.length → CGateOK ⟨1, κ⟩ c (r.c2.2.getD i default).r.g (r.c2.2.getD i default).r.src
      (r.c2.2.getD i default).r.arcs ((r.c2.2.getD i default).r.S ⟨1, κ⟩) x)
    (Gm : CGateOK ⟨1, κ⟩ c r.m.g r.m.src r.m.arcs (r.m.S ⟨1, κ⟩) x)
    (a e : Nat) (E1 E2 : Nat → Nat) (PS1 PS2 : Nat)
    (hcause : ∀ t, a ≤ t → t ≤ e → x r.c1.1.cn t = r.c1.1.cv)
    (hstat1 : ∀ k, k < r.c1.1.sn.length → ∀ t, a ≤ t → t ≤ E1 k → x (r.c1.1.sn.getD k 0) t = r.c1.1.sv.getD k false)
    (hstat2 : ∀ k, k < r.c2.1.sn.length → ∀ t, a ≤ t → t ≤ E2 k → x (r.c2.1.sn.getD k 0) t = r.c2.1.sv.getD k false)
    (hmem1 : ∀ i, i < r.c1.2.length → (r.c1.2.getD i default).r.mem = true →
      1 ≤ (r.c1.2.getD i default).r.lo ⟨1, κ⟩ c (r.c1.2.getD i default).r.fb ∧
      ∀ t, (win ⟨1, κ⟩ c a e E1 r.c1.2 i).1 ≤ t + (r.c1.2.getD i default).r.hi ⟨1, κ⟩ c (r.c1.2.getD i default).r.fb →
        t < (win ⟨1, κ⟩ c a e E1 r.c1.2 i).1 → x (r.c1.2.getD i default).r.q t = (r.c1.2.getD i default).r.w)
    (hmem2 : ∀ i, i < r.c2.2.length → (r.c2.2.getD i default).r.mem = true →
      1 ≤ (r.c2.2.getD i default).r.lo ⟨1, κ⟩ c (r.c2.2.getD i default).r.fb ∧
      ∀ t, (win ⟨1, κ⟩ c a e E2 r.c2.2 i).1 ≤ t + (r.c2.2.getD i default).r.hi ⟨1, κ⟩ c (r.c2.2.getD i default).r.fb →
        t < (win ⟨1, κ⟩ c a e E2 r.c2.2 i).1 → x (r.c2.2.getD i default).r.q t = (r.c2.2.getD i default).r.w)
    (hPS1 : ∀ i, i < r.c1.2.length → psum ⟨1, κ⟩ c r.c1.2 i ≤ PS1) (hE1 : ∀ k, e + PS1 ≤ E1 k) (hB1 : e + PS1 ≤ BIG)
    (hPS2 : ∀ i, i < r.c2.2.length → psum ⟨1, κ⟩ c r.c2.2 i ≤ PS2) (hE2 : ∀ k, e + PS2 ≤ E2 k) (hB2 : e + PS2 ≤ BIG) :
    lrowOK r.l = true ∧ r.l.src r.l.e = r.c1.1.cn ∧ (r.c1.1.cv ^^ r.l.pe) = true ∧
    ∀ u, max (r.m.S ⟨1, κ⟩)
        (max ((win ⟨1, κ⟩ c a e E1 r.c1.2 (r.c1.2.length - 1)).1 + r.m.hi ⟨1, κ⟩ c r.p1)
          ((win ⟨1, κ⟩ c a e E2 r.c2.2 (r.c2.2.length - 1)).1 + r.m.hi ⟨1, κ⟩ c r.p2)) ≤ u →
      u ≤ (e + 1) + r.l.hi ⟨1, κ⟩ c r.l.e → x (r.l.src r.l.d) u = r.m.w := by
  simp only [selOK, chainOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true'] at hr
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsp1, hch1⟩, hn1⟩, ⟨⟨hsp2, hch2⟩, hn2⟩⟩, hl⟩, hm⟩, hmf⟩, hP⟩, hp1⟩, hp2⟩, hq1⟩, hw1⟩, hq2⟩, hw2⟩, hd⟩, hen⟩, hcn⟩, hcv⟩, hpe⟩, f11⟩, f12⟩, hB01⟩, f21⟩, f22⟩, hB02⟩ := hr
  have hl' := hl
  simp only [lrowOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hl'
  have hkk : r.l.g.k = r.l.pins.length := hl'.1.1.1.1.1.1.1.1.1.1.1.1.1
  have he : r.l.e < r.l.g.k := hl'.1.1.1.1.1.1.1.1.1.1.1.1.2
  have hdk : r.l.d < r.l.g.k := hl'.1.1.1.1.1.1.1.1.1.1.1.2
  refine ⟨hl, by rw [src_eq r.l (by omega), hen], hpe, fun u hu1 hu2 => ?_⟩
  -- the two roots hold up to e + 1 + hi e
  have H1 := latch_hold hk0 hB01 hk1 hb r.c1.1 r.c1.2 r.l hc1 hsp1 hch1 hn1 f11 f12 hcc0 hcc1 G1 a e E1 PS1 hcause
    hstat1 hmem1 hPS1 hE1 hB1
  have hcause2 : ∀ t, a ≤ t → t ≤ e → x r.c2.1.cn t = r.c2.1.cv := by rw [hcn, hcv]; exact hcause
  have H2 := latch_hold hk0 hB02 hk2 hb r.c2.1 r.c2.2 r.l hc2 hsp2 hch2 hn2 f21 f22 hcc0 hcc1 G2 a e E2 PS2 hcause2
    hstat2 hmem2 hPS2 hE2 hB2
  -- the mux holds through both
  have hmux := krow_set (c := c) hb hm hmf Gm
    (fun j => if j = r.p1 then (win ⟨1, κ⟩ c a e E1 r.c1.2 (r.c1.2.length - 1)).1
      else (win ⟨1, κ⟩ c a e E2 r.c2.2 (r.c2.2.length - 1)).1)
    (fun _ => e + 1 + r.l.hi ⟨1, κ⟩ c r.l.e)
    (by
      intro j hj t ht1 ht2
      rw [hP] at hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      by_cases hj1 : j = r.p1
      · subst hj1
        simp only [ite_true] at ht1
        rw [ksrc_eq r.m hp1, hq1, hw1]
        exact H1 t ht1 ht2
      · have hj2 : j = r.p2 := by tauto
        subst hj2
        simp only [hj1, ite_false] at ht1
        rw [ksrc_eq r.m hp2, hq2, hw2]
        exact H2 t ht1 ht2)
  rw [src_eq r.l (by omega), hd]
  refine hmux u (le_trans (le_max_left _ _) hu1) (fun j hj => ?_)
  rw [hP] at hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  by_cases hj1 : j = r.p1
  · subst hj1
    simp only [ite_true]
    refine ⟨?_, by omega⟩
    have := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hu1)
    exact this
  · have hj2 : j = r.p2 := by tauto
    subst hj2
    simp only [hj1, ite_false]
    refine ⟨?_, by omega⟩
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hu1)

end Formal.Cells.SelectHold
