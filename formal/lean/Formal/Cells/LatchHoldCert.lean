import Formal.Cells.CertRaceAll
import Formal.Cells.LatchView

/-!
# Formal.Cells.LatchHoldCert — a latch's hold window from a chain certificate (every behaviour)

Shard B, 2026-11-07.

## Problem, plainly
`LatchView.target_latch_close` needs, besides setup and width, the latch's HOLD window: the data source keeps the
captured value until `τ + hi e` (τ = the first time the enable source shows "closed", `hi e` = the enable pin's upper
band). In a bundled-data pipeline the next data value is released only in response to the close itself, through the
controller's acknowledge path. Show, in every behaviour of THE circuit at g = 1 and κ ≤ 83/200, from a chain hold
certificate whose cause is the latch's enable source and whose last row is the latch's data source, that the data
source keeps its value up to `τ + hi e`.

## Proved (standard axioms)
* `margin_succ`: `A·(ΣFAST_MAX(loop) + 1) ≤ B·ΣFAST_MIN(path)` and the same with SLOW give, for g = 1, every
  κ ≥ 0 with `(1+κ)·B ≤ A·(1-κ)` (B > 0) and every corner, `Σ hi(loop) + 1 ≤ Σ lo(path)` (integer window ends). Each
  row carries its own (A, B), so its own κ range: κ ≤ (A - B)/(A + B).
* `latch_hold`: certificate (certOK, single path, chain shape) + the two facts on (enable-pin arcs, path arcs) +
  the certificate's value premises with the cause showing its old value on `[a, e]`: the last row's node shows its
  value on `[its window start, e + 1 + hi e]`.
* `LatchHoldRow`, `latchHoldOK`, `latch_hold_row`: a checkable row (certificate + latch row `LRow`; checks: `lrowOK`,
  the enable pin reads the cause, the cause's old value is the open value, the data pin reads the last row's node,
  the two arc-sum facts) gives the hold window in `target_latch_close`'s form, with `τ = e + 1`.
* `latch_row`: `target_latch_close` for one row at a given collapsed relation (same proof).
* `target_latch_holds_of`: for a list of checked rows, one corner for all certificate rows and latches (one
  `view_collapse`): the latch holds its data value on `[A, E' + lo e]` with the HOLD half of the data window and the
  enable's OPEN window discharged (from the certificate and its cause premise); what remains is the certificate's
  premises, the enable closed on `[τ, E']`, the setup half of the data window and the latch's own inequalities.

## Not shown
Which certificates exist (Python: ctlcert.py on simb.py dumps); the premises (static side inputs, memory rows, the
enable source showing "open" on `[a, e]`).
-/

namespace Formal.Cells.LatchHoldCert
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecChain Formal.Cells.CertPS Formal.Cells.RaceCertPS
  Formal.Cells.CertMarginPS Formal.Cells.RaceCornersPS Formal.Cells.CertRaceAll Formal.Cells.LatchView
  Formal.Cells.SpecCElemFact

/-- **Margin with one step to spare** (g = 1, κ ≤ 83/200, every corner). -/
theorem margin_succ {κ c : ℚ} (hk0 : 0 ≤ κ) {A B : Nat} (hB0 : 0 < B)
    (hk : (1 + κ) * (B : ℚ) ≤ (A : ℚ) * (1 - κ)) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    {path loop : List Arc} (h1 : A * (sFmax loop + 1) ≤ B * sFmin path)
    (h2 : A * (sSmax loop + 1) ≤ B * sSmin path) :
    (loop.map (Formal.Cells.Ua1Static.hi 1 κ c)).sum.toNat + 1 ≤
      (path.map (Formal.Cells.Ua1Static.lo 1 κ c)).sum.toNat := by
  have hBq : (0 : ℚ) < B := by exact_mod_cast hB0
  have hA0 : (0 : ℚ) ≤ A := by positivity
  have hk1 : κ < 1 := by
    by_contra hc
    rw [not_lt] at hc
    have : (A : ℚ) * (1 - κ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hA0 (by linarith)
    nlinarith
  have u := hi_sum_le hk0 hc0 hc1 loop
  have l := lo_sum_ge (κ := κ) (by linarith) hc0 hc1 path
  have q1 : (A : ℚ) * ((sFmax loop : ℚ) + 1) ≤ B * (sFmin path : ℚ) := by exact_mod_cast h1
  have q2 : (A : ℚ) * ((sSmax loop : ℚ) + 1) ≤ B * (sSmin path : ℚ) := by exact_mod_cast h2
  have f1 : (0 : ℚ) ≤ sFmax loop := by positivity
  have f2 : (0 : ℚ) ≤ sSmax loop := by positivity
  set X : ℚ := (1 - c) * (sFmax loop : ℚ) + c * (sSmax loop : ℚ) with hX
  set Y : ℚ := (1 - c) * (sFmin path : ℚ) + c * (sSmin path : ℚ) with hY
  have hX0 : 0 ≤ X := by rw [hX]; have : (0 : ℚ) ≤ 1 - c := by linarith
                         positivity
  have a1 := mul_le_mul_of_nonneg_left q1 (by linarith : (0 : ℚ) ≤ 1 - c)
  have a2 := mul_le_mul_of_nonneg_left q2 hc0
  have hA : (A : ℚ) * (X + 1) ≤ B * Y := by rw [hX, hY]; nlinarith
  have hB : (1 + κ) * X + 1 ≤ (1 - κ) * Y := by
    have b1 := mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℚ) ≤ 1 - κ)
    have b2 := mul_le_mul_of_nonneg_right hk (by linarith : (0 : ℚ) ≤ X + 1)
    have b3 : (B : ℚ) * ((1 + κ) * X + 1) ≤ B * ((1 - κ) * Y) := by nlinarith
    exact le_of_mul_le_mul_left b3 hBq
  have : ((((loop.map (Formal.Cells.Ua1Static.hi 1 κ c)).sum.toNat : ℕ) : ℚ)) + 1 ≤
      ((((path.map (Formal.Cells.Ua1Static.lo 1 κ c)).sum.toNat : ℕ) : ℚ)) := by linarith
  exact_mod_cast this

/-- **A latch's hold window from a chain certificate** (every behaviour, g = 1, κ ≤ 83/200, at the corner `c` of the
collapsed relations `G`). With the certificate's premises (the cause showing its old value on `[a, e]`, static nodes,
memory rows), the last row's node shows its value from its window start up to `e + 1 + hi e`. -/
theorem latch_hold {κ : ℚ} (hk0 : 0 ≤ κ) {A B : Nat} (hB0 : 0 < B) (hk : (1 + κ) * (B : ℚ) ≤ (A : ℚ) * (1 - κ))
    {x : Beh}
    (hb : Behaves ⟨1, κ⟩ (circuit net boundary) x) (P : Prem) (rows : List CRow) (r : LRow)
    (hok : certOK P rows = true) (hsp : singlePath rows = true) (hch : chainShape rows = true)
    (hn : 1 ≤ rows.length)
    (h1 : A * (sFmax (r.arcs r.e) + 1) ≤ B * sFmin (pathArcs rows))
    (h2 : A * (sSmax (r.arcs r.e) + 1) ≤ B * sSmin (pathArcs rows))
    {c : ℚ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (G : ∀ i, i < rows.length → CGateOK ⟨1, κ⟩ c (rows.getD i default).r.g (rows.getD i default).r.src
      (rows.getD i default).r.arcs ((rows.getD i default).r.S ⟨1, κ⟩) x)
    (a e : Nat) (E : Nat → Nat) (PS : Nat)
    (hcause : ∀ t, a ≤ t → t ≤ e → x P.cn t = P.cv)
    (hstat : ∀ k, k < P.sn.length → ∀ t, a ≤ t → t ≤ E k → x (P.sn.getD k 0) t = P.sv.getD k false)
    (hmem : ∀ i, i < rows.length → (rows.getD i default).r.mem = true →
      1 ≤ (rows.getD i default).r.lo ⟨1, κ⟩ c (rows.getD i default).r.fb ∧
      ∀ t, (win ⟨1, κ⟩ c a e E rows i).1 ≤ t + (rows.getD i default).r.hi ⟨1, κ⟩ c (rows.getD i default).r.fb →
        t < (win ⟨1, κ⟩ c a e E rows i).1 → x (rows.getD i default).r.q t = (rows.getD i default).r.w)
    (hPS : ∀ i, i < rows.length → psum ⟨1, κ⟩ c rows i ≤ PS) (hE : ∀ k, e + PS ≤ E k) (hB : e + PS ≤ BIG) :
    ∀ u, (win ⟨1, κ⟩ c a e E rows (rows.length - 1)).1 ≤ u → u ≤ e + 1 + r.hi ⟨1, κ⟩ c r.e →
      x (rows.getD (rows.length - 1) default).r.q u = (rows.getD (rows.length - 1) default).r.w := by
  intro u hu1 hu2
  have hw := win_end_ge (p := ⟨1, κ⟩) (c := c) P rows hok hsp a e E PS hPS hE hB (rows.length - 1) (by omega)
  have hpc := psum_chain (p := ⟨1, κ⟩) (c := c) rows hch rows.length hn le_rfl
  have hm := margin_succ hk0 hB0 hk hc0 hc1 h1 h2
  have hk1 : κ ≤ 1 := by
    have hBq : (0 : ℚ) < B := by exact_mod_cast hB0
    by_contra hc
    rw [not_le] at hc
    have : (A : ℚ) * (1 - κ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    nlinarith
  have hpath := toNat_sum_le (fun i => (rows.getD i default).r.arcs (pathPin (rows.getD i default)))
    (Formal.Cells.Ua1Static.lo 1 κ c) (lo_nonneg (by linarith) hc0 hc1) rows.length
  have hlo : ((pathArcs rows).map (Formal.Cells.Ua1Static.lo 1 κ c)).sum.toNat ≤ loSum ⟨1, κ⟩ c rows rows.length :=
    hpath
  have hhi : r.hi ⟨1, κ⟩ c r.e = ((r.arcs r.e).map (Formal.Cells.Ua1Static.hi 1 κ c)).sum.toNat := rfl
  exact cert_sound hb P rows hok G a e E hcause hstat hmem (rows.length - 1) (by omega) u hu1 (by omega)

/-- A latch-hold row: a certificate and the latch's row. -/
structure LatchHoldRow where
  pc : Prem × List CRow
  l : LRow
  kA : Nat   -- the row's margin ratio: valid for κ with (1+κ)·kB ≤ kA·(1-κ)
  kB : Nat

/-- The checks of a latch-hold row besides `certOK`: path shape, the latch row itself, its enable pin reads the cause
whose old value is the "open" value, its data pin reads the last row's node, and the two arc-sum facts. -/
def latchHoldOK (r : LatchHoldRow) : Bool :=
  singlePath r.pc.2 && chainShape r.pc.2 && decide (1 ≤ r.pc.2.length) && lrowOK r.l &&
  (r.l.pins.getD r.l.e ([], 0)).2 == r.pc.1.cn && (r.pc.1.cv ^^ r.l.pe) &&
  (r.l.pins.getD r.l.d ([], 0)).2 == (r.pc.2.getD (r.pc.2.length - 1) default).r.q &&
  decide (r.kA * (sFmax (r.l.arcs r.l.e) + 1) ≤ r.kB * sFmin (pathArcs r.pc.2)) &&
  decide (r.kA * (sSmax (r.l.arcs r.l.e) + 1) ≤ r.kB * sSmin (pathArcs r.pc.2)) && decide (0 < r.kB)

/-- **A checked latch-hold row gives the latch's hold window** in `target_latch_close`'s form: with `τ = e + 1` (the
enable source shows its "open" value up to `e`, by the cause premise), the data source shows the last row's value on
`[its window start, τ + hi e]`. -/
theorem latch_hold_row {r : LatchHoldRow} (hc : certOK r.pc.1 r.pc.2 = true) (hr : latchHoldOK r = true) {κ : ℚ}
    (hk0 : 0 ≤ κ) (hk : (1 + κ) * (r.kB : ℚ) ≤ (r.kA : ℚ) * (1 - κ)) {x : Beh}
    (hb : Behaves ⟨1, κ⟩ (circuit net boundary) x) {c : ℚ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1)
    (G : ∀ i, i < r.pc.2.length → CGateOK ⟨1, κ⟩ c (r.pc.2.getD i default).r.g (r.pc.2.getD i default).r.src
      (r.pc.2.getD i default).r.arcs ((r.pc.2.getD i default).r.S ⟨1, κ⟩) x)
    (a e : Nat) (E : Nat → Nat) (PS : Nat)
    (hcause : ∀ t, a ≤ t → t ≤ e → x r.pc.1.cn t = r.pc.1.cv)
    (hstat : ∀ k, k < r.pc.1.sn.length → ∀ t, a ≤ t → t ≤ E k → x (r.pc.1.sn.getD k 0) t = r.pc.1.sv.getD k false)
    (hmem : ∀ i, i < r.pc.2.length → (r.pc.2.getD i default).r.mem = true →
      1 ≤ (r.pc.2.getD i default).r.lo ⟨1, κ⟩ c (r.pc.2.getD i default).r.fb ∧
      ∀ t, (win ⟨1, κ⟩ c a e E r.pc.2 i).1 ≤ t + (r.pc.2.getD i default).r.hi ⟨1, κ⟩ c (r.pc.2.getD i default).r.fb →
        t < (win ⟨1, κ⟩ c a e E r.pc.2 i).1 → x (r.pc.2.getD i default).r.q t = (r.pc.2.getD i default).r.w)
    (hPS : ∀ i, i < r.pc.2.length → psum ⟨1, κ⟩ c r.pc.2 i ≤ PS) (hE : ∀ k, e + PS ≤ E k) (hB : e + PS ≤ BIG) :
    lrowOK r.l = true ∧ r.l.src r.l.e = r.pc.1.cn ∧ (r.pc.1.cv ^^ r.l.pe) = true ∧
    ∀ u, (win ⟨1, κ⟩ c a e E r.pc.2 (r.pc.2.length - 1)).1 ≤ u → u ≤ (e + 1) + r.l.hi ⟨1, κ⟩ c r.l.e →
      x (r.l.src r.l.d) u = (r.pc.2.getD (r.pc.2.length - 1) default).r.w := by
  simp only [latchHoldOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hr
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hsp, hch⟩, hn⟩, hl⟩, hen⟩, hpe⟩, hd⟩, h1⟩, h2⟩, hB0⟩ := hr
  have hl' := hl
  simp only [lrowOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hl'
  have hkk : r.l.g.k = r.l.pins.length := hl'.1.1.1.1.1.1.1.1.1.1.1.1.1
  have he : r.l.e < r.l.g.k := hl'.1.1.1.1.1.1.1.1.1.1.1.1.2
  have hdk : r.l.d < r.l.g.k := hl'.1.1.1.1.1.1.1.1.1.1.1.2
  refine ⟨hl, by rw [src_eq r.l (by omega), hen], hpe, fun u hu1 hu2 => ?_⟩
  rw [src_eq r.l (by omega), hd]
  exact latch_hold hk0 hB0 hk hb r.pc.1 r.pc.2 r.l hc hsp hch hn h1 h2 hc0 hc1 G a e E PS hcause hstat hmem hPS hE hB u
    hu1 (by omega)

/-- `target_latch_close` for one row, given its collapsed relation (so that a caller can fix the corner). -/
theorem latch_row {p : DelayPar} {c : ℚ} {x : Beh} (hb : Behaves p (circuit net boundary) x) (r : LRow)
    (hok : lrowOK r = true) (hg : CGateOK p c r.g r.src r.arcs (r.S p) x) :
    ∀ (τ E We Wd A H : Nat) (v : Bool), r.S p ≤ A →
      (∀ i, i < r.g.k → r.hi p c i ≤ H) → 1 ≤ r.lo p c r.j →
      (∀ t, A ≤ t + H → x CElemPS.rstNode t = false) →
      (∀ t, τ ≤ t + We → t < τ → (x (r.src r.e) t ^^ r.pe) = true) →
      (∀ t, τ ≤ t → t ≤ E → (x (r.src r.e) t ^^ r.pe) = false) →
      (∀ t, τ ≤ t + Wd → t ≤ τ + r.hi p c r.e → (x (r.src r.d) t ^^ r.pd) = v) →
      τ + r.hi p c r.e ≤ A + We → τ + r.hi p c r.d ≤ A + Wd → A + r.hi p c r.j ≤ τ + r.lo p c r.e →
      ∀ s, A ≤ s → s ≤ E + r.lo p c r.e → x r.q s = v := by
  intro τ E We Wd A H v hS hH hloj hrst hop hcl hdat hAe hAd hloop
  simp only [lrowOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    bne_iff_ne, ne_eq, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hk, he⟩, hd⟩, hj⟩, hed⟩, hej⟩, hdj⟩, -⟩, -⟩, hf⟩, -⟩, hfb⟩, hout⟩, hheld⟩ := hok
  have hout' : r.g.out = r.q := hout
  have hfb' : r.src r.j = r.g.out := by rw [src_eq r (by omega), hfb, hout']
  have key := Formal.Cells.SpecLatch.latch_close hg (Formal.Cells.SpecFbChain.cbands_of_sums r.arcs) he hd hj hed hej
    hdj hfb' hloj r.pe r.pd (fl r.held) (fl r.ov)
    (Formal.Cells.SpecLatchFact.hopen_of_lfact hf he hd) (Formal.Cells.SpecLatchFact.hclosed_of_lfact hf he hj)
    τ E We Wd A H v hH
    (fun i hi' hh t ht => by
      have h := hheld i hi'
      simp only [hh, Bool.not_true, Bool.false_or] at h
      rw [src_eq r (by omega)]
      simp only [lheldOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at h
      rcases h with ⟨hs, hov⟩ | ⟨⟨⟨⟨hs1, hs2⟩, hs3⟩, hs4⟩, hs5⟩
      · rw [hs, hov]; exact hrst t ht
      · rw [Formal.Cells.ViewPS.const_hold hb hs1 hs2 hs3 hs4 t, hs5])
    hop hcl hdat hS hAe hAd hloop
  rw [hout'] at key
  exact key

/-- **Latches close and hold with the hold window from a certificate** (every behaviour of THE circuit, g = 1,
κ ≤ 83/200, one corner for all rows). For each checked latch-hold row: with the certificate's premises (the enable
source shows its "open" value on `[a, e]`, static side inputs, memory rows), the enable closed on `[e + 1, E']`, the
data source showing `v` before the hold window (setup part, `[τ - Wd, window start)`, τ = e + 1), the last row's value
matching `v`, `a + We ≤ τ`, the latch's own window inequalities and the reset low: the latch holds `v` on
`[A, E' + lo e]`. Compared with `target_latch_close`, the hold half of the data window and the open window are
discharged. -/
theorem target_latch_holds_of (L : List LatchHoldRow) (hL : ∀ r ∈ L, certOK r.pc.1 r.pc.2 = true ∧ latchHoldOK r = true)
    {κ : ℚ} (hk0 : 0 ≤ κ) (hk1 : κ ≤ 1) {x : Beh} (hb : Behaves ⟨1, κ⟩ (circuit net boundary) x) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ r ∈ L, (1 + κ) * (r.kB : ℚ) ≤ (r.kA : ℚ) * (1 - κ) →
      ∀ (a e : Nat) (E : Nat → Nat) (PS : Nat),
      (∀ t, a ≤ t → t ≤ e → x r.pc.1.cn t = r.pc.1.cv) →
      (∀ k, k < r.pc.1.sn.length → ∀ t, a ≤ t → t ≤ E k → x (r.pc.1.sn.getD k 0) t = r.pc.1.sv.getD k false) →
      (∀ i, i < r.pc.2.length → (r.pc.2.getD i default).r.mem = true →
        1 ≤ (r.pc.2.getD i default).r.lo ⟨1, κ⟩ c (r.pc.2.getD i default).r.fb ∧
        ∀ t, (win ⟨1, κ⟩ c a e E r.pc.2 i).1 ≤ t + (r.pc.2.getD i default).r.hi ⟨1, κ⟩ c (r.pc.2.getD i default).r.fb →
          t < (win ⟨1, κ⟩ c a e E r.pc.2 i).1 → x (r.pc.2.getD i default).r.q t = (r.pc.2.getD i default).r.w) →
      (∀ i, i < r.pc.2.length → psum ⟨1, κ⟩ c r.pc.2 i ≤ PS) → (∀ k, e + PS ≤ E k) → e + PS ≤ BIG →
      ∀ (E' We Wd A H : Nat) (v : Bool), r.l.S ⟨1, κ⟩ ≤ A →
      (∀ i, i < r.l.g.k → r.l.hi ⟨1, κ⟩ c i ≤ H) → 1 ≤ r.l.lo ⟨1, κ⟩ c r.l.j →
      (∀ t, A ≤ t + H → x CElemPS.rstNode t = false) →
      a + We ≤ e + 1 →
      (∀ t, e + 1 ≤ t → t ≤ E' → (x (r.l.src r.l.e) t ^^ r.l.pe) = false) →
      (∀ t, e + 1 ≤ t + Wd → t < (win ⟨1, κ⟩ c a e E r.pc.2 (r.pc.2.length - 1)).1 →
        (x (r.l.src r.l.d) t ^^ r.l.pd) = v) →
      ((r.pc.2.getD (r.pc.2.length - 1) default).r.w ^^ r.l.pd) = v →
      (e + 1) + r.l.hi ⟨1, κ⟩ c r.l.e ≤ A + We → (e + 1) + r.l.hi ⟨1, κ⟩ c r.l.d ≤ A + Wd →
      A + r.l.hi ⟨1, κ⟩ c r.l.j ≤ (e + 1) + r.l.lo ⟨1, κ⟩ c r.l.e →
      ∀ s, A ≤ s → s ≤ E' + r.l.lo ⟨1, κ⟩ c r.l.e → x r.l.q s = v := by
  have hp : Formal.Timing.SpecSettle.Sane ⟨1, κ⟩ := ⟨hk0, hk1, by norm_num⟩
  obtain ⟨c, hc0, hc1, hcol⟩ := Formal.Cells.ViewPS.view_collapse hp hb
    ((L.flatMap fun r => (List.range r.pc.2.length).map fun i =>
      ((r.pc.2.getD i default).r.q, (r.pc.2.getD i default).r.pins)) ++ L.map fun r => (r.l.q, r.l.pins)) (by
      simp only [List.all_append, Bool.and_eq_true, List.all_eq_true, List.mem_flatMap, List.mem_map, List.mem_range]
      refine ⟨?_, ?_⟩
      · rintro e ⟨r, hr, i, hi, rfl⟩
        have hc := (hL r hr).1
        simp only [certOK, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hc
        exact (krow_facts hb (hc i hi).1).2.2.2.2.2
      · rintro e ⟨r, hr, rfl⟩
        have hl := (hL r hr).2
        simp only [latchHoldOK, Bool.and_eq_true] at hl
        have h := hl.1.1.1.1.1.1.2
        simp only [lrowOK, Bool.and_eq_true] at h
        exact h.1.1.1.2)
  refine ⟨c, hc0, hc1, fun r hr hk a e E PS h1 h2 h3 h4 h5 h6 E' We Wd A H v hS hH hloj hrst haW hcl hset hw hAe hAd
    hloop => ?_⟩
  have G : ∀ i, i < r.pc.2.length → CGateOK ⟨1, κ⟩ c (r.pc.2.getD i default).r.g (r.pc.2.getD i default).r.src
      (r.pc.2.getD i default).r.arcs ((r.pc.2.getD i default).r.S ⟨1, κ⟩) x := fun i hi =>
    hcol _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨r, hr, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩⟩))
  have hg : CGateOK ⟨1, κ⟩ c r.l.g r.l.src r.l.arcs (r.l.S ⟨1, κ⟩) x :=
    hcol _ (List.mem_append_right _ (List.mem_map.mpr ⟨r, hr, rfl⟩))
  obtain ⟨hl, hsrc, hpe, hhold⟩ := latch_hold_row (hL r hr).1 (hL r hr).2 hk0 hk hb hc0 hc1 G a e E PS h1 h2 h3 h4 h5 h6
  refine latch_row hb r.l hl hg (e + 1) E' We Wd A H v hS hH hloj hrst (fun t t1 t2 => ?_) hcl (fun t t1 t2 => ?_)
    hAe hAd hloop
  · rw [hsrc, h1 t (by omega) (by omega)]; exact hpe
  · by_cases hlt : t < (win ⟨1, κ⟩ c a e E r.pc.2 (r.pc.2.length - 1)).1
    · exact hset t t1 hlt
    · rw [hhold t (by omega) t2]; exact hw

end Formal.Cells.LatchHoldCert
