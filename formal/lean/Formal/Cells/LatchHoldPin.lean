import Formal.Cells.LatchHoldCert

/-!
# Formal.Cells.LatchHoldPin — latch hold windows at the data PIN (sharper than LatchHoldCert)

Shard B, 2026-11-07.

## Problem, plainly
`SpecLatch.latch_close` asks the data SOURCE to keep its value until `τ + hi e`. But the latch only uses a data read
while its enable read still sees "open", i.e. at output times `s < τ + hi e`, and such a read looks at the source at
`s - (data read delay) ≤ s - lo d`. So the source only has to hold while `t + lo d < τ + hi e`. With this, the hold
margin of a certificate becomes `Σ hi(enable arcs) ≤ Σ lo(path arcs) + lo(data arcs)` (the `race_holds` shape), which
for the binding latch SLICE_X32Y90.C O6 raises the κ range from 0.291 to about 0.44 (Python estimate from the sums).

## Proved (standard axioms)
* `latch_close_pin`: `SpecLatch.latch_close` with the data premise `∀ t, τ ≤ t + Wd → t + lo d < τ + hi e → …`
  (same proof; the weaker premise is what the proof uses).
* `margin_le`: `kA·ΣFAST_MAX(loop) ≤ kB·ΣFAST_MIN(path)` (and SLOW), `0 < kB`, `(1+κ)·kB ≤ kA·(1-κ)`:
  `Σ hi(loop) ≤ Σ lo(path)` (integer window ends, every corner).
* `latch_hold_pin`, `latchHoldPinOK`, `latch_hold_pin_row`: as in LatchHoldCert with the facts on
  (path arcs ++ the latch's data-pin arcs) vs (enable-pin arcs), no +1: the data source shows its value at every
  `u ≥` the window start with `u + lo d < τ + hi e`, τ = e + 1.
* `latch_row_pin`, `target_latch_holds_pin_of`: the list theorem of LatchHoldCert at this sharper data window.

## Not shown
As in LatchHoldCert: the certificates' local premises, the setup half.
-/

namespace Formal.Cells.LatchHoldPin
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecChain Formal.Cells.CertPS Formal.Cells.RaceCertPS
  Formal.Cells.CertMarginPS Formal.Cells.RaceCornersPS Formal.Cells.CertRaceAll Formal.Cells.LatchView
  Formal.Cells.SpecCElemFact Formal.Cells.SpecFbChain Formal.Cells.LatchHoldCert

/-- **A routed latch closes cleanly and holds; data needed only while a read can still use it.** -/
theorem latch_close_pin {p : DelayPar} {c : ℚ} {g : Gate} {src : Nat → Nat} {arcs : Nat → List Arc}
    {S : Nat} {x : Beh} (hg : CGateOK p c g src arcs S x) {lo hi : Nat → Nat}
    (hb : CBands p c g.k arcs lo hi)
    {e d j : Nat} (he : e < g.k) (hd : d < g.k) (hj : j < g.k) (hed : e ≠ d) (hej : e ≠ j) (hdj : d ≠ j)
    (hfb : src j = g.out) (hloj : 1 ≤ lo j)
    (pe pd : Bool) (held : Nat → Bool) (ov : Nat → Bool)
    (hopen : ∀ v : Nat → Bool, (v e ^^ pe) = true →
      (∀ i, i < g.k → held i = true → v i = ov i) → g.init.testBit (addr g.k v) = (v d ^^ pd))
    (hclosed : ∀ v : Nat → Bool, (v e ^^ pe) = false →
      (∀ i, i < g.k → held i = true → v i = ov i) → g.init.testBit (addr g.k v) = v j)
    (τ E We Wd A H : Nat) (v : Bool) (hH : ∀ i, i < g.k → hi i ≤ H)
    (hheld : ∀ i, i < g.k → held i = true → ∀ t, A ≤ t + H → x (src i) t = ov i)
    (hopenW : ∀ t, τ ≤ t + We → t < τ → (x (src e) t ^^ pe) = true)
    (hclosedW : ∀ t, τ ≤ t → t ≤ E → (x (src e) t ^^ pe) = false)
    (hdata : ∀ t, τ ≤ t + Wd → t + lo d < τ + hi e → (x (src d) t ^^ pd) = v)
    (hAS : S ≤ A) (hAe : τ + hi e ≤ A + We) (hAd : τ + hi d ≤ A + Wd) (hloop : A + hi j ≤ τ + lo e) :
    ∀ s, A ≤ s → s ≤ E + lo e → x g.out s = v := by
  obtain ⟨F, -, hF⟩ := hg
  have hrd : ∀ t, S ≤ t → ∀ i, i < g.k → lo i ≤ t - F i t ∧ t - F i t ≤ hi i ∧ F i t ≤ t := by
    intro t ht i hi'
    obtain ⟨hr, -⟩ := hF t ht
    have h1 := hr i hi'
    exact ⟨(hb i hi' _ h1.2).1, (hb i hi' _ h1.2).2, h1.1⟩
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro hAs hsE
  obtain ⟨-, hy⟩ := hF s (by omega)
  have hheldR : ∀ i, i < g.k → held i = true → x (src i) (F i s) = ov i := fun i hi' hh =>
    hheld i hi' hh _ (by have := hrd s (by omega) i hi'; have := hH i hi'; omega)
  have hre := hrd s (by omega) e he
  have hrdd := hrd s (by omega) d hd
  have hrj := hrd s (by omega) j hj
  -- the data read (whenever used) sees v
  have hdv : F e s < τ → (x (src d) (F d s) ^^ pd) = v := fun h => hdata _ (by omega) (by omega)
  by_cases hcl : τ ≤ F e s
  · -- the enable read sees it closed: the output is the feedback read, which is v by induction
    have hcr : (x (src e) (F e s) ^^ pe) = false := hclosedW _ hcl (by omega)
    rw [hy, hclosed _ hcr hheldR, hfb]
    exact ih (F j s) (by omega) (by omega) (by omega)
  · -- the enable read sees it open: the output is the data read
    have hor : (x (src e) (F e s) ^^ pe) = true := hopenW _ (by omega) (by omega)
    rw [hy, hopen _ hor hheldR]
    exact hdv (by omega)


/-- **Margin** (g = 1, every corner, κ in the row's range). -/
theorem margin_le {κ c : ℚ} (hk0 : 0 ≤ κ) {A B : Nat} (hB0 : 0 < B)
    (hk : (1 + κ) * (B : ℚ) ≤ (A : ℚ) * (1 - κ)) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    {path loop : List Arc} (h1 : A * sFmax loop ≤ B * sFmin path) (h2 : A * sSmax loop ≤ B * sSmin path) :
    (loop.map (Formal.Cells.Ua1Static.hi 1 κ c)).sum.toNat ≤ (path.map (Formal.Cells.Ua1Static.lo 1 κ c)).sum.toNat := by
  have hBq : (0 : ℚ) < B := by exact_mod_cast hB0
  have hA0 : (0 : ℚ) ≤ A := by positivity
  have hk1 : κ < 1 := by
    by_contra hc
    rw [not_lt] at hc
    have : (A : ℚ) * (1 - κ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hA0 (by linarith)
    nlinarith
  have u := hi_sum_le hk0 hc0 hc1 loop
  have l := lo_sum_ge (κ := κ) (by linarith) hc0 hc1 path
  have q1 : (A : ℚ) * (sFmax loop : ℚ) ≤ B * (sFmin path : ℚ) := by exact_mod_cast h1
  have q2 : (A : ℚ) * (sSmax loop : ℚ) ≤ B * (sSmin path : ℚ) := by exact_mod_cast h2
  have f1 : (0 : ℚ) ≤ sFmax loop := by positivity
  have f2 : (0 : ℚ) ≤ sSmax loop := by positivity
  set X : ℚ := (1 - c) * (sFmax loop : ℚ) + c * (sSmax loop : ℚ) with hX
  set Y : ℚ := (1 - c) * (sFmin path : ℚ) + c * (sSmin path : ℚ) with hY
  have hX0 : 0 ≤ X := by rw [hX]; have : (0 : ℚ) ≤ 1 - c := by linarith
                         positivity
  have a1 := mul_le_mul_of_nonneg_left q1 (by linarith : (0 : ℚ) ≤ 1 - c)
  have a2 := mul_le_mul_of_nonneg_left q2 hc0
  have hA : (A : ℚ) * X ≤ B * Y := by rw [hX, hY]; nlinarith
  have hB : (1 + κ) * X ≤ (1 - κ) * Y := by
    have b1 := mul_le_mul_of_nonneg_left hA (by linarith : (0 : ℚ) ≤ 1 - κ)
    have b2 := mul_le_mul_of_nonneg_right hk hX0
    have b3 : (B : ℚ) * ((1 + κ) * X) ≤ B * ((1 - κ) * Y) := by nlinarith
    exact le_of_mul_le_mul_left b3 hBq
  have : ((((loop.map (Formal.Cells.Ua1Static.hi 1 κ c)).sum.toNat : ℕ) : ℚ)) ≤
      ((((path.map (Formal.Cells.Ua1Static.lo 1 κ c)).sum.toNat : ℕ) : ℚ)) := by linarith
  exact_mod_cast this

/-- **A latch's data-pin hold window from a chain certificate.** -/
theorem latch_hold_pin {κ : ℚ} (hk0 : 0 ≤ κ) {A B : Nat} (hB0 : 0 < B)
    (hk : (1 + κ) * (B : ℚ) ≤ (A : ℚ) * (1 - κ)) {x : Beh}
    (hb : Behaves ⟨1, κ⟩ (circuit net boundary) x) (P : Prem) (rows : List CRow) (r : LRow)
    (hok : certOK P rows = true) (hsp : singlePath rows = true) (hch : chainShape rows = true)
    (hn : 1 ≤ rows.length)
    (h1 : A * sFmax (r.arcs r.e) ≤ B * sFmin (pathArcs rows ++ r.arcs r.d))
    (h2 : A * sSmax (r.arcs r.e) ≤ B * sSmin (pathArcs rows ++ r.arcs r.d))
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
    ∀ u, (win ⟨1, κ⟩ c a e E rows (rows.length - 1)).1 ≤ u → u + r.lo ⟨1, κ⟩ c r.d < e + 1 + r.hi ⟨1, κ⟩ c r.e →
      x (rows.getD (rows.length - 1) default).r.q u = (rows.getD (rows.length - 1) default).r.w := by
  intro u hu1 hu2
  have hk1 : κ ≤ 1 := by
    have hBq : (0 : ℚ) < B := by exact_mod_cast hB0
    by_contra hc
    rw [not_le] at hc
    have : (A : ℚ) * (1 - κ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    nlinarith
  have hw := win_end_ge (p := ⟨1, κ⟩) (c := c) P rows hok hsp a e E PS hPS hE hB (rows.length - 1) (by omega)
  have hpc := psum_chain (p := ⟨1, κ⟩) (c := c) rows hch rows.length hn le_rfl
  have hm := margin_le hk0 hB0 hk hc0 hc1 h1 h2
  have hsplit : (((pathArcs rows ++ r.arcs r.d).map (Formal.Cells.Ua1Static.lo 1 κ c)).sum.toNat) ≤
      ((pathArcs rows).map (Formal.Cells.Ua1Static.lo 1 κ c)).sum.toNat +
        ((r.arcs r.d).map (Formal.Cells.Ua1Static.lo 1 κ c)).sum.toNat := by
    rw [List.map_append, List.sum_append]
    have := sum_nonneg' ((pathArcs rows).map (Formal.Cells.Ua1Static.lo 1 κ c))
      (fun y hy => by obtain ⟨a, -, rfl⟩ := List.mem_map.1 hy; exact lo_nonneg (by linarith) hc0 hc1 a)
    have := sum_nonneg' ((r.arcs r.d).map (Formal.Cells.Ua1Static.lo 1 κ c))
      (fun y hy => by obtain ⟨a, -, rfl⟩ := List.mem_map.1 hy; exact lo_nonneg (by linarith) hc0 hc1 a)
    omega
  have hpath := toNat_sum_le (fun i => (rows.getD i default).r.arcs (pathPin (rows.getD i default)))
    (Formal.Cells.Ua1Static.lo 1 κ c) (lo_nonneg (by linarith) hc0 hc1) rows.length
  have hlo : ((pathArcs rows).map (Formal.Cells.Ua1Static.lo 1 κ c)).sum.toNat ≤ loSum ⟨1, κ⟩ c rows rows.length :=
    hpath
  have hhi : r.hi ⟨1, κ⟩ c r.e = ((r.arcs r.e).map (Formal.Cells.Ua1Static.hi 1 κ c)).sum.toNat := rfl
  have hld : r.lo ⟨1, κ⟩ c r.d = ((r.arcs r.d).map (Formal.Cells.Ua1Static.lo 1 κ c)).sum.toNat := rfl
  exact cert_sound hb P rows hok G a e E hcause hstat hmem (rows.length - 1) (by omega) u hu1 (by omega)

/-- The checks of a latch-hold row at the data pin: as `latchHoldOK`, with the arc-sum facts on
(path arcs ++ data-pin arcs) vs enable-pin arcs and no step to spare. -/
def latchHoldPinOK (r : LatchHoldRow) : Bool :=
  singlePath r.pc.2 && chainShape r.pc.2 && decide (1 ≤ r.pc.2.length) && lrowOK r.l &&
  (r.l.pins.getD r.l.e ([], 0)).2 == r.pc.1.cn && (r.pc.1.cv ^^ r.l.pe) &&
  (r.l.pins.getD r.l.d ([], 0)).2 == (r.pc.2.getD (r.pc.2.length - 1) default).r.q &&
  decide (r.kA * sFmax (r.l.arcs r.l.e) ≤ r.kB * sFmin (pathArcs r.pc.2 ++ r.l.arcs r.l.d)) &&
  decide (r.kA * sSmax (r.l.arcs r.l.e) ≤ r.kB * sSmin (pathArcs r.pc.2 ++ r.l.arcs r.l.d)) && decide (0 < r.kB)

theorem latch_hold_pin_row {r : LatchHoldRow} (hc : certOK r.pc.1 r.pc.2 = true) (hr : latchHoldPinOK r = true) {κ : ℚ}
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
    ∀ u, (win ⟨1, κ⟩ c a e E r.pc.2 (r.pc.2.length - 1)).1 ≤ u → u + r.l.lo ⟨1, κ⟩ c r.l.d < (e + 1) + r.l.hi ⟨1, κ⟩ c r.l.e →
      x (r.l.src r.l.d) u = (r.pc.2.getD (r.pc.2.length - 1) default).r.w := by
  simp only [latchHoldPinOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hr
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hsp, hch⟩, hn⟩, hl⟩, hen⟩, hpe⟩, hd⟩, h1⟩, h2⟩, hB0⟩ := hr
  have hl' := hl
  simp only [lrowOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hl'
  have hkk : r.l.g.k = r.l.pins.length := hl'.1.1.1.1.1.1.1.1.1.1.1.1.1
  have he : r.l.e < r.l.g.k := hl'.1.1.1.1.1.1.1.1.1.1.1.1.2
  have hdk : r.l.d < r.l.g.k := hl'.1.1.1.1.1.1.1.1.1.1.1.2
  refine ⟨hl, by rw [src_eq r.l (by omega), hen], hpe, fun u hu1 hu2 => ?_⟩
  rw [src_eq r.l (by omega), hd]
  exact latch_hold_pin hk0 hB0 hk hb r.pc.1 r.pc.2 r.l hc hsp hch hn h1 h2 hc0 hc1 G a e E PS hcause hstat hmem hPS hE hB u
    hu1 hu2

theorem latch_row_pin {p : DelayPar} {c : ℚ} {x : Beh} (hb : Behaves p (circuit net boundary) x) (r : LRow)
    (hok : lrowOK r = true) (hg : CGateOK p c r.g r.src r.arcs (r.S p) x) :
    ∀ (τ E We Wd A H : Nat) (v : Bool), r.S p ≤ A →
      (∀ i, i < r.g.k → r.hi p c i ≤ H) → 1 ≤ r.lo p c r.j →
      (∀ t, A ≤ t + H → x CElemPS.rstNode t = false) →
      (∀ t, τ ≤ t + We → t < τ → (x (r.src r.e) t ^^ r.pe) = true) →
      (∀ t, τ ≤ t → t ≤ E → (x (r.src r.e) t ^^ r.pe) = false) →
      (∀ t, τ ≤ t + Wd → t + r.lo p c r.d < τ + r.hi p c r.e → (x (r.src r.d) t ^^ r.pd) = v) →
      τ + r.hi p c r.e ≤ A + We → τ + r.hi p c r.d ≤ A + Wd → A + r.hi p c r.j ≤ τ + r.lo p c r.e →
      ∀ s, A ≤ s → s ≤ E + r.lo p c r.e → x r.q s = v := by
  intro τ E We Wd A H v hS hH hloj hrst hop hcl hdat hAe hAd hloop
  simp only [lrowOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    bne_iff_ne, ne_eq, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hk, he⟩, hd⟩, hj⟩, hed⟩, hej⟩, hdj⟩, -⟩, -⟩, hf⟩, -⟩, hfb⟩, hout⟩, hheld⟩ := hok
  have hout' : r.g.out = r.q := hout
  have hfb' : r.src r.j = r.g.out := by rw [src_eq r (by omega), hfb, hout']
  have key := latch_close_pin hg (Formal.Cells.SpecFbChain.cbands_of_sums r.arcs) he hd hj hed hej
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

theorem target_latch_holds_pin_of (L : List LatchHoldRow) (hL : ∀ r ∈ L, certOK r.pc.1 r.pc.2 = true ∧ latchHoldPinOK r = true)
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
        simp only [latchHoldPinOK, Bool.and_eq_true] at hl
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
  obtain ⟨hl, hsrc, hpe, hhold⟩ := latch_hold_pin_row (hL r hr).1 (hL r hr).2 hk0 hk hb hc0 hc1 G a e E PS h1 h2 h3 h4 h5 h6
  refine latch_row_pin hb r.l hl hg (e + 1) E' We Wd A H v hS hH hloj hrst (fun t t1 t2 => ?_) hcl (fun t t1 t2 => ?_)
    hAe hAd hloop
  · rw [hsrc, h1 t (by omega) (by omega)]; exact hpe
  · by_cases hlt : t < (win ⟨1, κ⟩ c a e E r.pc.2 (r.pc.2.length - 1)).1
    · exact hset t t1 hlt
    · rw [hhold t (by omega) (by omega)]; exact hw

end Formal.Cells.LatchHoldPin
