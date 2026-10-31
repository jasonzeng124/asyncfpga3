import Formal.Core.Delay.Corner
import Formal.Core.Substrate.CornerNat

/-!
# Corner model: scatter on the DIFFERENCE of two compared paths

Probe A / corner-diff (follow-up to `formal/notes/A-kappa.md`, section
"Lean status", proposed lemmas `ruleE_sound_diff`, `ring_kappa_attained`).

Rules E and A (`cells/verify/skew.py`, `cells/verify/tighten.py`) compare two
divergent tails `a` (early: data / select, prediction `Pa`) and `b` (late:
request, prediction `Pb`) of one route. `Corner.ruleE_sound` and
`Corner.ruleA_sound_rel` assume per-tail LocalScatter κ
(`Scat κ (s·P) d` on each tail). The ring oscillators of `ro_many_top` refute
that hypothesis at rule E's κ (`Corner.guard_refuted_by_7link_rings`). This
file proves the rules sound under a strictly weaker hypothesis that only
constrains the difference the rules actually compare.

## The hypothesis (named, explicit)

* **DiffScat κd** (`DiffScat κd s Pa Pb da db`): with one shared scale
  `s > 0` (proportional SharedCorner), the real difference `db - da` deviates
  from its nominal `s·(Pb - Pa)` by at most `κd` times the nominal SUM:

      |(db - da) - s·(Pb - Pa)| ≤ κd · s·(Pa + Pb).

  Writing `d = s·P·(1+ε)`, the deviation is `s·(εb·Pb - εa·Pa)`, so
  `κd = |εb·Pb - εa·Pa| / (Pa + Pb)`: exactly `kappa.py pairs`' `κ_diff`
  (`formal/tools-A/kappa/kappa.py`). The sum (not `Pb` alone) is the
  normaliser because then per-path κ gives `κd ≤ κ` with the SAME number
  (`diffScat_of_scat`), so the rules' limits read the same in both models.
* **DiffLow κd**: the lower half only, `s·((Pb-Pa) - κd(Pa+Pb)) ≤ db - da`.
  The soundness theorems need only this half (the late path really is late);
  `DiffScat` implies it (`DiffScat.low`).

## What is proved

1. `ruleE_sound_diff`: rule E's guard + `DiffLow κd`, `κd ≤ kappaE` (0.1988)
   ⇒ select before request. `ruleE_diff_tight`: for every `κd > kappaE` a
   `DiffScat κd` instance passes the guard and the select arrives strictly
   after the request. So `kappaE` is the exact limit.
2. `ruleA_sound_diff`: rule A + `DiffLow κd`, `κd ≤ 1/11` ⇒ data before request;
   `ruleA_diff_tight`: exact for every `κd > 1/11`.
   `ruleA_sound_diff_mixed`: with an additive difference term `θd ≤ 100`
   (two tails of rule A's 50 ps each), `κd ≤ 1/22`; `ruleA_diff_mixed_tight`.
3. Per-path ⇒ difference: `diffScat_of_scat` (`κd = κ`),
   `diff_of_scat_sharp` (it is attained, so `f(κ) = κ` is the best map), and
   `ruleE_sound_of_diff` re-derives `Corner.ruleE_sound` through it.
   Difference ⇏ per-path: `diff_not_imp_scat` (perfectly correlated tails,
   `κd = 0`, per-path scatter beyond ANY bound `K`), and the instance
   `rings_refute_path_not_diff`: the 7-link ring ratios 1.470 / 0.773 are
   realised at per-path κ = 0.311 > kappaE (so `ruleE_sound` does not apply)
   together with a guarded tail pair at κd = 0, where `ruleE_sound_diff`
   proves the order.
4. `ring_kappa_attained`: at `s = (ri+rj)/2`, `κ = (ri-rj)/(ri+rj)` both rings
   (and every ratio in `[rj, ri]`, `ring_kappa_attained_all`) satisfy `Scat`.
   `ring_kappa_iff`: some shared scale realises both ratios at κ iff
   `ri - rj ≤ κ(ri + rj)`. Together with `Corner.ring_kappa_lower` this makes
   `(r_max - r_min)/(r_max + r_min)` the best lower bound on κ that ratio
   data alone can give.

Nothing here constrains `κd` from ring data: a ring is one absolute path, and
`diff_not_imp_scat` / `rings_refute_path_not_diff` show that absolute
(per-path) scatter, however large, is compatible with `κd = 0`.
-/

namespace Formal.Core.CornerDiff

open Formal.Core.Corner

/-! ## 1. The difference hypothesis -/

/-- **DiffScat κd**: the real difference `db - da` of two tails with
predictions `Pa`, `Pb` under one shared scale `s` is within `κd·s·(Pa+Pb)` of
its nominal `s·(Pb - Pa)`. -/
def DiffScat (κd s Pa Pb da db : ℝ) : Prop :=
  s * (Pb - Pa) - κd * (s * (Pa + Pb)) ≤ db - da ∧
    db - da ≤ s * (Pb - Pa) + κd * (s * (Pa + Pb))

/-- The lower half of `DiffScat`: the late tail `b` is late by at least the
guarded nominal difference. This is all the soundness theorems use. -/
def DiffLow (κd s Pa Pb da db : ℝ) : Prop :=
  s * ((Pb - Pa) - κd * (Pa + Pb)) ≤ db - da

theorem DiffScat.low {κd s Pa Pb da db : ℝ} (h : DiffScat κd s Pa Pb da db) :
    DiffLow κd s Pa Pb da db := by
  unfold DiffLow; have := h.1; nlinarith

/-- `DiffScat` is monotone in `κd` (for nonnegative nominal sums). -/
theorem DiffScat.mono {κd κd' s Pa Pb da db : ℝ} (hle : κd ≤ κd')
    (hsum : 0 ≤ s * (Pa + Pb)) (h : DiffScat κd s Pa Pb da db) :
    DiffScat κd' s Pa Pb da db := by
  obtain ⟨h1, h2⟩ := h
  have := mul_le_mul_of_nonneg_right hle hsum
  constructor <;> linarith

/-! ## 2. Rule E under difference scatter -/

/-- **Rule E is sound under difference scatter `κd ≤ kappaE`.** Tail `s` (select,
prediction `Ps`, real `as_`) and tail `r` (request, `Pr`, `ar`) after a shared
prefix `C`. Only the lower half of `DiffScat` is assumed. -/
theorem ruleE_sound_diff {κd s C Pr Ps ar as_ : ℝ} (hs : 0 < s) (hκ : κd ≤ kappaE)
    (hPs : 0 ≤ Ps) (hd : DiffLow κd s Ps Pr as_ ar)
    (hguard : 0 < guardLo * Pr - guardHi * Ps) :
    C + as_ < C + ar := by
  unfold DiffLow at hd
  have hk := guard_kappa_iff.mpr hκ
  unfold guardLo guardHi at hk hguard
  unfold kappaE at hκ
  have key : 0 < (Pr - Ps) - κd * (Ps + Pr) := by nlinarith
  have := mul_pos hs key
  linarith

/-- **`kappaE` is the exact difference limit of rule E.** For every
`κd > kappaE` there are guarded predictions and real tails satisfying the full
two-sided `DiffScat κd` (scale 1) in which the select arrives strictly after
the request. -/
theorem ruleE_diff_tight {κd : ℝ} (hκ : kappaE < κd) :
    ∃ Pr Ps ar as_ : ℝ, 0 ≤ Ps ∧ 0 < guardLo * Pr - guardHi * Ps ∧
      DiffScat κd 1 Ps Pr as_ ar ∧ ar < as_ := by
  set k := min κd (1/2) with hkdef
  have hk1 : k ≤ κd := min_le_left _ _
  have hk2 : k ≤ 1/2 := min_le_right _ _
  have hk3 : kappaE < k := lt_min hκ (by unfold kappaE; norm_num)
  obtain ⟨Pr, Ps, hPs, hg, hv⟩ := ruleE_tight hk3 (by linarith)
  have hPr : 0 ≤ Pr := by unfold guardLo guardHi at hg; nlinarith
  refine ⟨Pr, Ps, (1 - k) * Pr, (1 + k) * Ps, hPs, hg, ?_, by linarith⟩
  have hk0 : 0 ≤ k := by unfold kappaE at hk3; linarith
  apply DiffScat.mono hk1 (by linarith)
  constructor <;> nlinarith

/-! ## 3. Rule A under difference scatter -/

/-- **Rule A is sound under difference scatter `κd ≤ 1/11`** (data tail `Pd`,
request tail `Pr`, `t_req ≥ t_data + max(0.2·t_data, 200)` on the
predictions). -/
theorem ruleA_sound_diff {κd s Pd Pr ad ar : ℝ} (hs : 0 < s)
    (hκ : κd ≤ 1/11) (hPd : 0 ≤ Pd)
    (hruleA : Pd + max (Pd / 5) 200 ≤ Pr)
    (hd : DiffLow κd s Pd Pr ad ar) :
    ad ≤ ar := by
  unfold DiffLow at hd
  have hm1 := le_max_left (Pd / 5) 200
  have hm2 := le_max_right (Pd / 5) 200
  have key : 0 ≤ (Pr - Pd) - κd * (Pd + Pr) := by
    by_cases hk0 : κd ≤ 0
    · nlinarith
    · have hk0 := (not_le.mp hk0)
      have hsum : κd * (Pd + Pr) ≤ (Pd + Pr) / 11 := by nlinarith
      by_cases hP : Pd ≤ 1000
      · nlinarith
      · nlinarith
  have := mul_nonneg hs.le key
  linarith

/-- **`1/11` is the exact difference limit of rule A.** For `κd > 1/11`, a
1000 ps data tail with the request exactly at rule A's bound (1200 ps) admits
a `DiffScat κd` (scale 1) assignment with the data strictly after the
request. -/
theorem ruleA_diff_tight {κd : ℝ} (hκ : 1/11 < κd) :
    ∃ ad ar : ℝ, (1000:ℝ) + max (1000 / 5) 200 ≤ 1200 ∧
      DiffScat κd 1 1000 1200 ad ar ∧ ar < ad := by
  refine ⟨(1 + κd) * 1000, (1 - κd) * 1200, by norm_num, ?_, by linarith⟩
  constructor <;> nlinarith

/-- **Rule A, mixed form, under difference scatter.** If the difference
deviates by at most `s·(κd·(Pd+Pr) + θd)` with `κd ≤ 1/22` and an additive
difference term `θd ≤ 100` ps (two tails at rule A's 50 ps each), rule A
still orders data before request. -/
theorem ruleA_sound_diff_mixed {κd θd s Pd Pr ad ar : ℝ} (hs : 0 < s)
    (hκ : κd ≤ 1/22) (hθ : θd ≤ 100) (hPd : 0 ≤ Pd)
    (hruleA : Pd + max (Pd / 5) 200 ≤ Pr)
    (hd : s * ((Pr - Pd) - κd * (Pd + Pr) - θd) ≤ ar - ad) :
    ad ≤ ar := by
  have hm1 := le_max_left (Pd / 5) 200
  have hm2 := le_max_right (Pd / 5) 200
  have key : 0 ≤ (Pr - Pd) - κd * (Pd + Pr) - θd := by
    by_cases hk0 : κd ≤ 0
    · nlinarith
    · have hk0 := (not_le.mp hk0)
      have hsum : κd * (Pd + Pr) ≤ (Pd + Pr) / 22 := by nlinarith
      by_cases hP : Pd ≤ 1000
      · nlinarith
      · nlinarith
  have := mul_nonneg hs.le key
  linarith

/-- The mixed limits are tight together: with `θd = 100` exactly, any
`κd > 1/22` breaks rule A on the 1000/1200 ps pair. -/
theorem ruleA_diff_mixed_tight {κd : ℝ} (hκ : 1/22 < κd) :
    (1000:ℝ) + max (1000 / 5) 200 ≤ 1200 ∧
      (1200 - 1000) - κd * (1000 + 1200) - 100 < (0:ℝ) := by
  refine ⟨by norm_num, by linarith⟩

/-! ## 4. Per-path scatter implies difference scatter, not conversely -/

/-- **Per-path κ ⇒ difference κ, with the same number.** -/
theorem diffScat_of_scat {κ s Pa Pb da db : ℝ}
    (ha : Scat κ (s * Pa) da) (hb : Scat κ (s * Pb) db) :
    DiffScat κ s Pa Pb da db := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  constructor <;> nlinarith

/-- **`κd = κ` is the best map**: anti-correlated extreme tails (early tail
slow by κ, late tail fast by κ) attain the lower difference bound exactly. -/
theorem diff_of_scat_sharp {κ s Pa Pb : ℝ} (hκ : 0 ≤ κ) (hs : 0 ≤ s)
    (hPa : 0 ≤ Pa) (hPb : 0 ≤ Pb) :
    ∃ da db : ℝ, Scat κ (s * Pa) da ∧ Scat κ (s * Pb) db ∧
      (db - da) - s * (Pb - Pa) = -(κ * (s * (Pa + Pb))) := by
  have hA : 0 ≤ s * Pa := mul_nonneg hs hPa
  have hB : 0 ≤ s * Pb := mul_nonneg hs hPb
  refine ⟨(1 + κ) * (s * Pa), (1 - κ) * (s * Pb), ⟨?_, le_refl _⟩, ⟨le_refl _, ?_⟩, by ring⟩
  · nlinarith
  · nlinarith

/-- `Corner.ruleE_sound` is a corollary of `ruleE_sound_diff`: the per-path
hypothesis is the stronger one. -/
theorem ruleE_sound_of_diff {κ s C Pr Ps ar as_ : ℝ} (hs : 0 < s) (hκ : κ ≤ kappaE)
    (hPs : 0 ≤ Ps)
    (har : Scat κ (s * Pr) ar) (has : Scat κ (s * Ps) as_)
    (hguard : 0 < guardLo * Pr - guardHi * Ps) :
    C + as_ < C + ar :=
  ruleE_sound_diff hs hκ hPs (diffScat_of_scat has har).low hguard

/-- **Difference κ ⇏ per-path κ.** For every candidate per-path bound `K`
there are two perfectly correlated tails (equal predictions, equal real
delays) with `κd = 0` and per-path scatter outside `K` on both tails. So no
function `g` gives `DiffScat κd → Scat (g κd)`. -/
theorem diff_not_imp_scat (K : ℝ) :
    ∃ s Pa Pb da db : ℝ, 0 < s ∧ 0 < Pa ∧ 0 < Pb ∧
      DiffScat 0 s Pa Pb da db ∧ ¬ Scat K (s * Pa) da ∧ ¬ Scat K (s * Pb) db := by
  refine ⟨1, 1, 1, |K| + 3, |K| + 3, one_pos, one_pos, one_pos, ?_, ?_, ?_⟩
  · constructor <;> norm_num
  · rintro ⟨_, h⟩; have := le_abs_self K; linarith
  · rintro ⟨_, h⟩; have := le_abs_self K; linarith

/-- **The rings refute per-path κ, not difference κ** (concrete instance).
At one shared scale `s = 2.243/2` the 7-link ring ratios 1.470 and 0.773 are
realised with per-path κ = 0.697/2.243 > kappaE, so `Corner.ruleE_sound`'s
hypothesis fails at kappaE (`Corner.guard_refuted_by_7link_rings`). On the
same die, a guarded tail pair (`Pr = 2`, `Ps = 1`) whose tails also scatter
by up to that κ but are correlated so that `κd = 0` satisfies
`ruleE_sound_diff`, which proves the select first. -/
theorem rings_refute_path_not_diff :
    let s : ℝ := 2243 / 2000
    let κ : ℝ := 697 / 2243
    let as_ : ℝ := s * (1 + κ)
    let ar : ℝ := as_ + s
    kappaE < κ ∧ Scat κ s (1470/1000) ∧ Scat κ s (773/1000) ∧
      Scat κ (s * 2) ar ∧ Scat κ (s * 1) as_ ∧
      DiffScat 0 s 1 2 as_ ar ∧ 0 < guardLo * 2 - guardHi * 1 ∧
      (∀ C : ℝ, C + as_ < C + ar) := by
  intro s κ as_ ar
  have hd : DiffScat 0 s 1 2 as_ ar := by
    simp only [DiffScat, s, κ, as_, ar]; constructor <;> norm_num
  have hg : 0 < guardLo * 2 - guardHi * 1 := by unfold guardLo guardHi; norm_num
  refine ⟨by unfold kappaE; simp only [κ]; norm_num, ?_, ?_, ?_, ?_, hd, hg, ?_⟩
  · simp only [Scat, s, κ]; constructor <;> norm_num
  · simp only [Scat, s, κ]; constructor <;> norm_num
  · simp only [Scat, s, κ, as_, ar]; constructor <;> norm_num
  · simp only [Scat, s, κ, as_]; constructor <;> norm_num
  · intro C
    exact ruleE_sound_diff (by simp only [s]; norm_num) (by unfold kappaE; norm_num)
      (by norm_num) hd.low hg

/-! ## 5. The ring pair bound is attained -/

/-- **The pair bound is attained.** With `s = (ri+rj)/2` and
`κ = (ri-rj)/(ri+rj)`, every ratio `r ∈ [rj, ri]` satisfies `Scat κ s r`. -/
theorem ring_kappa_attained_all {ri rj : ℝ} (hj : 0 < rj) (hji : rj ≤ ri) :
    ∀ r : ℝ, rj ≤ r → r ≤ ri →
      Scat ((ri - rj) / (ri + rj)) ((ri + rj) / 2) r := by
  intro r h1 h2
  have hpos : 0 < ri + rj := by linarith
  have hk : (ri - rj) / (ri + rj) * (ri + rj) = ri - rj := div_mul_cancel₀ _ hpos.ne'
  set k := (ri - rj) / (ri + rj)
  constructor <;> nlinarith

/-- `ring_kappa_attained` (A-kappa.md's proposed lemma): both extreme rings
are realised at the pair bound. -/
theorem ring_kappa_attained {ri rj : ℝ} (hj : 0 < rj) (hji : rj ≤ ri) :
    Scat ((ri - rj) / (ri + rj)) ((ri + rj) / 2) ri ∧
      Scat ((ri - rj) / (ri + rj)) ((ri + rj) / 2) rj :=
  ⟨ring_kappa_attained_all hj hji ri hji le_rfl,
   ring_kappa_attained_all hj hji rj le_rfl hji⟩

/-- **The pair bound is the exact feasibility test.** For `κ ∈ [-1, 1]` and
two ratios `rj ≤ ri`, some shared scale realises both at κ iff
`ri - rj ≤ κ·(ri + rj)`. So `(r_max - r_min)/(r_max + r_min)` is the best
lower bound on κ obtainable from ratio data alone. -/
theorem ring_kappa_iff {κ ri rj : ℝ} (hκ1 : κ ≤ 1) (hκm : -1 ≤ κ)
    (hji : rj ≤ ri) :
    (∃ s : ℝ, Scat κ s ri ∧ Scat κ s rj) ↔ ri - rj ≤ κ * (ri + rj) := by
  constructor
  · rintro ⟨s, hi, hj'⟩
    exact ring_kappa_lower hκ1 hκm hi hj'
  · intro h
    refine ⟨(ri + rj) / 2, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith

/-- Below the pair bound no shared scale exists (the strict converse of
`ring_kappa_attained`, from `Corner.ring_kappa_lower`). -/
theorem ring_kappa_below_infeasible {κ ri rj : ℝ} (hκ1 : κ ≤ 1) (hκm : -1 ≤ κ)
    (hj : 0 < rj) (hji : rj ≤ ri) (hlt : κ < (ri - rj) / (ri + rj)) :
    ¬ ∃ s : ℝ, Scat κ s ri ∧ Scat κ s rj := by
  rintro ⟨s, hi, hj'⟩
  have h := ring_kappa_lower hκ1 hκm hi hj'
  have hpos : 0 < ri + rj := by linarith
  have hk : (ri - rj) / (ri + rj) * (ri + rj) = ri - rj := div_mul_cancel₀ _ hpos.ne'
  nlinarith

/-! ## Non-degenerate difference-without-per-path witness (2026-10-31)

Audit `5a1ee8d2` (P13, OVERSTATED): `diff_not_imp_scat`'s witness is a scale artefact -- at
the shared scale `s' = |K| + 3` both of its tails have per-path scatter 0. The statement is
still true, but the witness does not show what the docstring says. `diff_not_imp_scat_strong`
(proof by the auditor, `audit/lean/P13/T23_Corner.lean`, ported verbatim) is the honest
version: a pair that passes rule E's guard (`Pa = 1`, `Pb = 2`), has `κd = 0` at scale 1, and
violates per-path `Scat K` on at least one tail at EVERY positive shared scale, for every
`0 ≤ K < 1`. -/

/-- At the scale `|K| + 3` the old witness has per-path scatter 0 (it is degenerate). -/
theorem diff_not_imp_scat_degenerate (K : ℝ) :
    DiffScat 0 (|K| + 3) 1 1 (|K| + 3) (|K| + 3) ∧ Scat 0 ((|K| + 3) * 1) (|K| + 3) := by
  refine ⟨?_, ?_⟩ <;> simp [DiffScat, Scat]

theorem diff_not_imp_scat_strong (K : ℝ) (hK0 : 0 ≤ K) (hK1 : K < 1) :
    ∃ da db : ℝ, 0 < guardLo * 2 - guardHi * 1 ∧ DiffScat 0 1 1 2 da db ∧
      ∀ s' : ℝ, 0 < s' → ¬ (Scat K (s' * 1) da ∧ Scat K (s' * 2) db) := by
  set e := (1 - K) / (4 * (1 + K)) with he
  have hpos : 0 < 1 + K := by linarith
  have he4 : (1 + K) * (4 * e) = 1 - K := by rw [he]; field_simp
  have he0 : 0 < e := by rw [he]; apply div_pos <;> linarith
  refine ⟨e, 1 + e, by unfold guardLo guardHi; norm_num, ?_, ?_⟩
  · constructor <;> linarith
  · rintro s' hs' ⟨⟨h1, _⟩, ⟨_, h4⟩⟩
    have a : (1 - K) * (1 + e) ≤ (1 - K) * ((1 + K) * (s' * 2)) :=
      mul_le_mul_of_nonneg_left h4 (by linarith)
    have b : (1 + K) * 2 * ((1 - K) * (s' * 1)) ≤ (1 + K) * 2 * e :=
      mul_le_mul_of_nonneg_left h1 (by nlinarith)
    nlinarith

end Formal.Core.CornerDiff
