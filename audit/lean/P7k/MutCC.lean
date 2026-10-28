import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rule A exactly as `cells/verify/tighten.py` computes it

Probe A / CornerCode. Answers the audit finding (audit/findings/A.md, first
row) that `Corner.ruleA_sound_rel` / `Corner.ruleA_tight` ("rule A is sound iff
κ ≤ 1/11") are about the **real-valued** rule `Pd + max (Pd/5) 200 ≤ Pr`, while
the code works on integer picoseconds and truncates the 20 % term.

## The code (cells/verify/tighten.py)

* SDF delays are parsed with `int(...)` (`parse_sdf`), so every arrival
  `t_e` (request, shortest walk) and `t_l` (data, longest walk) is a natural
  number of ps.
* `req_guard(p, t) = max(int(0.2 * t), 200) + SLACK` (l.1106).
* `check` computes `margin = t_e - t_l - guard(t_l)`; `rule_a_links` asks for
  more links (verdict `VIOLATION`) exactly when `margin < 0`. So the design
  passes iff `t_l + guard(t_l) ≤ t_e`: `pass SLACK t_e t_l` below.
* `int(0.2 * t)` on a Python float equals `t / 5` (floor) for every integer
  `0 ≤ t < 2^50`; this is **not** proved here (it is a fact about IEEE
  doubles; see formal/notes/A-corner-code.md for the argument and the scan).
  The Lean model uses `t / 5` on `ℕ`.
* `SLACK` is 0 unless `--slack` is passed; only `verify/resize.sh` and
  `hw/tighten_loop.sh` (opt-in) pass it, for the length *search*. The audit
  that gates a build runs with `SLACK = 0`. Both cases are treated: `S = 0` is
  the gate, `S ≥ 1` is the search.

## The corner model (as in `Corner.ruleA_sound_rel`)

Proportional shared corner: one scale `s > 0` for the whole die, the real data
delay `ad ≤ s·(1+κ)·t_l` and the real request delay `ar ≥ s·(1-κ)·t_e`
(local scatter κ, purely relative, no additive θ).

## What is proved

* `ruleA_code_sound`: with any `S` and `κ ≤ 25/276 ≈ 0.09058`, a passing pair
  has `ad ≤ ar`.
* `ruleA_code_tight`: for every `κ > 25/276` the pair `t_l = 1004`,
  `t_e = 1204` passes the gate (`S = 0`) and is violated (`s = 1`).
* `ruleA_code_iff`, `ruleA_code_model_iff`: hence, at `S = 0`, the code's rule
  is sound in this model **iff** `κ ≤ 25/276` (exact threshold; the auditor's
  number is confirmed).
* `ruleA_code_at`: the exact threshold for one data delay `t_l`:
  `κ·(2 t_l + g) ≤ g`, `g = guard S t_l`. For `t_l ≤ 1004` (`guard_small`)
  `g = 200` and the threshold is `100/(t_l+100)`, smallest at `t_l = 1004`;
  for `t_l ≥ 1005` (`guard_large`) `g = ⌊t_l/5⌋` and it is above 25/276.
* `ruleA_slack_sound`, `ruleA_slack_tight`: with `S ≥ 1` the truncation loss
  (at most 4/5 ps) is covered and the threshold is back to 1/11, but it is not
  attained: for every `κ > 1/11` and every `S` some passing pair is violated.
* `real_imp_code`: the real-valued rule implies the code's, so the code accepts
  at least what `Corner.ruleA_sound_rel` covers (and, e.g., (1004, 1204) more).

Not covered: affine (two-endpoint) corners (rule A reads one SDF number), the
additive scatter θ of `Corner.ruleA_sound`, the `upstream_lag` correction of
the bundled-channel pairing (guard computed on `t_l` before the lag is added),
and whether the SDF shortest/longest walks are the real extreme paths.
-/

namespace Formal.Core.CornerCode

/-- `req_guard` with `int(0.2*t)` read as `t / 5` (floor) and slack `S`. -/
def guard (S tl : ℕ) : ℕ := max (tl / 5) 200 + S

/-- Rule A not a violation: `t_e - t_l - guard(t_l) ≥ 0`. -/
def pass (S te tl : ℕ) : Prop := tl + guard S tl ≤ te

instance (S te tl : ℕ) : Decidable (pass S te tl) := by
  unfold pass; infer_instance

/-- The 200 ps floor dominates up to `t_l = 1004`. -/
theorem guard_small {tl : ℕ} (h : tl ≤ 1004) : guard 0 tl = 200 := by
  simp only [guard, Nat.add_zero]
  exact max_eq_right (show tl / 5 ≤ 200 by omega)

/-- From `t_l = 1005` on, the guard is `⌊t_l/5⌋`. -/
theorem guard_large {tl : ℕ} (h : 1005 ≤ tl) : guard 0 tl = tl / 5 := by
  simp only [guard, Nat.add_zero]
  exact max_eq_left (show 200 ≤ tl / 5 by omega)

/-- More slack only makes the rule stricter. -/
theorem pass_zero {S te tl : ℕ} (h : pass S te tl) : pass 0 te tl := by
  unfold pass guard at *; omega

/-- The integer core: a passing pair has `301·t_l ≤ 251·t_e`, i.e.
`(1 + 25/276)·t_l ≤ (1 - 25/276)·t_e`. -/
theorem pass_ratio {te tl : ℕ} (h : pass 0 te tl) : 301 * tl ≤ 251 * te := by
  unfold pass guard at h
  rcases le_total (tl / 5) 200 with hm | hm
  · rw [max_eq_right hm] at h; omega
  · rw [max_eq_left hm] at h; omega

/-- The nominal inequality at `κ ≤ 25/276`, for any slack. -/
theorem ruleA_code_nominal {κ : ℝ} {S te tl : ℕ} (hκ : κ ≤ 25 / 276)
    (h : pass S te tl) : (1 + κ) * (tl : ℝ) ≤ (1 - κ) * te := by
  have h1 := pass_ratio (pass_zero h)
  have h2 : (301 : ℝ) * tl ≤ 251 * te := by exact_mod_cast h1
  have h3 : (0 : ℝ) ≤ tl := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ te := Nat.cast_nonneg _
  have h5 := mul_le_mul_of_nonneg_right hκ (add_nonneg h3 h4)
  nlinarith

/-- **Soundness of the code's rule A for κ ≤ 25/276** (proportional shared
corner, relative local scatter κ, any slack `S`). -/
theorem ruleA_code_sound {κ s ad ar : ℝ} {S te tl : ℕ} (hs : 0 < s)
    (hκ : κ ≤ 25 / 276) (h : pass S te tl)
    (had : ad ≤ s * ((1 + κ) * tl)) (har : s * ((1 - κ) * te) ≤ ar) :
    ad ≤ ar := by
  have := mul_le_mul_of_nonneg_left (ruleA_code_nominal hκ h) hs.le
  linarith

/-- **Tightness at the gate (S = 0).** For `κ > 25/276`, `t_l = 1004`,
`t_e = 1204` passes (guard `max(200, 200) = 200`, margin 0) and the request
at `(1-κ)·1204` beats the data at `(1+κ)·1004`. -/
theorem ruleA_code_tight {κ : ℝ} (hκ : 25 / 276 < κ) :
    pass 0 1204 1004 ∧ (1 - κ) * (1204 : ℝ) < (1 + κ) * 1004 := by
  refine ⟨by decide, by linarith⟩

/-- The audit's witness: κ = 1/11 is not covered by the code's rule. -/
theorem ruleA_code_unsound_1_11 :
    pass 0 1204 1004 ∧ (1 - 1 / 11) * (1204 : ℝ) < (1 + 1 / 11) * 1004 :=
  ruleA_code_tight (by norm_num)

/-- **Exact threshold, nominal form**: at `S = 0`, every passing pair satisfies
the scattered inequality iff `κ ≤ 25/276`. -/
theorem ruleA_code_iff (κ : ℝ) :
    (∀ te tl : ℕ, pass 0 te tl → (1 + κ) * (tl : ℝ) ≤ (1 - κ) * te) ↔
      κ ≤ 1 / 11 := by
  constructor
  · intro H
    by_contra hk
    have ⟨hp, hv⟩ := ruleA_code_tight (lt_of_not_ge hk)
    have := H 1204 1004 hp
    push_cast at this
    linarith
  · intro hκ te tl h; exact ruleA_code_nominal hκ h

/-- **Exact threshold, model form**: at `S = 0`, the code's rule A guarantees
`ad ≤ ar` for every shared scale and every scatter-κ realisation iff
`κ ≤ 25/276`. -/
theorem ruleA_code_model_iff (κ : ℝ) :
    (∀ (s ad ar : ℝ) (te tl : ℕ), 0 < s → pass 0 te tl →
      ad ≤ s * ((1 + κ) * tl) → s * ((1 - κ) * te) ≤ ar → ad ≤ ar) ↔
      κ ≤ 25 / 276 := by
  constructor
  · intro H
    by_contra hk
    have ⟨hp, hv⟩ := ruleA_code_tight (lt_of_not_ge hk)
    have := H 1 ((1 + κ) * 1004) ((1 - κ) * 1204) 1204 1004 one_pos hp
      (by push_cast; linarith) (by push_cast; linarith)
    linarith
  · intro hκ s ad ar te tl hs h had har
    exact ruleA_code_sound hs hκ h had har

/-- **Per-data-delay threshold.** For a fixed `t_l` and slack `S`, every
request delay that passes is safe iff `κ·(2 t_l + g) ≤ g`, `g = guard S t_l`
(the worst passing request is `t_e = t_l + g`). -/
theorem ruleA_code_at (S tl : ℕ) (κ : ℝ) :
    (∀ te : ℕ, pass S te tl → (1 + κ) * (tl : ℝ) ≤ (1 - κ) * te) ↔
      κ * (2 * tl + guard S tl) ≤ guard S tl := by
  have hg : (200 : ℝ) ≤ guard S tl := by
    have : 200 ≤ guard S tl := by unfold guard; omega
    exact_mod_cast this
  have ht : (0 : ℝ) ≤ tl := Nat.cast_nonneg _
  constructor
  · intro H
    have := H (tl + guard S tl) (by unfold pass; omega)
    push_cast at this
    nlinarith
  · intro hk te h
    have h1 : (tl : ℝ) + guard S tl ≤ te := by unfold pass at h; exact_mod_cast h
    have hk1 : κ ≤ 1 := by
      by_contra hc
      replace hc := lt_of_not_ge hc
      nlinarith [mul_lt_mul_of_pos_right hc (by linarith : (0 : ℝ) < guard S tl)]
    nlinarith [mul_nonneg (sub_nonneg.2 hk1) (sub_nonneg.2 h1)]

/-- **With slack `S ≥ 1` the threshold is back to 1/11**: the truncation loses
at most 4/5 ps, which one ps of slack covers. -/
theorem ruleA_slack_sound {κ s ad ar : ℝ} {S te tl : ℕ} (hS : 1 ≤ S) (hs : 0 < s)
    (hκ : κ ≤ 1 / 11) (h : pass S te tl)
    (had : ad ≤ s * ((1 + κ) * tl)) (har : s * ((1 - κ) * te) ≤ ar) :
    ad ≤ ar := by
  have h1 : 6 * tl ≤ 5 * te := by
    unfold pass guard at h
    rcases le_total (tl / 5) 200 with hm | hm
    · rw [max_eq_right hm] at h; omega
    · rw [max_eq_left hm] at h; omega
  have h2 : (6 : ℝ) * tl ≤ 5 * te := by exact_mod_cast h1
  have h3 : (0 : ℝ) ≤ tl := Nat.cast_nonneg _
  have h4 : (0 : ℝ) ≤ te := Nat.cast_nonneg _
  have h5 := mul_le_mul_of_nonneg_right hκ (add_nonneg h3 h4)
  have key : (1 + κ) * (tl : ℝ) ≤ (1 - κ) * te := by nlinarith
  have := mul_le_mul_of_nonneg_left key hs.le
  linarith

/-- **No slack covers any κ > 1/11**: for every `S` there is a passing pair
(`t_l = 5q+4`, `t_e = t_l + q + S`, `q` large) that is violated. -/
theorem ruleA_slack_tight (S : ℕ) {κ : ℝ} (hκ : 1 / 11 < κ) :
    ∃ te tl : ℕ, pass S te tl ∧ (1 - κ) * (te : ℝ) < (1 + κ) * tl := by
  obtain ⟨ε, hε0, rfl⟩ : ∃ ε : ℝ, 0 < ε ∧ κ = 1 / 11 + ε :=
    ⟨κ - 1 / 11, by linarith, by ring⟩
  have h121 : (0 : ℝ) < 121 * ε := by linarith
  obtain ⟨q, hq⟩ := exists_nat_gt ((10 * (S : ℝ) + 1) / (121 * ε) + 200)
  have hq200 : (200 : ℝ) < q := by
    have : 0 ≤ (10 * (S : ℝ) + 1) / (121 * ε) :=
      div_nonneg (by positivity) h121.le
    linarith
  have hq200' : 200 < q := by exact_mod_cast hq200
  have hqe : 10 * (S : ℝ) + 1 < q * (121 * ε) := by
    have h1 : (10 * (S : ℝ) + 1) / (121 * ε) < q := by linarith
    rwa [div_lt_iff₀ h121] at h1
  refine ⟨5 * q + 4 + q + S, 5 * q + 4, ?_, ?_⟩
  · unfold pass guard
    rw [show (5 * q + 4) / 5 = q by omega, max_eq_left (show 200 ≤ q by omega)]
    all_goals omega
  · push_cast
    have hS : (0 : ℝ) ≤ S := Nat.cast_nonneg _
    nlinarith [mul_nonneg hε0.le hS]

/-- The real-valued rule of `Corner.ruleA_sound_rel` implies the code's rule
(`⌊t/5⌋ ≤ t/5`), so the code accepts every design the real rule accepts. -/
theorem real_imp_code {te tl : ℕ}
    (h : (tl : ℝ) + max ((tl : ℝ) / 5) 200 ≤ te) : pass 0 te tl := by
  have hd : ((tl / 5 : ℕ) : ℝ) ≤ (tl : ℝ) / 5 := Nat.cast_div_le
  have hm : (((max (tl / 5) 200 : ℕ)) : ℝ) ≤ max ((tl : ℝ) / 5) 200 := by
    push_cast
    exact max_le_max hd le_rfl
  have : ((tl + guard 0 tl : ℕ) : ℝ) ≤ te := by
    unfold guard; push_cast at hm ⊢; linarith
  unfold pass; exact_mod_cast this

/-- …and strictly more: (1004, 1204) passes the code but not the real rule. -/
theorem code_not_imp_real :
    pass 0 1204 1004 ∧ ¬ ((1004 : ℝ) + max ((1004 : ℝ) / 5) 200 ≤ 1204) := by
  refine ⟨by decide, ?_⟩
  rw [max_eq_left (show (200 : ℝ) ≤ 1004 / 5 by norm_num)]; norm_num

end Formal.Core.CornerCode
