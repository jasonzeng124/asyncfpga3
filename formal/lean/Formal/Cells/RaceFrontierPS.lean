import Formal.Cells.RaceTablePS
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Formal.Cells.RaceFrontierPS — the (g, κ) frontier of gcd_ps's recorded acknowledgement races

Shard B, THE goal, S3. The owner asked for the margin as the (g, κ) frontier (decision 3). `RaceTablePS` fixes g = 1.

## Problem, plainly
For which guard g and scatter κ is every recorded acknowledgement race of THE target (the 185 rows of
`RaceTablePS.raceTable`) safe at every corner, under Spec's `Adm` window `[(1-κ)·lerp_lo/g, (1+κ)·lerp_hi·g]`?

## Results
* `sum_lower_g`, `sum_upper_g`: admissible delays at `(g, κ, c)` sum to within
  `(1-κ)/g · lerp(ΣFAST_MIN, ΣSLOW_MIN, c)` .. `(1+κ)·g · lerp(ΣFAST_MAX, ΣSLOW_MAX, c)` (any g > 0, κ ≤ 1).
* `race_ok_gk`: if `(1+κ)·g²·ΣFAST_MAX(loop) ≤ (1-κ)·ΣFAST_MIN(path)` and the same with SLOW, then for every corner
  `c ∈ [0,1]` and every admissible delays, loop total ≤ path total.
* `frontier`: all 185 rows pass at (g, κ) = (1.55, 0), (1.5, 0), (1.25, 0.2), (1.1, 0.3), (1, 0.415).
  The binding row (SLICE_X32Y45.A) sets the frontier `g² (1+κ)/(1-κ) ≤ 2.433` (ΣFAST_MIN path / ΣFAST_MAX loop =
  1073/441; the slow-corner ratio 2798/1082 is larger): g ≤ 1.56 at κ = 0, 1.27 at κ = 0.2, 1.02 at κ = 0.4.

## Not covered
As `RaceTablePS` (recorded episodes only; generated rows; necessity per simulated run).
-/

namespace Formal.Cells.RaceFrontierPS
open Formal.Target Formal.Cells.RaceCornersPS Formal.Cells.RaceTablePS

theorem sum_lower_g {p : DelayPar} (hg : 0 < p.g) {c : ℚ} :
    ∀ (es : List Arc) (ds : List Nat), List.Forall₂ (fun e d => Adm p c e d) es ds →
      (1 - p.κ) / p.g * ((1 - c) * (sFmin es : ℚ) + c * (sSmin es : ℚ)) ≤ ((ds.sum : Nat) : ℚ)
  | [], [], _ => by simp [sFmin, sSmin]
  | e :: es, d :: ds, h => by
    obtain ⟨h1, h2⟩ := List.forall₂_cons.mp h
    have ih := sum_lower_g hg es ds h2
    have ha := h1.1
    unfold lerp at ha
    simp only [sFmin, sSmin, List.map_cons, List.sum_cons, Nat.cast_add] at ih ⊢
    have e1 : (1 - p.κ) / p.g * ((1 - c) * ((e.fmin : ℚ) + ((es.map Arc.fmin).sum : ℚ)) +
        c * ((e.smin : ℚ) + ((es.map Arc.smin).sum : ℚ))) =
        (1 - p.κ) * ((1 - c) * (e.fmin : ℚ) + c * (e.smin : ℚ)) / p.g +
        (1 - p.κ) / p.g * ((1 - c) * ((es.map Arc.fmin).sum : ℚ) + c * ((es.map Arc.smin).sum : ℚ)) := by
      field_simp; ring
    rw [e1]; linarith

theorem sum_upper_g {p : DelayPar} {c : ℚ} :
    ∀ (es : List Arc) (ds : List Nat), List.Forall₂ (fun e d => Adm p c e d) es ds →
      ((ds.sum : Nat) : ℚ) ≤ (1 + p.κ) * p.g * ((1 - c) * (sFmax es : ℚ) + c * (sSmax es : ℚ))
  | [], [], _ => by simp [sFmax, sSmax]
  | e :: es, d :: ds, h => by
    obtain ⟨h1, h2⟩ := List.forall₂_cons.mp h
    have ih := sum_upper_g es ds h2
    have ha := h1.2
    unfold lerp at ha
    simp only [sFmax, sSmax, List.map_cons, List.sum_cons, Nat.cast_add] at ih ⊢
    nlinarith [ha, ih]

theorem race_ok_gk {p : DelayPar} (hg : 0 < p.g) {path loop : List Arc}
    (h1 : (1 + p.κ) * p.g * p.g * (sFmax loop : ℚ) ≤ (1 - p.κ) * (sFmin path : ℚ))
    (h2 : (1 + p.κ) * p.g * p.g * (sSmax loop : ℚ) ≤ (1 - p.κ) * (sSmin path : ℚ))
    {c : ℚ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {dp dl : List Nat}
    (hp : List.Forall₂ (fun e d => Adm p c e d) path dp)
    (hl : List.Forall₂ (fun e d => Adm p c e d) loop dl) : dl.sum ≤ dp.sum := by
  have l := sum_lower_g hg path dp hp
  have u := sum_upper_g loop dl hl
  have a1 := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℚ) ≤ 1 - c)
  have a2 := mul_le_mul_of_nonneg_left h2 hc0
  set L := (1 - c) * (sFmax loop : ℚ) + c * (sSmax loop : ℚ)
  set P := (1 - c) * (sFmin path : ℚ) + c * (sSmin path : ℚ)
  have k1 : (1 + p.κ) * p.g * p.g * L ≤ (1 - p.κ) * P := by
    simp only [L, P]; nlinarith [a1, a2]
  have key : (1 + p.κ) * p.g * L ≤ (1 - p.κ) / p.g * P := by
    have e1 : (1 + p.κ) * p.g * L = (1 + p.κ) * p.g * p.g * L / p.g := by field_simp
    have e2 : (1 - p.κ) / p.g * P = (1 - p.κ) * P / p.g := by ring
    rw [e1, e2]; exact div_le_div_of_nonneg_right k1 hg.le
  have h3 : ((dl.sum : Nat) : ℚ) ≤ ((dp.sum : Nat) : ℚ) := le_trans u (le_trans key l)
  exact_mod_cast h3

/-- Integer form of the row condition at g = a/b, κ = m/n (m ≤ n). -/
def rowOKgk (a b m n : Nat) (r : Row) : Bool :=
  (n + m) * a * a * sFmax r.loop ≤ (n - m) * b * b * sFmin r.path &&
    (n + m) * a * a * sSmax r.loop ≤ (n - m) * b * b * sSmin r.path

theorem frontier :
    raceTable.all (rowOKgk 31 20 0 1) = true ∧ raceTable.all (rowOKgk 3 2 0 1) = true ∧
    raceTable.all (rowOKgk 5 4 1 5) = true ∧ raceTable.all (rowOKgk 11 10 3 10) = true ∧
    raceTable.all (rowOKgk 1 1 83 200) = true := by decide +kernel

/-- Negative control: at (g, κ) = (1.6, 0) the binding row fails. -/
theorem frontier_edge : raceTable.all (rowOKgk 8 5 0 1) = false := by decide +kernel

/-- The integer row condition gives `race_ok_gk`'s hypotheses. -/
theorem row_hyps {a b m n : Nat} (hb : 0 < b) (hn : 0 < n) (hmn : m ≤ n) {r : Row} (h : rowOKgk a b m n r = true) :
    (1 + (m : ℚ) / n) * ((a : ℚ) / b) * ((a : ℚ) / b) * (sFmax r.loop : ℚ) ≤ (1 - (m : ℚ) / n) * (sFmin r.path : ℚ) ∧
    (1 + (m : ℚ) / n) * ((a : ℚ) / b) * ((a : ℚ) / b) * (sSmax r.loop : ℚ) ≤ (1 - (m : ℚ) / n) * (sSmin r.path : ℚ) := by
  simp only [rowOKgk, Bool.and_eq_true, decide_eq_true_eq] at h
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have q1 : ((n + m) * a * a * sFmax r.loop : ℚ) ≤ ((n - m : Nat) : ℚ) * b * b * sFmin r.path := by exact_mod_cast h.1
  have q2 : ((n + m) * a * a * sSmax r.loop : ℚ) ≤ ((n - m : Nat) : ℚ) * b * b * sSmin r.path := by exact_mod_cast h.2
  rw [Nat.cast_sub hmn] at q1 q2
  have hd : (0 : ℚ) < n * b * b := by positivity
  constructor
  · have e1 : (1 + (m : ℚ) / n) * ((a : ℚ) / b) * ((a : ℚ) / b) * (sFmax r.loop : ℚ) =
        ((n + m) * a * a * sFmax r.loop : ℚ) / (n * b * b) := by field_simp
    have e2 : (1 - (m : ℚ) / n) * (sFmin r.path : ℚ) = (((n : ℚ) - m) * b * b * sFmin r.path) / (n * b * b) := by
      field_simp
    rw [e1, e2]; exact div_le_div_of_nonneg_right q1 hd.le
  · have e1 : (1 + (m : ℚ) / n) * ((a : ℚ) / b) * ((a : ℚ) / b) * (sSmax r.loop : ℚ) =
        ((n + m) * a * a * sSmax r.loop : ℚ) / (n * b * b) := by field_simp
    have e2 : (1 - (m : ℚ) / n) * (sSmin r.path : ℚ) = (((n : ℚ) - m) * b * b * sSmin r.path) / (n * b * b) := by
      field_simp
    rw [e1, e2]; exact div_le_div_of_nonneg_right q2 hd.le

/-- **The frontier as a statement about behaviours' delays**: at any (g, κ) = (a/b, m/n) at which the table check
passes (e.g. the five points of `frontier`), every row's loop total is at most its path total, for every corner and
every admissible delays. -/
theorem table_race_free_gk {a b m n : Nat} (ha : 0 < a) (hb : 0 < b) (hn : 0 < n) (hmn : m ≤ n)
    (hpt : raceTable.all (rowOKgk a b m n) = true) :
    ∀ r ∈ raceTable, ∀ {p : DelayPar}, p.g = (a : ℚ) / b → p.κ = (m : ℚ) / n →
      ∀ {c : ℚ}, 0 ≤ c → c ≤ 1 → ∀ {dp dl : List Nat},
        List.Forall₂ (fun e d => Adm p c e d) r.path dp → List.Forall₂ (fun e d => Adm p c e d) r.loop dl →
        dl.sum ≤ dp.sum := by
  intro r hr p hg hκ c hc0 hc1 dp dl hp hl
  have h := row_hyps hb hn hmn (List.all_eq_true.mp hpt r hr)
  rw [← hg, ← hκ] at h
  have hg0 : 0 < p.g := by rw [hg]; positivity
  exact race_ok_gk hg0 h.1 h.2 hc0 hc1 hp hl

end Formal.Cells.RaceFrontierPS
