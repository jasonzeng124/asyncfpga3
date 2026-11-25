import Formal.Cells.CertPS
import Formal.Cells.RaceCornersPS

/-!
# Formal.Cells.CertMarginPS — from a hold certificate to a race margin, generically

Shard B, 2026-11-07.

## Problem, plainly
`CertPS.cert_sound` says each certificate row holds on a window `win i` whose end is a min over branches. For a race
obligation we need it as a sum: "the acknowledge keeps its value until the cause + the path's summed lower bands".
And the comparison with the storage node's feedback loop should follow from two integer facts on arc sums, at every
corner, as in `RaceTablePS.race_ok_of_sums`.

## Proved (standard axioms)
* `psum`: the summed lower bands along a certificate's causal path (the pins not labelled static).
* `win_end_ge`: if the static premises last long enough (`E k ≥ e + PS`, `PS` ≥ every `psum`), each row's window
  ends no earlier than `e + psum i`.
* `lo_sum_ge`, `hi_sum_le`: the integer lower / upper window ends of an arc list, summed, are at least / at most
  the corner-linear real sums `(1-κ)·lerp(ΣFAST_MIN, ΣSLOW_MIN, c)` / `(1+κ)·lerp(ΣFAST_MAX, ΣSLOW_MAX, c)` (g = 1).
* `margin_of_sums`: `283·ΣFAST_MAX(loop) ≤ 117·ΣFAST_MIN(path)` and the same with SLOW imply, for g = 1,
  every κ ≤ 83/200 and every corner, `Σ hi(loop) ≤ Σ lo(path)`.
-/

namespace Formal.Cells.CertMarginPS
open Formal.Target Formal.Cells.CertPS Formal.Cells.RaceCertPS Formal.Cells.RaceCornersPS

/-- The (first) causal pin of a row: a controlling pin not labelled static. -/
def pathPin (row : CRow) : Nat := (row.r.P.find? fun j => (row.lab j).kind != 1).getD 0

/-- The summed lower bands along the causal path, by row index. -/
def psum (p : DelayPar) (c : ℚ) (rows : List CRow) (i : Nat) : Nat :=
  let row := rows.getD i default
  let j := pathPin row
  row.r.lo p c j + (if h : (row.lab j).kind = 2 ∧ (row.lab j).k < i then psum p c rows (row.lab j).k else 0)
termination_by i
decreasing_by exact h.2

/-- Each row has exactly one non-static controlling pin, in `P`. -/
def singlePath (rows : List CRow) : Bool :=
  rows.all fun row => (row.r.P.filter fun j => (row.lab j).kind != 1).length == 1

theorem foldr_min_ge (f : Nat → Nat) (b v : Nat) (hb : v ≤ b) :
    ∀ (l : List Nat), (∀ j ∈ l, v ≤ f j) → v ≤ l.foldr (fun j m => min m (f j)) b
  | [], _ => by simpa using hb
  | x :: l, h => by
    simp only [List.foldr_cons]
    exact le_min (foldr_min_ge f b v hb l fun j hj => h j (List.mem_cons_of_mem _ hj)) (h x List.mem_cons_self)

theorem pathPin_spec {row : CRow} (h : (row.r.P.filter fun j => (row.lab j).kind != 1).length = 1) :
    pathPin row ∈ row.r.P ∧ (row.lab (pathPin row)).kind ≠ 1 ∧
      ∀ j ∈ row.r.P, (row.lab j).kind ≠ 1 → j = pathPin row := by
  obtain ⟨y, hy⟩ : ∃ y, (row.r.P.filter fun j => (row.lab j).kind != 1) = [y] := by
    match hl : (row.r.P.filter fun j => (row.lab j).kind != 1), h with
    | [y], _ => exact ⟨y, rfl⟩
  have hmem : y ∈ row.r.P.filter fun j => (row.lab j).kind != 1 := by rw [hy]; simp
  rw [List.mem_filter] at hmem
  have hfind : row.r.P.find? (fun j => (row.lab j).kind != 1) = some y := by
    rw [← List.head?_filter, hy]; rfl
  have hpp : pathPin row = y := by simp [pathPin, hfind]
  rw [hpp]
  refine ⟨hmem.1, by simpa using hmem.2, fun j hj hk => ?_⟩
  have : j ∈ row.r.P.filter fun j => (row.lab j).kind != 1 := List.mem_filter.mpr ⟨hj, by simpa using hk⟩
  rw [hy] at this; simpa using this

/-- **The window end is at least the cause plus the path's lower bands** (static premises long enough). -/
theorem win_end_ge {p : DelayPar} {c : ℚ} (P : Prem) (rows : List CRow) (hok : certOK P rows = true)
    (hsp : singlePath rows = true) (a e : Nat) (E : Nat → Nat) (PS : Nat)
    (hPS : ∀ i, i < rows.length → psum p c rows i ≤ PS) (hE : ∀ k, e + PS ≤ E k) (hB : e + PS ≤ BIG) :
    ∀ i, i < rows.length → e + psum p c rows i ≤ (win p c a e E rows i).2 := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hi
  have hok' := hok
  simp only [certOK, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hok'
  obtain ⟨-, hl⟩ := hok' i hi
  have hsp' : (((rows.getD i default).r.P.filter fun j => ((rows.getD i default).lab j).kind != 1).length = 1) := by
    simp only [singlePath, List.all_eq_true, beq_iff_eq] at hsp
    exact hsp _ (List.getD_eq_getElem?_getD .. ▸ by simp [List.getElem?_eq_getElem hi])
  obtain ⟨hppP, hppk, huniq⟩ := pathPin_spec hsp'
  set row := rows.getD i default
  have hwin : win p c a e E rows i =
      rowWin p c a e E (fun k => if k < i then win p c a e E rows k else (a + 1, a)) row := by rw [win]
  have hpsum : psum p c rows i = row.r.lo p c (pathPin row) +
      (if h : (row.lab (pathPin row)).kind = 2 ∧ (row.lab (pathPin row)).k < i then psum p c rows (row.lab (pathPin row)).k
        else 0) := by rw [psum]
  have hps := hPS i hi
  rw [hwin]
  simp only [rowWin]
  apply foldr_min_ge _ _ _ (by unfold BIG at hB ⊢; omega)
  intro j hj
  simp only [labOK, List.all_eq_true] at hl
  have hlj := hl j hj
  by_cases hk1 : (row.lab j).kind = 1
  · simp only [srcWin, hk1, Nat.one_ne_zero, if_false, if_true]
    have := hE (row.lab j).k
    omega
  · have hjp := huniq j hj hk1
    subst hjp
    by_cases hk0 : (row.lab (pathPin row)).kind = 0
    · have hn : ¬ ((row.lab (pathPin row)).kind = 2 ∧ (row.lab (pathPin row)).k < i) := by omega
      rw [dif_neg hn] at hpsum
      simp only [srcWin, hk0, if_true]
      omega
    · simp only [hk0, hk1, if_false, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hlj
      obtain ⟨⟨⟨hk2, hlt⟩, -⟩, -⟩ := hlj
      have hy : (row.lab (pathPin row)).kind = 2 ∧ (row.lab (pathPin row)).k < i := ⟨hk2, hlt⟩
      rw [dif_pos hy] at hpsum
      simp only [srcWin, hk0, hk1, if_false, hlt, if_true]
      have := ih _ hlt (by omega)
      omega

theorem lerp_sum_min (κ c : ℚ) : ∀ l : List Arc, (l.map fun e => (1 - κ) * lerp e.fmin e.smin c / 1).sum =
    (1 - κ) * ((1 - c) * (sFmin l : ℚ) + c * (sSmin l : ℚ))
  | [] => by simp [sFmin, sSmin]
  | e :: l => by
    have ih := lerp_sum_min κ c l
    simp only [List.map_cons, List.sum_cons, ih, sFmin, sSmin, Nat.cast_add, lerp] at ih ⊢
    push_cast
    ring

theorem lerp_sum_max (κ c : ℚ) : ∀ l : List Arc, (l.map fun e => (1 + κ) * lerp e.fmax e.smax c * 1).sum =
    (1 + κ) * ((1 - c) * (sFmax l : ℚ) + c * (sSmax l : ℚ))
  | [] => by simp [sFmax, sSmax]
  | e :: l => by
    have ih := lerp_sum_max κ c l
    simp only [List.map_cons, List.sum_cons, ih, sFmax, sSmax, Nat.cast_add, lerp] at ih ⊢
    push_cast
    ring

open Formal.Cells.Ua1Static in
theorem lo_sum_ge {κ c : ℚ} (hk1 : κ ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (l : List Arc) :
    (1 - κ) * ((1 - c) * (sFmin l : ℚ) + c * (sSmin l : ℚ)) ≤ (((l.map (lo 1 κ c)).sum.toNat : ℕ) : ℚ) := by
  have h1 := sum_lo_ge (g := 1) (κ := κ) (c := c) l
  have h2 := toNat_ge (l.map (lo 1 κ c)).sum
  have h3 := lerp_sum_min κ c l
  linarith

open Formal.Cells.Ua1Static in
theorem hi_sum_le {κ c : ℚ} (hk0 : 0 ≤ κ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (l : List Arc) :
    (((l.map (hi 1 κ c)).sum.toNat : ℕ) : ℚ) ≤ (1 + κ) * ((1 - c) * (sFmax l : ℚ) + c * (sSmax l : ℚ)) := by
  have h1 := sum_hi_le (g := 1) (κ := κ) (c := c) l
  rw [lerp_sum_max κ c l] at h1
  refine toNat_le h1 ?_
  have : (0 : ℚ) ≤ 1 - c := by linarith
  positivity

/-- **Margin from two integer arc-sum facts** (g = 1, κ ≤ 83/200, every corner). -/
theorem margin_of_sums {κ c : ℚ} (hk0 : 0 ≤ κ) (hk : κ ≤ 83 / 200) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    {path loop : List Arc} (h1 : 283 * sFmax loop ≤ 117 * sFmin path) (h2 : 283 * sSmax loop ≤ 117 * sSmin path) :
    (((loop.map (Formal.Cells.Ua1Static.hi 1 κ c)).sum.toNat : ℕ) : ℚ) ≤
      (((path.map (Formal.Cells.Ua1Static.lo 1 κ c)).sum.toNat : ℕ) : ℚ) := by
  have u := hi_sum_le hk0 hc0 hc1 loop
  have l := lo_sum_ge (κ := κ) (by linarith) hc0 hc1 path
  have q1 : (283 : ℚ) * (sFmax loop : ℚ) ≤ 117 * (sFmin path : ℚ) := by exact_mod_cast h1
  have q2 : (283 : ℚ) * (sSmax loop : ℚ) ≤ 117 * (sSmin path : ℚ) := by exact_mod_cast h2
  have f1 : (0 : ℚ) ≤ sFmax loop := by positivity
  have f2 : (0 : ℚ) ≤ sSmax loop := by positivity
  have a1 := mul_le_mul_of_nonneg_left q1 (by linarith : (0 : ℚ) ≤ 1 - c)
  have a2 := mul_le_mul_of_nonneg_left q2 hc0
  -- (1+κ)·X ≤ (283/117)(1-κ)... use κ ≤ 83/200: (1+κ)·117 ≤ 283·(1-κ)
  have hk' : (1 + κ) * 117 ≤ 283 * (1 - κ) := by nlinarith
  nlinarith [mul_nonneg (sub_nonneg.2 hc1) f1, mul_nonneg hc0 f2, mul_nonneg hk0 (mul_nonneg (sub_nonneg.2 hc1) f1),
    mul_nonneg hk0 (mul_nonneg hc0 f2)]

end Formal.Cells.CertMarginPS
