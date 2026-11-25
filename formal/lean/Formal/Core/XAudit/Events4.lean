import Formal.Core.XAudit.Events3

/-!
# Formal.Core.XAudit.Events4 — choice between DIFFERENT sources, branch-aware walks, guarded pins and delay lines

Probe A-events4. See `formal/notes/A-events4.md`.

`Events3` proved choice whose two arms reconverge from ONE source (steer → arms
→ OR → the same pin), with exclusivity from a timing condition (`Skew`). The
routed gcd_hw control needs four more facts, each proved here as a lemma about
counts (the same counter semantics: a wire with reset value 0 that has fired
`m` times reads `ph false m`):

* **W-E5a, merge of different sources** (`or_sum`, `orL_sum`): the OR of arms
  that are never both high has the SUMMED count. Exclusivity is not assumed:
  `merge_excl` proves it by induction on the merge's samples from three
  count facts that the analysis certifies structurally — each arm fires only in
  its own branch of one steer source `S` (`x_b ≤ filt_b m`), and `S` cannot
  start a new transaction before the merge has seen the previous one
  (`m ≤ y0 + y1 + 1`, a walk from `S` back to the merge with at most one
  token). **No timing condition**: the arm skew cancels, because `S`'s
  acknowledge is the merge itself (this is why `Events3.Skew` was conservative,
  W-E5b).
* **W-E5c/d, branch-aware walks** (`sub_step`, `sub_step'`, `reconv`): a walk
  from a steer arm back to its consumer may pass THROUGH the acknowledge merge
  of that steer by subtracting the other branch (`sub_step`, conservation
  `filt_add`); a walk may cross a merge whose arms are distinct branches of one
  source by jumping to that source (`reconv`). With these, loop entry (mux),
  loop exit (steer arm leaving the loop) and the cond_br / mux / fork shapes
  of bdc's control get `Back` certificates.
* **Guarded pins** (`cel_guard_ph`): `x_ack = C(j0, z_ack)` of `bd_mux` (and the
  arbiter's `A_b = C(g_b, A0)`) reads a pin that fires in EVERY transaction
  while the stage fires only in branch-`b` ones. Such a pin is not a counter
  pin (it can run two phases ahead), but while the guard pin `j0` has not
  advanced the C-element holds whatever the guarded pin does. The lemma
  reduces the stage to `cel_ph` under one hypothesis (`hguard`): when the guard
  has advanced, the guarded pin reads its branch count. Discharging `hguard`
  is a timing condition (entry/exit, notes §3), NOT proved here (Wip).
* **Delay lines** (`and_val`, `or_val'`, `andCnt_mono`, `orCnt_mono`): bdc's
  FASTFALL/FASTRISE request delays are AND/OR trees of copies of ONE source.
  If the copies' counts form a CONTIGUOUS set `[lo, hi]` (no missing value),
  the AND reads `ph false (min hi (lo + lo % 2))` and the OR reads
  `ph false (max lo (hi - 1 + hi % 2))`; both counts are monotone and lie in
  `[lo, hi]`, so the min-plus walks of `Events2` go through a delay line with
  the band `[min lo, max hi]`. Contiguity is certified per gate (two
  representatives within one event: a window shorter than the source's
  minimum event spacing).

Nothing here is a hypothesis-free statement about a netlist; the integration
of these lemmas into one `Beh4.safe` over the parsed netlist (`design_beh4`) is
open (`Wip/Events4.lean`).
-/

namespace Formal.Core.XAudit.Events4

open Formal.Core.XAudit.Events (ph)
open Formal.Core.XAudit.Events2 (cel cel_hold cel_ph fmin fmin_le le_fmin)
open Formal.Core.XAudit.Events3 (filt filt_add filt_mono filt_even filt_odd ph_false_eq)

/-! ## 1. Merge of different sources: the sum (W-E5a) -/

/-- **The OR of two arms that are never both high has the summed count.** -/
theorem or_sum (a b : Nat) (h : ¬ (a % 2 = 1 ∧ b % 2 = 1)) :
    (ph false a || ph false b) = ph false (a + b) := by
  rw [ph_false_eq, ph_false_eq, ph_false_eq]
  by_cases ha : a % 2 = 1 <;> by_cases hb : b % 2 = 1
  · exact absurd ⟨ha, hb⟩ h
  · have : (a + b) % 2 = 1 := by omega
    simp [ha, hb, this]
  · have : (a + b) % 2 = 1 := by omega
    simp [ha, hb, this]
  · have : ¬ (a + b) % 2 = 1 := by omega
    simp [ha, hb, this]

/-- Number of odd entries (arms currently high). -/
def nOdd : List Nat → Nat
  | [] => 0
  | x :: l => (if x % 2 = 1 then 1 else 0) + nOdd l

theorem sum_even_of_nOdd (l : List Nat) (h : nOdd l = 0) : l.sum % 2 = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [nOdd] at h
    have hx : ¬ x % 2 = 1 := by intro hx; rw [if_pos hx] at h; omega
    rw [if_neg hx] at h
    have := ih (by omega)
    simp only [List.sum_cons]; omega

theorem any_false_of_nOdd (l : List Nat) (h : nOdd l = 0) : (l.any fun x => ph false x) = false := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [nOdd] at h
    have hx : ¬ x % 2 = 1 := by intro hx; rw [if_pos hx] at h; omega
    rw [if_neg hx] at h
    rw [List.any_cons, ih (by omega), ph_false_eq]
    simp [hx]

/-- **n-ary merge** (an OR LUT of several arms): with at most one arm high, the
OR has the summed count. -/
theorem orL_sum (l : List Nat) (h : nOdd l ≤ 1) :
    (l.any fun x => ph false x) = ph false l.sum := by
  induction l with
  | nil => simp [ph_false_eq]
  | cons x l ih =>
    simp only [nOdd] at h
    simp only [List.any_cons, List.sum_cons]
    by_cases hx : x % 2 = 1
    · rw [if_pos hx] at h
      have h0 : nOdd l = 0 := by omega
      rw [any_false_of_nOdd l h0]
      have := sum_even_of_nOdd l h0
      rw [ph_false_eq, ph_false_eq]
      have : (x + l.sum) % 2 = 1 := by omega
      simp [hx, this]
    · rw [if_neg hx] at h
      rw [ih (by omega)]
      rw [ph_false_eq, ph_false_eq, ph_false_eq]
      by_cases hs : l.sum % 2 = 1
      · have : (x + l.sum) % 2 = 1 := by omega
        simp [hx, hs, this]
      · have : ¬ (x + l.sum) % 2 = 1 := by omega
        simp [hx, hs, this]

/-- Only the current transaction can be odd: the two branch counts of one
source are never both odd. -/
theorem filt_not_both_odd (sel : Nat → Bool) (m : Nat) :
    ¬ (filt sel false m % 2 = 1 ∧ filt sel true m % 2 = 1) := by
  obtain ⟨k, hk | hk⟩ : ∃ k, m = 2 * k ∨ m = 2 * k + 1 := ⟨m / 2, by omega⟩
  · subst hk
    have := filt_even sel false k; omega
  · subst hk
    rw [filt_odd, filt_odd]
    have := filt_even sel false k; have := filt_even sel true k
    cases sel k <;> simp <;> omega

/-- The exclusivity step: if the arms see at most the branch counts of `m`,
`m` is at most one ahead of the merge's earlier sample `(y0, y1)`, and that
earlier sample was exclusive, then the current one is. -/
theorem excl_step (sel : Nat → Bool) (x0 x1 y0 y1 m : Nat)
    (hu0 : x0 ≤ filt sel false m) (hu1 : x1 ≤ filt sel true m)
    (hy0 : y0 ≤ x0) (hy1 : y1 ≤ x1) (hw : m ≤ y0 + y1 + 1)
    (hprev : ¬ (y0 % 2 = 1 ∧ y1 % 2 = 1)) : ¬ (x0 % 2 = 1 ∧ x1 % 2 = 1) := by
  have hadd := filt_add sel m
  have hf := filt_not_both_odd sel m
  omega

/-- **W-E5a: exclusivity of a merge by conservation, for every behaviour of the
counts.** `x0 t`, `x1 t`: the arm counts at the merge's `t`-th sample
(monotone); `m t`: a count of the steer source `S` with each arm below its
branch count; `σ t < t`: the merge's earlier sample that `S` had to wait for
(the walk `S → … → merge` with one token). Then the arms are never both high:
the merge reads the SUM (`or_sum`). No timing condition on the arms. -/
theorem merge_excl (sel : Nat → Bool) (x0 x1 m σ : Nat → Nat)
    (hσ : ∀ t, 0 < t → σ t < t)
    (hm0 : ∀ a b, a ≤ b → x0 a ≤ x0 b) (hm1 : ∀ a b, a ≤ b → x1 a ≤ x1 b)
    (hu0 : ∀ t, x0 t ≤ filt sel false (m t)) (hu1 : ∀ t, x1 t ≤ filt sel true (m t))
    (hw : ∀ t, 0 < t → m t ≤ x0 (σ t) + x1 (σ t) + 1)
    (hz0 : x0 0 = 0) (_hz1 : x1 0 = 0) :
    ∀ t, ¬ (x0 t % 2 = 1 ∧ x1 t % 2 = 1) := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h; rw [hz0]; omega
    · have hs := hσ t h
      exact excl_step sel (x0 t) (x1 t) (x0 (σ t)) (x1 (σ t)) (m t) (hu0 t) (hu1 t)
        (hm0 _ _ (Nat.le_of_lt hs)) (hm1 _ _ (Nat.le_of_lt hs)) (hw t h) (ih _ hs)

/-! ## 2. Branch-aware walks (W-E5c, W-E5d) -/

/-- **SUB**: a walk from the steer source `S` that reaches the acknowledge merge
(`mS ≤ a0 + a1 + k`) continues through the branch-`false` arm, the other arm
being bounded by the other branch (`a1 ≤ filt true mS'`, `mS' ≤ mS`). -/
theorem sub_step (sel : Nat → Bool) (mS mS' a0 a1 k : Nat) (h : mS ≤ a0 + a1 + k)
    (h1 : a1 ≤ filt sel true mS') (hle : mS' ≤ mS) : filt sel false mS ≤ a0 + k := by
  have := filt_add sel mS
  have := filt_mono sel true hle
  omega

/-- SUB through the branch-`true` arm. -/
theorem sub_step' (sel : Nat → Bool) (mS mS' a0 a1 k : Nat) (h : mS ≤ a0 + a1 + k)
    (h0 : a0 ≤ filt sel false mS') (hle : mS' ≤ mS) : filt sel true mS ≤ a1 + k := by
  have := filt_add sel mS
  have := filt_mono sel false hle
  omega

/-- **R3, reconvergence**: a merge whose arms are the two branches of one
source counts no more than that source. -/
theorem reconv (sel : Nat → Bool) (a0 a1 m0 m1 m : Nat) (h0 : a0 ≤ filt sel false m0)
    (h1 : a1 ≤ filt sel true m1) (h0m : m0 ≤ m) (h1m : m1 ≤ m) : a0 + a1 ≤ m := by
  have := filt_mono sel false h0m
  have := filt_mono sel true h1m
  have := filt_add sel m
  omega

/-- Walk steps keep the filter: `filt` is monotone and grows by at most the
token added on a pin. -/
theorem filt_add_le (sel : Nat → Bool) (b : Bool) (x k : Nat) :
    filt sel b (x + k) ≤ filt sel b x + k := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    have := Formal.Core.XAudit.Events3.filt_succ_le sel b (x + k)
    rw [← Nat.add_assoc]; omega

theorem filt_le (sel : Nat → Bool) (b : Bool) (x : Nat) : filt sel b x ≤ x := by
  have := filt_add sel x; cases b <;> omega

/-! ## 3. Guarded pins (bd_mux acknowledges, arbiter A1/A2) -/

/-- **A guarded C-element.** Pins other than `gd` read their counts; the guard
pin `g` (≠ `gd`) is a counter pin; the guarded pin `gd` reads its count only
when the guard has advanced past the feedback (`hguard`). Then the stage still
equals the C-element of the counts. While the guard has not advanced, the
C-element holds whatever `gd` does (`cel_hold`). -/
theorem cel_guard_ph (v : Bool) (n : Nat) (hn : 0 < n) (p : Fin n → Nat) (x : Fin n → Bool)
    (mq : Nat) (g gd : Fin n) (hgd : g ≠ gd)
    (hx : ∀ i, i ≠ gd → x i = ph v (p i)) (h1 : ∀ i, mq ≤ p i) (h2 : ∀ i, p i ≤ mq + 1)
    (hguard : p g = mq + 1 → x gd = ph v (p gd)) :
    cel x (ph v mq) = ph v (fmin n p) := by
  by_cases hg : p g = mq
  · have hm : fmin n p = mq := by
      have := fmin_le n p g; have := le_fmin n p hn mq h1; omega
    rw [hm]
    exact cel_hold _ _ ⟨g, by rw [hx g hgd, hg]⟩
  · have hall : ∀ i, x i = ph v (p i) := by
      intro i
      by_cases hi : i = gd
      · subst hi; exact hguard (by have := h1 g; have := h2 g; omega)
      · exact hx i hi
    rw [show x = fun i => ph v (p i) from funext hall]
    exact cel_ph v n hn p mq h1 h2

/-! ## 4. Delay lines: AND / OR of copies of one source -/

/-- Count of an AND of copies whose counts fill `[lo, hi]`. -/
def andCnt (lo hi : Nat) : Nat := min hi (lo + lo % 2)

/-- Count of an OR of copies whose counts fill `[lo, hi]`. -/
def orCnt (lo hi : Nat) : Nat := max lo (hi - 1 + hi % 2)

/-- The copies' counts lie in `[lo, hi]`, attain both ends, and miss no value
in between (CONTIGUITY). -/
def Contig (l : List Nat) (lo hi : Nat) : Prop :=
  (∀ x ∈ l, lo ≤ x ∧ x ≤ hi) ∧ lo ∈ l ∧ hi ∈ l ∧ ∀ k, lo ≤ k → k ≤ hi → k ∈ l

/-- **FASTFALL line**: the AND of contiguous copies reads `andCnt`. -/
theorem and_val (l : List Nat) (lo hi : Nat) (h : Contig l lo hi) :
    (l.all fun x => ph false x) = ph false (andCnt lo hi) := by
  obtain ⟨hb, hlo, hhi, hc⟩ := h
  have hle : lo ≤ hi := (hb lo hlo).2
  have lowF : ∀ k, k ∈ l → k % 2 = 0 → (l.all fun x => ph false x) = false := by
    intro k hk he
    exact List.all_eq_false.mpr ⟨k, hk, by rw [ph_false_eq]; simp [he]⟩
  unfold andCnt
  by_cases he : lo % 2 = 0
  · rw [lowF lo hlo he, show min hi (lo + lo % 2) = lo by omega, ph_false_eq]; simp [he]
  · by_cases heq : hi = lo
    · subst heq
      have hodd : hi % 2 = 1 := by omega
      have hall : (l.all fun x => ph false x) = true := by
        rw [List.all_eq_true]
        intro x hx
        have := hb x hx
        have : x = hi := by omega
        subst this; rw [ph_false_eq]; simp [hodd]
      rw [hall, show min hi (hi + hi % 2) = hi by omega, ph_false_eq]; simp [hodd]
    · rw [lowF (lo + 1) (hc _ (by omega) (by omega)) (by omega),
        show min hi (lo + lo % 2) = lo + 1 by omega, ph_false_eq]
      have h1 : ¬ (lo + 1) % 2 = 1 := by omega
      simp [h1]

/-- **FASTRISE line**: the OR of contiguous copies reads `orCnt`. -/
theorem or_val' (l : List Nat) (lo hi : Nat) (h : Contig l lo hi) :
    (l.any fun x => ph false x) = ph false (orCnt lo hi) := by
  obtain ⟨hb, hlo, hhi, hc⟩ := h
  have hle : lo ≤ hi := (hb lo hlo).2
  have highT : ∀ k, k ∈ l → k % 2 = 1 → (l.any fun x => ph false x) = true := by
    intro k hk ho
    exact List.any_eq_true.mpr ⟨k, hk, by rw [ph_false_eq]; simp [ho]⟩
  unfold orCnt
  by_cases ho : hi % 2 = 1
  · rw [highT hi hhi ho, show max lo (hi - 1 + hi % 2) = hi by omega, ph_false_eq]; simp [ho]
  · by_cases heq : hi = lo
    · subst heq
      have hall : (l.any fun x => ph false x) = false := by
        rw [List.any_eq_false]
        intro x hx
        have := hb x hx
        have : x = hi := by omega
        subst this; rw [ph_false_eq]; simp [ho]
      rw [hall, show max hi (hi - 1 + hi % 2) = hi by omega, ph_false_eq]; simp [ho]
    · rw [highT (hi - 1) (hc _ (by omega) (by omega)) (by omega),
        show max lo (hi - 1 + hi % 2) = hi - 1 by omega, ph_false_eq]
      have h1 : (hi - 1) % 2 = 1 := by omega
      simp [h1]

theorem andCnt_mono {lo hi lo' hi' : Nat} (h1 : lo ≤ lo') (h2 : hi ≤ hi') :
    andCnt lo hi ≤ andCnt lo' hi' := by unfold andCnt; omega

theorem orCnt_mono {lo hi lo' hi' : Nat} (h1 : lo ≤ lo') (h2 : hi ≤ hi') :
    orCnt lo hi ≤ orCnt lo' hi' := by unfold orCnt; omega

/-- Both line counts lie in `[lo, hi]`: walks through a line use `[min lo, max hi]`. -/
theorem andCnt_mem (lo hi : Nat) (h : lo ≤ hi) : lo ≤ andCnt lo hi ∧ andCnt lo hi ≤ hi := by
  unfold andCnt; omega

theorem orCnt_mem (lo hi : Nat) (h : lo ≤ hi) : lo ≤ orCnt lo hi ∧ orCnt lo hi ≤ hi := by
  unfold orCnt; omega

/-- Contiguity of a union: two contiguous sets whose representatives are within
one event are together contiguous (the per-gate certificate of the analysis). -/
theorem contig_union (a b : List Nat) (la ha lb hb : Nat) (hA : Contig a la ha) (hB : Contig b lb hb)
    (ra rb : Nat) (hra : ra ∈ a) (hrb : rb ∈ b) (hr : ra ≤ rb + 1 ∧ rb ≤ ra + 1) :
    Contig (a ++ b) (min la lb) (max ha hb) := by
  obtain ⟨ba, la_mem, ha_mem, ca⟩ := hA
  obtain ⟨bb, lb_mem, hb_mem, cb⟩ := hB
  have ra_b := ba ra hra
  have rb_b := bb rb hrb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have := ba x hx; omega
    · have := bb x hx; omega
  · rcases Nat.le_total la lb with h | h
    · rw [Nat.min_eq_left h]; exact List.mem_append_left _ la_mem
    · rw [Nat.min_eq_right h]; exact List.mem_append_right _ lb_mem
  · rcases Nat.le_total ha hb with h | h
    · rw [Nat.max_eq_right h]; exact List.mem_append_right _ hb_mem
    · rw [Nat.max_eq_left h]; exact List.mem_append_left _ ha_mem
  · intro k hk1 hk2
    by_cases h1 : la ≤ k ∧ k ≤ ha
    · exact List.mem_append_left _ (ca k h1.1 h1.2)
    · by_cases h2 : lb ≤ k ∧ k ≤ hb
      · exact List.mem_append_right _ (cb k h2.1 h2.2)
      · exfalso; omega

/-! ## 5. Negative controls -/

/-- NEGATIVE CONTROL (merge): two arms high at once (both odd) — the OR reads 1
but the summed count is even: a token is lost. `merge_excl`'s hypotheses are
what excludes it. -/
theorem or_sum_neg : (ph false 1 || ph false 1) ≠ ph false (1 + 1) := by decide

/-- NEGATIVE CONTROL (exclusivity): `excl_step` without its walk fact
`m ≤ y0 + y1 + 1`. With `sel = [0, 1]` and `m = 4`, arms `(1, 1)` lie under
the branch counts of `m` and the earlier sample `(0, 0)` was exclusive, but `m`
is two transactions ahead of it: both arms are odd (both high). -/
theorem excl_step_neg :
    let sel : Nat → Bool := fun k => k == 1
    1 ≤ filt sel false 4 ∧ 1 ≤ filt sel true 4 ∧ ¬ (4 ≤ 0 + 0 + 1) ∧
      (1 % 2 = 1 ∧ 1 % 2 = 1) := by decide

/-- NEGATIVE CONTROL (delay line): copies with a GAP (counts 1 and 3, no 2:
the line's slow copy still shows the previous high while the fast copy shows
the next one) read AND = 1, but `andCnt 1 3 = 2` is even. -/
theorem and_val_neg : ([1, 3].all fun x => ph false x) ≠ ph false (andCnt 1 3) := by decide

/-- NEGATIVE CONTROL (guard): a C-element whose guard has advanced (`j0 = 1`,
feedback 0) and whose guarded pin still shows the PREVIOUS transaction's high
fires — the count model (guarded pin's branch count 0) says it must not. -/
theorem guard_neg : cel (n := 2) (fun i => if i.val = 0 then true else true) false ≠
    ph false (fmin 2 (fun i => if i.val = 0 then 1 else 0)) := by decide

end Formal.Core.XAudit.Events4
