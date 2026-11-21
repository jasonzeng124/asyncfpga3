import Formal.Core.XAudit.Events7Core

/-!
# Formal.Core.XAudit.Events7Excl — n-ary merges: labels, SelPart, conservation, exclusivity

Probe A-events7 (rebuilt in E7r). See `formal/notes/A-events7.md`.

A **label** `(g, β)` names the transactions of a source in which the select
sequence `sel g` has value `β`. Two labels are **exclusive** (`Excl`) if no
transaction index carries both. Syntactically (`lx`): the same group with
different branches, or two DIFFERENT groups of one select PARTITION, both with
branch `true` (the patterns `00`, `01`, `10` of one 2-bit select are their own
groups with branch `true`).

**SelPart** (hypothesis on `sel`): the groups of one partition are never true
at the same index. It holds for every `sel` derived from one select-value
sequence per select bundle (each group the indicator of one pattern), which is
the `sel` that SelOK ties to the steer gates.

* `lx_sound`: `lx` = true implies `Excl` under SelPart.
* `fsum_filt_le` (n-ary conservation): pairwise exclusive branch counts of one
  count `m` sum to at most `m`. `fodd_filt_le`: at most one of them is odd.
* `excl_stepN` / **`merge_exclN`**: the n-ary `Events4.excl_step` /
  `Events4.merge_excl`.
* negative control `selpart_neg`: without SelPart, `lx`-exclusive labels can
  both count the same event.
-/

namespace Formal.Core.XAudit.Events7

open Formal.Core.XAudit.Events3 (filt filt_add filt_mono filt_even filt_odd)
open Formal.Core.XAudit.Events4 (filt_le)
open Formal.Core.XAudit.Events5

/-- A label: steer group and branch. -/
abbrev Lab := Nat × Bool

/-- **SelPart**: two different groups of one partition are never true at the same index. -/
def SelPart (sel : Nat → Nat → Bool) (parts : List (List Nat)) : Prop :=
  ∀ P ∈ parts, ∀ g1 ∈ P, ∀ g2 ∈ P, g1 ≠ g2 → ∀ k, ¬ (sel g1 k = true ∧ sel g2 k = true)

/-- Semantic exclusivity of two labels. -/
def Excl (sel : Nat → Nat → Bool) (l1 l2 : Lab) : Prop :=
  ∀ k, ¬ (sel l1.1 k = l1.2 ∧ sel l2.1 k = l2.2)

/-- Syntactic exclusivity of two labels (decidable; what the checker evaluates). -/
def lx (parts : List (List Nat)) (l1 l2 : Lab) : Bool :=
  if l1.1 == l2.1 then l1.2 != l2.2
  else l1.2 && l2.2 && parts.any (fun P => P.contains l1.1 && P.contains l2.1)

theorem lx_sound {sel : Nat → Nat → Bool} {parts : List (List Nat)} (hp : SelPart sel parts) {l1 l2 : Lab}
    (h : lx parts l1 l2 = true) : Excl sel l1 l2 := by
  obtain ⟨g1, b1⟩ := l1; obtain ⟨g2, b2⟩ := l2
  unfold lx at h; simp only at h
  intro k ⟨h1, h2⟩
  by_cases hg : g1 = g2
  · subst hg
    simp only [beq_self_eq_true, ite_true, bne_iff_ne, ne_eq] at h
    simp only at h1 h2; rw [h1] at h2; exact h h2
  · have hg' : (g1 == g2) = false := by simpa using hg
    rw [hg'] at h
    simp only [Bool.false_eq_true, ite_false, Bool.and_eq_true, List.any_eq_true] at h
    obtain ⟨⟨hb1, hb2⟩, P, hP, hc1, hc2⟩ := h
    subst hb1; subst hb2
    simp only [List.contains_iff_mem] at hc1 hc2
    exact hp P hP g1 hc1 g2 hc2 hg k ⟨h1, h2⟩

/-! ## Sums over `Fin n` -/

theorem fsum_eq_zero : ∀ (n : Nat) (f : Fin n → Nat), (∀ i, f i = 0) → fsum n f = 0
  | 0, _, _ => rfl
  | n + 1, f, h => by
      simp only [fsum]; rw [h 0, fsum_eq_zero n _ (fun i => h i.succ)]

theorem fsum_add : ∀ (n : Nat) (f g : Fin n → Nat), fsum n (fun i => f i + g i) = fsum n f + fsum n g
  | 0, _, _ => rfl
  | n + 1, f, g => by
      simp only [fsum]; rw [fsum_add n (fun i => f i.succ) (fun i => g i.succ)]; omega

theorem fodd_eq : ∀ (n : Nat) (f : Fin n → Nat), fodd n f = fsum n (fun i => if f i % 2 = 1 then 1 else 0)
  | 0, _ => rfl
  | n + 1, f => by simp only [fodd, fsum]; rw [fodd_eq n (fun i => f i.succ)]

/-- At most one index satisfies a pairwise exclusive predicate. -/
theorem fsum_ind_le_one : ∀ (n : Nat) (e : Fin n → Bool), (∀ i i', i ≠ i' → ¬ (e i = true ∧ e i' = true)) →
    fsum n (fun i => if e i then 1 else 0) ≤ 1
  | 0, _, _ => Nat.zero_le _
  | n + 1, e, h => by
      simp only [fsum]
      by_cases h0 : e 0 = true
      · have hz : fsum n (fun i => if e i.succ then 1 else 0) = 0 :=
          fsum_eq_zero n _ (fun i => by
            have := h 0 i.succ (Fin.succ_ne_zero i).symm
            have : e i.succ = false := by cases hh : e i.succ <;> simp_all
            simp [this])
        rw [hz]; split <;> omega
      · have := fsum_ind_le_one n (fun i => e i.succ) (fun i i' hne => h i.succ i'.succ (fun hh => hne (Fin.succ_inj.mp hh)))
        simp only [h0, Bool.false_eq_true, ite_false]; omega

/-- `f ≤ g` pointwise with `Σ g ≤ Σ f`: then `f = g`. -/
theorem fsum_le_eq : ∀ (n : Nat) (f g : Fin n → Nat), (∀ i, f i ≤ g i) → fsum n g ≤ fsum n f → ∀ i, f i = g i
  | 0, _, _, _, _, i => i.elim0
  | n + 1, f, g, hle, hs, i => by
      simp only [fsum] at hs
      have hm := fsum_mono n (fun i => f i.succ) (fun i => g i.succ) (fun i => hle i.succ)
      have h0 := hle 0
      have e0 : f 0 = g 0 := by omega
      have ih := fsum_le_eq n (fun i => f i.succ) (fun i => g i.succ) (fun i => hle i.succ) (by omega)
      refine Fin.cases e0 (fun k => ih k) i

/-- Split one term off a sum. -/
theorem fsum_split : ∀ (n : Nat) (f : Fin n → Nat) (a : Fin n),
    fsum n f = f a + fsum n (fun i => if i = a then 0 else f i)
  | 0, _, a => a.elim0
  | n + 1, f, a => by
      simp only [fsum]
      refine Fin.cases ?_ (fun k => ?_) a
      · simp only [ite_true]
        have : (fun i : Fin n => if i.succ = (0 : Fin (n + 1)) then 0 else f i.succ) = (fun i => f i.succ) := by
          funext i; rw [if_neg (Fin.succ_ne_zero i)]
        rw [this]; omega
      · have ih := fsum_split n (fun i => f i.succ) k
        have e : (fun i : Fin n => if i.succ = k.succ then 0 else f i.succ) = (fun i => if i = k then 0 else f i.succ) := by
          funext i; simp only [Fin.succ_inj]
        rw [if_neg (Fin.succ_ne_zero k).symm, e]; omega

/-! ## Conservation over pairwise exclusive labels -/

section
variable {sel : Nat → Nat → Bool}

theorem filt_odd_sel (s : Nat → Bool) (β : Bool) (m : Nat) (h : filt s β m % 2 = 1) : s (m / 2) = β := by
  obtain ⟨k, hk | hk⟩ : ∃ k, m = 2 * k ∨ m = 2 * k + 1 := ⟨m / 2, by omega⟩
  · subst hk; have := filt_even s β k; omega
  · subst hk
    rw [filt_odd] at h
    have := filt_even s β k
    rw [show (2 * k + 1) / 2 = k by omega]
    by_cases hs : s k = β
    · exact hs
    · rw [if_neg hs] at h; omega

/-- **n-ary conservation**: pairwise exclusive branch counts of one count `m` sum to at most `m`. -/
theorem fsum_filt_le (n : Nat) (lab : Fin n → Lab) (hex : ∀ i i', i ≠ i' → Excl sel (lab i) (lab i')) :
    ∀ m, fsum n (fun i => filt (sel (lab i).1) (lab i).2 m) ≤ m
  | 0 => by
      rw [fsum_eq_zero n (fun i => filt (sel (lab i).1) (lab i).2 0) (fun i => rfl)]; exact Nat.le_refl 0
  | m + 1 => by
      have ih := fsum_filt_le n lab hex m
      have e : (fun i => filt (sel (lab i).1) (lab i).2 (m + 1)) =
          (fun i => filt (sel (lab i).1) (lab i).2 m + (if decide (sel (lab i).1 (m / 2) = (lab i).2) then 1 else 0)) := by
        funext i; simp only [filt, decide_eq_true_eq]
      rw [e, fsum_add]
      have := fsum_ind_le_one n (fun i => decide (sel (lab i).1 (m / 2) = (lab i).2))
        (fun i i' hne ⟨h1, h2⟩ => hex i i' hne (m / 2) ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩)
      omega

/-- At most one of pairwise exclusive branch counts of one count is odd. -/
theorem fodd_filt_le (n : Nat) (lab : Fin n → Lab) (hex : ∀ i i', i ≠ i' → Excl sel (lab i) (lab i')) (m : Nat) :
    fodd n (fun i => filt (sel (lab i).1) (lab i).2 m) ≤ 1 := by
  rw [fodd_eq]
  have hle := fsum_mono n (fun i => if filt (sel (lab i).1) (lab i).2 m % 2 = 1 then 1 else 0)
    (fun i => if decide (sel (lab i).1 (m / 2) = (lab i).2) then 1 else 0) (fun i => by
      by_cases h : filt (sel (lab i).1) (lab i).2 m % 2 = 1
      · have := filt_odd_sel _ _ _ h; simp [h, this]
      · simp only [h, ite_false]; exact Nat.zero_le _)
  have := fsum_ind_le_one n (fun i => decide (sel (lab i).1 (m / 2) = (lab i).2))
    (fun i i' hne ⟨h1, h2⟩ => hex i i' hne (m / 2) ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩)
  omega

/-- **The n-ary exclusivity step.** Arms `xs` below pairwise exclusive branch
counts of `m`, an earlier exclusive sample `ys ≤ xs`, and `m ≤ Σ ys + 1`: then
at most one arm is odd. (Either the arms did not move, or they equal the branch
counts, of which at most one is odd.) -/
theorem excl_stepN (n : Nat) (lab : Fin n → Lab) (hex : ∀ i i', i ≠ i' → Excl sel (lab i) (lab i'))
    (xs ys : Fin n → Nat) (m : Nat) (hu : ∀ i, xs i ≤ filt (sel (lab i).1) (lab i).2 m)
    (hy : ∀ i, ys i ≤ xs i) (hw : m ≤ fsum n ys + 1) (hprev : fodd n ys ≤ 1) : fodd n xs ≤ 1 := by
  have h1 := fsum_mono n _ _ hu
  have h2 := fsum_filt_le n lab hex m
  have h3 := fsum_mono n _ _ hy
  by_cases hc : fsum n xs ≤ fsum n ys
  · have e := fsum_le_eq n ys xs hy hc
    have : xs = ys := funext fun i => (e i).symm
    rw [this]; exact hprev
  · have e := fsum_le_eq n xs (fun i => filt (sel (lab i).1) (lab i).2 m) hu (by omega)
    have : xs = (fun i => filt (sel (lab i).1) (lab i).2 m) := funext e
    rw [this]; exact fodd_filt_le n lab hex m

/-- **`merge_exclN`** (the n-ary `Events4.merge_excl`): monotone arm counts
`xs i t`, each below its branch count of `m t` (pairwise exclusive labels),
and `m t ≤ Σ xs (σ t) + 1` for an earlier sample `σ t < t`: then at most one
arm is odd at every sample. No timing condition on the arms. -/
theorem merge_exclN (n : Nat) (lab : Fin n → Lab) (hex : ∀ i i', i ≠ i' → Excl sel (lab i) (lab i'))
    (xs : Fin n → Nat → Nat) (m σ : Nat → Nat) (hσ : ∀ t, 0 < t → σ t < t)
    (hmono : ∀ i a c, a ≤ c → xs i a ≤ xs i c)
    (hu : ∀ i t, xs i t ≤ filt (sel (lab i).1) (lab i).2 (m t))
    (hw : ∀ t, 0 < t → m t ≤ fsum n (fun i => xs i (σ t)) + 1)
    (hz : ∀ i, xs i 0 = 0) : ∀ t, fodd n (fun i => xs i t) ≤ 1 := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h
      rw [fodd_eq, fsum_eq_zero n _ (fun i => by simp [hz i])]; exact Nat.zero_le _
    · have hs := hσ t h
      exact excl_stepN n lab hex (fun i => xs i t) (fun i => xs i (σ t)) (m t) (fun i => hu i t)
        (fun i => hmono i _ _ (Nat.le_of_lt hs)) (hw t h) (ih _ hs)

end

/-- NEGATIVE CONTROL: the labels `(0, true)` and `(1, true)` are syntactically
exclusive under the partition `[[0, 1]]`, but for a `sel` violating SelPart
(both groups always true) their branch counts of one event sum to 2 > 1:
without SelPart, n-ary conservation fails. -/
theorem selpart_neg :
    lx [[0, 1]] (0, true) (1, true) = true ∧ ¬ SelPart (fun _ _ => true) [[0, 1]] ∧
    fsum 2 (fun i => filt ((fun _ _ => true) ((if i.val = 0 then ((0 : Nat), true) else (1, true)) : Lab).1)
      ((if i.val = 0 then ((0 : Nat), true) else (1, true)) : Lab).2 1) = 2 := by
  refine ⟨by decide, fun h => ?_, by decide⟩
  exact h [0, 1] (by simp) 0 (by simp) 1 (by simp) (by decide) 0 ⟨rfl, rfl⟩

end Formal.Core.XAudit.Events7
