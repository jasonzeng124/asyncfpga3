import Formal.Target.Witness

/-!
# Formal.Target.WitBoundary — boundary properties of a described behaviour

Shard A, 2026-11-01. Generic lemmas to discharge `Spec.Env`, `Spec.ArbOK` and the failure of
`Spec.Correct` for a behaviour given by signal descriptions (`Witness.SD`):
* `flip_iff`: with strictly increasing flip times, the value changes at `t+1` iff `t+1` is a flip;
* `rises_eq`: `Spec.rises` (a recursion over every ps) equals a count over the flip list;
* `walk_sound`: a property that only changes at listed breakpoints holds at every `t ≥ lo` once it
  holds at `lo` and at each breakpoint (`walk` checks that);
* `arbOK_of`: H_ARB(T) from "every flip of `q` follows a flip of an input by less than `T`".
-/

namespace Formal.Target.Wit
open Formal.Target

/-- `l` is strictly increasing and every element is above `m`. -/
def incr : Nat → List Nat → Bool
  | _, [] => true
  | m, x :: l => decide (m < x) && incr x l

/-- Flip times strictly increasing and positive (checked by `decide`). -/
def SD.ok (d : SD) : Bool := incr 0 d.ts

theorem incr_gt : ∀ (m : Nat) (l : List Nat), incr m l = true → ∀ x ∈ l, m < x
  | _, [], _ => fun x hx => by cases hx
  | m, y :: l, h => by
    simp only [incr, Bool.and_eq_true, decide_eq_true_eq] at h
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 (incr_gt y l h.2 x hx)

theorem incr_nodup : ∀ (m : Nat) (l : List Nat), incr m l = true → l.Nodup
  | _, [], _ => List.nodup_nil
  | m, y :: l, h => by
    simp only [incr, Bool.and_eq_true] at h
    exact List.nodup_cons.2 ⟨fun hy => Nat.lt_irrefl _ (incr_gt y l h.2 y hy), incr_nodup y l h.2⟩

theorem nodup_of_ok (d : SD) (h : d.ok = true) : d.ts.Nodup := incr_nodup 0 d.ts h

/-- Count when the predicate changes at one point `a` only, from false to `p a`. -/
theorem countP_step (p q : Nat → Bool) (a : Nat) (hpq : ∀ x, x ≠ a → p x = q x) (hq : q a = false) :
    ∀ l : List Nat, l.Nodup → l.countP p = l.countP q + (if a ∈ l ∧ p a = true then 1 else 0)
  | [], _ => by simp
  | y :: l, hn => by
    have ih := countP_step p q a hpq hq l (List.nodup_cons.1 hn).2
    have hy := (List.nodup_cons.1 hn).1
    rw [List.countP_cons, List.countP_cons, ih]
    by_cases e : y = a
    · subst e
      simp [hq, hy]
    · have e' : a ≠ y := Ne.symm e
      simp only [List.mem_cons, e', false_or, hpq y e]
      omega

theorem len_filter_step (p q : Nat → Bool) (a : Nat) (hpq : ∀ x, x ≠ a → p x = q x) (hq : q a = false)
    (l : List Nat) (hn : l.Nodup) :
    (l.filter p).length = (l.filter q).length + (if a ∈ l ∧ p a = true then 1 else 0) := by
  rw [← List.countP_eq_length_filter, ← List.countP_eq_length_filter]
  exact countP_step p q a hpq hq l hn

theorem cnt_succ (d : SD) (h : d.ok = true) (t : Nat) :
    d.cnt (t + 1) = d.cnt t + (if t + 1 ∈ d.ts then 1 else 0) := by
  unfold SD.cnt
  rw [len_filter_step (fun x => decide (x ≤ t + 1)) (fun x => decide (x ≤ t)) (t + 1)
    (fun x hx => by simp only [decide_eq_decide]; omega) (by simp) d.ts (nodup_of_ok d h)]
  simp

/-- **The value changes exactly at the flips.** -/
theorem flip_iff (d : SD) (h : d.ok = true) (t : Nat) : d.val (t + 1) ≠ d.val t ↔ t + 1 ∈ d.ts := by
  unfold SD.val
  rw [cnt_succ d h]
  by_cases hm : t + 1 ∈ d.ts
  · simp only [hm, if_true, iff_true]
    generalize d.cnt t = m
    cases d.v0 <;> rcases Nat.mod_two_eq_zero_or_one m with hm2 | hm2 <;> simp [Nat.add_mod, hm2]
  · simp [hm]

/-- The rising flips in `(R, t]`. -/
def rp (d : SD) (R t : Nat) (x : Nat) : Bool := decide (R < x) && decide (x ≤ t) && d.val x

def risesD (d : SD) (R t : Nat) : Nat := (d.ts.filter (rp d R t)).length

theorem risesD_succ (d : SD) (h : d.ok = true) (R t : Nat) :
    risesD d R (t + 1) = risesD d R t +
      (if R ≤ t ∧ d.val t = false ∧ d.val (t + 1) = true then 1 else 0) := by
  unfold risesD
  rw [len_filter_step (rp d R (t + 1)) (rp d R t) (t + 1)
    (fun x hx => by unfold rp; congr 2; simp only [decide_eq_decide]; omega)
    (by unfold rp; simp) d.ts (nodup_of_ok d h)]
  congr 1
  have hf := flip_iff d h t
  unfold rp
  by_cases hm : t + 1 ∈ d.ts
  · have hne := hf.2 hm
    by_cases hv : d.val (t + 1) = true
    · have : d.val t = false := by cases h2 : d.val t <;> simp_all
      by_cases hR : R ≤ t
      · simp [hm, hv, this, hR, show R < t + 1 by omega]
      · simp [hm, hv, hR, show ¬ R < t + 1 by omega]
    · have hv' : d.val (t + 1) = false := by simpa using hv
      simp [hm, hv']
  · have heq : d.val (t + 1) = d.val t := by
      by_contra hne; exact hm (hf.1 hne)
    by_cases hv : d.val t = false
    · simp [hm, heq, hv]
    · simp [hm, heq, hv]

/-- **`Spec.rises` of a described signal is a count over its flips.** -/
theorem rises_eq (d : SD) (h : d.ok = true) (R : Nat) : ∀ t, rises d.val R t = risesD d R t
  | 0 => by
    unfold risesD; simp only [rises]
    symm; rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]; intro x _; simp [rp]; omega
  | t + 1 => by
    simp only [rises]; rw [rises_eq d h R t, risesD_succ d h]

/-! ## A property that changes only at listed breakpoints -/

/-- Check `Q` at `t` and at every breakpoint after it, up to `cap` (checked last). -/
def walk (bp : List Nat) (Q : Nat → Bool) (cap : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, t => if cap ≤ t then Q t else Q t && walk bp Q cap fuel (nextAfter bp t cap)

theorem walk_sound (bp : List Nat) (Q : Nat → Bool) (cap : Nat)
    (hinv : ∀ s t, s ≤ t → (∀ x ∈ bp, s < x → t < x) → Q t = Q s) (hcap : ∀ x ∈ bp, x < cap) :
    ∀ fuel lo, walk bp Q cap fuel lo = true → ∀ t, lo ≤ t → Q t = true := by
  intro fuel
  induction fuel with
  | zero => intro lo h; simp [walk] at h
  | succ fuel ih =>
    intro lo h t hlt
    simp only [walk] at h
    split at h
    · rw [hinv lo t hlt (fun x hx _ => by have := hcap x hx; omega)]; exact h
    · simp only [Bool.and_eq_true] at h
      let n := nextAfter bp lo cap
      by_cases ht : t < n
      · rw [hinv lo t hlt (fun x hx hlx => by have := nextAfter_gap bp lo cap x hx hlx; omega)]; exact h.1
      · exact ih n h.2 t (by omega)

/-- Two descriptions' values are constant on a gap of the merged flip list. -/
theorem val_const_of_gap (d : SD) (bp : List Nat) (hsub : ∀ x ∈ d.ts, x ∈ bp) {s t : Nat} (hst : s ≤ t)
    (h : ∀ x ∈ bp, s < x → t < x) : d.val t = d.val s :=
  d.val_const hst (fun x hx => h x (hsub x hx))

theorem risesD_const (d : SD) (R : Nat) (bp : List Nat) (hsub : ∀ x ∈ d.ts, x ∈ bp) {s t : Nat} (hst : s ≤ t)
    (h : ∀ x ∈ bp, s < x → t < x) : risesD d R t = risesD d R s := by
  unfold risesD; congr 1
  apply List.filter_congr; intro x hx
  have := h x (hsub x hx)
  unfold rp
  by_cases hxs : x ≤ s
  · simp [hxs, Nat.le_trans hxs hst]
  · have : ¬ x ≤ t := by omega
    simp [hxs, this]

/-! ## H_ARB from flips -/

/-- Every flip of `q` follows some flip of one of `ins` by less than `T`. -/
def arbFlipsOK (T : Nat) (q : SD) (ins : List SD) : Bool :=
  q.ts.all fun τ => ins.any fun d => d.ts.any fun τ' => decide (τ < τ' + T ∧ τ' ≤ τ)

theorem constOn_of_noflip (d : SD) (h : d.ok = true) {t1 t2 : Nat} (hno : ∀ τ ∈ d.ts, t1 < τ → t2 < τ) :
    ConstOn d.val t1 t2 := fun t h1 h2 => d.val_const h1 (fun x hx hx1 => by have := hno x hx hx1; omega)

theorem noflip_of_constOn (d : SD) (h : d.ok = true) {t1 t2 : Nat} (hc : ConstOn d.val t1 t2) :
    ∀ τ ∈ d.ts, t1 < τ → t2 < τ := by
  intro τ hτ h1
  by_contra h2
  have hf := (flip_iff d h (τ - 1)).2 (by rw [show τ - 1 + 1 = τ by omega]; exact hτ)
  rw [show τ - 1 + 1 = τ by omega] at hf
  exact hf ((hc τ (by omega) (by omega)).trans (hc (τ - 1) (by omega) (by omega)).symm)

theorem arbOK_one (T : Nat) (q : SD) (ins : List SD) (hq : q.ok = true) (hi : ∀ d ∈ ins, d.ok = true)
    (hA : arbFlipsOK T q ins = true) (t1 t2 : Nat) (hc : ∀ d ∈ ins, ConstOn d.val t1 t2) :
    ConstOn q.val (t1 + T) t2 := by
  apply constOn_of_noflip q hq
  intro τ hτ h1
  by_contra h2
  have := List.all_eq_true.1 hA τ hτ
  obtain ⟨d, hd, hd'⟩ := List.any_eq_true.1 this
  obtain ⟨τ', hτ', h'⟩ := List.any_eq_true.1 hd'
  have h' := of_decide_eq_true h'
  have := noflip_of_constOn d (hi d hd) (hc d hd) τ' hτ' (by omega)
  omega

end Formal.Target.Wit
