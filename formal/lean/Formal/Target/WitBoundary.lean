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

/-! ## Quiet nodes, moves, liveness -/

/-- A node whose flips all end a period before `b` reads the same in the extension. -/
theorem ext_eq_val (D : Nat → SD) {b P n : Nat} (hP : 0 < P) (hPb : P ≤ b) (hq : ∀ τ ∈ (D n).ts, τ + P < b) :
    ∀ t, ext D b P n t = (D n).val t := by
  intro t
  unfold ext
  by_cases h : t < b
  · rw [wrap_lt h]
  · have hw1 : b - P ≤ wrap b P t := by unfold wrap; rw [if_neg h]; omega
    have hw2 : wrap b P t ≤ t := by
      unfold wrap; rw [if_neg h]
      have := Nat.mod_lt (t - (b - P)) hP
      have := Nat.mod_le (t - (b - P)) P
      omega
    exact ((D n).val_const hw2 (fun x hx h1 => by have := hq x hx; omega)).symm

/-- Four-phase moves of the driver of `r` (rises only while `a` is low, falls only while high),
from a check at each flip of `r`. -/
def movesB (R : Nat) (r a : SD) : Bool := r.ts.all fun τ => !(decide (R + 1 ≤ τ)) || (r.val (τ - 1) == a.val (τ - 1))

theorem reqMoves_of (R : Nat) (r a : SD) (hr : r.ok = true) (h : movesB R r a = true) :
    ReqMoves r.val a.val R := by
  intro t ht hne
  have hm := (flip_iff r hr t).1 hne
  have := List.all_eq_true.1 h _ hm
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq,
    Nat.add_sub_cancel] at this
  rcases this with h1 | h1
  · omega
  · exact h1

/-- Four-phase moves of the driver of `a` (rises only while `r` is high, falls only while low). -/
def ackMovesB (R : Nat) (r a : SD) : Bool := a.ts.all fun τ => !(decide (R + 1 ≤ τ)) || (a.val (τ - 1) != r.val (τ - 1))

theorem ackMoves_of (R : Nat) (r a : SD) (ha : a.ok = true) (h : ackMovesB R r a = true) :
    AckMoves r.val a.val R := by
  intro t ht hne
  have hm := (flip_iff a ha t).1 hne
  have := List.all_eq_true.1 h _ hm
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, bne_iff_ne, ne_eq,
    Nat.add_sub_cancel] at this
  rcases this with h1 | h1
  · omega
  · exact h1

/-- The time-dependent part of a liveness check: some later breakpoint where `f` holds. -/
def later (bp : List Nat) (f : Nat → Bool) (t : Nat) : Bool := bp.any fun e => decide (t < e) && f e

theorem later_inv (bp : List Nat) (f : Nat → Bool) {s t : Nat} (hst : s ≤ t) (h : ∀ x ∈ bp, s < x → t < x) :
    later bp f t = later bp f s := by
  unfold later
  induction bp with
  | nil => rfl
  | cons e l ih =>
    simp only [List.any_cons]
    have he := h e List.mem_cons_self
    rw [ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    congr 1
    by_cases h1 : s < e
    · simp [h1, he h1]
    · simp [h1, show ¬ t < e by omega]

theorem exists_of_later (bp : List Nat) (f : Nat → Bool) (t : Nat) (h : later bp f t = true) :
    ∃ e, t ≤ e ∧ f e = true := by
  obtain ⟨e, _, he⟩ := List.any_eq_true.1 h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at he
  exact ⟨e, Nat.le_of_lt he.1, he.2⟩

/-! ## The environment of a described behaviour -/

theorem val_before (d : SD) {T : Nat} (h : ∀ τ ∈ d.ts, T < τ) : ∀ t, t ≤ T → d.val t = d.val 0 :=
  fun t ht => d.val_const (Nat.zero_le t) (fun x hx _ => by have := h x hx; omega)

theorem val_after (d : SD) {T : Nat} (h : ∀ τ ∈ d.ts, τ ≤ T) : ∀ t, T ≤ t → d.val t = d.val T :=
  fun t ht => d.val_const ht (fun x hx h1 => by have := h x hx; omega)

theorem mem_of_zipIdx {l : List Nat} {n i : Nat} (hm : (n, i) ∈ l.zipIdx) : n ∈ l := by
  have h3 := List.mem_zipIdx hm
  rw [h3.2.2]; exact List.getElem_mem _

theorem busVal_congr (x y : Beh) (l : List Nat) (t : Nat) (h : ∀ n ∈ l, x n t = y n t) :
    busVal x l t = busVal y l t := by
  unfold busVal; congr 1
  apply List.map_congr_left
  rintro ⟨n, i⟩ hm
  simp [h n (mem_of_zipIdx hm)]

theorem busVal_inv (D : Nat → SD) (l bp : List Nat) (hsub : ∀ n ∈ l, ∀ x ∈ (D n).ts, x ∈ bp) {s t : Nat}
    (hst : s ≤ t) (h : ∀ x ∈ bp, s < x → t < x) : busVal (beh D) l t = busVal (beh D) l s := by
  unfold busVal; congr 1
  apply List.map_congr_left
  rintro ⟨n, i⟩ hm
  have := val_const_of_gap (D n) bp (hsub n (mem_of_zipIdx hm)) hst h
  exact congrArg (fun v : Bool => if v = true then 2 ^ i else 0) this

theorem val0_false (d : SD) {R : Nat} (h0 : d.v0 = false) (h : ∀ τ ∈ d.ts, R < τ) : d.val 0 = false := by
  unfold SD.val SD.cnt
  rw [List.filter_eq_nil_iff.2 (fun x hx => by have := h x hx; simp; omega)]
  simp [h0]

/-- The liveness check of a request driver (`ReqLive` with at most `m` rises owed). -/
def reqLiveQ (bp : List Nat) (R m : Nat) (r a : SD) (t : Nat) : Bool :=
  !((r.val t == a.val t) && (r.val t || decide (risesD r R t < m))) || later bp (fun e => r.val e != a.val e) t

def ackLiveQ (bp : List Nat) (r a : SD) (t : Nat) : Bool :=
  (a.val t == r.val t) || later bp (fun e => a.val e == r.val e) t

def offQ (R m : Nat) (r : SD) (t : Nat) : Bool := !(r.val t) || decide (risesD r R t - 1 < m)

def dataQ (D : Nat → SD) (R : Nat) (r a : SD) (data : List Nat) (vals : Nat → Nat) (t : Nat) : Bool :=
  !((r.val t || a.val t) && decide (1 ≤ risesD r R t)) || (busVal (beh D) data t == vals (risesD r R t - 1))

/-- Data present at each rising flip of the request (the `su = 0` clause). -/
def riseDataB (D : Nat → SD) (R : Nat) (r : SD) (data : List Nat) (vals : Nat → Nat) : Bool :=
  r.ts.all fun τ => !(decide (R + 1 ≤ τ) && r.val τ) || (busVal (beh D) data τ == vals (risesD r R τ - 1))

/-- The output acknowledge rises no earlier than `Δo` after its request (checked at each flip). -/
def deltaB (R Δo : Nat) (r a : SD) : Bool :=
  a.ts.all fun τ => !(decide (R + 1 ≤ τ) && a.val τ) ||
    (r.val (τ - Δo) && r.ts.all fun y => !(decide (τ - Δo < y) && decide (y ≤ τ)))

section env
variable (D : Nat → SD) (bp : List Nat) (cap fuel R : Nat)

theorem walk_any (Q : Nat → Bool) (hinv : ∀ s t, s ≤ t → (∀ x ∈ bp, s < x → t < x) → Q t = Q s)
    (hcap : ∀ x ∈ bp, x < cap) (h : walk bp Q cap fuel R = true) : ∀ t, R ≤ t → Q t = true :=
  walk_sound bp Q cap hinv hcap fuel R h

/-- **`Spec.EnvIn` for the described behaviour** (`su = 0`, `m` pairs), from finite checks. -/
theorem envIn_of (ch : InCh) (m : Nat) (vals : Nat → Nat)
    (hok : (D ch.req).ok = true ∧ (D ch.ack).ok = true)
    (hsub : ∀ n ∈ ch.req :: ch.ack :: ch.data, ∀ x ∈ (D n).ts, x ∈ bp) (hcap : ∀ x ∈ bp, x < cap)
    (hlow : (D ch.req).v0 = false ∧ ∀ τ ∈ (D ch.req).ts, R < τ)
    (hmv : movesB R (D ch.req) (D ch.ack) = true)
    (hlive : walk bp (reqLiveQ bp R m (D ch.req) (D ch.ack)) cap fuel R = true)
    (hoff : walk bp (offQ R m (D ch.req)) cap fuel R = true)
    (hrise : riseDataB D R (D ch.req) ch.data vals = true)
    (hdata : walk bp (dataQ D R (D ch.req) (D ch.ack) ch.data vals) cap fuel R = true) :
    EnvIn (beh D) ch R 0 (some m) vals := by
  obtain ⟨hr, ha⟩ := hok
  have sr : ∀ x ∈ (D ch.req).ts, x ∈ bp := hsub _ List.mem_cons_self
  have sa : ∀ x ∈ (D ch.ack).ts, x ∈ bp := hsub _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have sd : ∀ n ∈ ch.data, ∀ x ∈ (D n).ts, x ∈ bp := fun n hn =>
    hsub n (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hn))
  have vr := fun {s t : Nat} (h1 : s ≤ t) (h2 : ∀ x ∈ bp, s < x → t < x) => val_const_of_gap (D ch.req) bp sr h1 h2
  have va := fun {s t : Nat} (h1 : s ≤ t) (h2 : ∀ x ∈ bp, s < x → t < x) => val_const_of_gap (D ch.ack) bp sa h1 h2
  have rr := fun {s t : Nat} (h1 : s ≤ t) (h2 : ∀ x ∈ bp, s < x → t < x) => risesD_const (D ch.req) R bp sr h1 h2
  have hre : ∀ t, rises (beh D ch.req) R t = risesD (D ch.req) R t := rises_eq (D ch.req) hr R
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    simp only [beh]; rw [val_before (D ch.req) hlow.2 t ht]; exact val0_false _ hlow.1 hlow.2
  · exact reqMoves_of R _ _ hr hmv
  · have hQ := walk_any bp cap fuel R _ (fun s t h1 h2 => by
      unfold reqLiveQ; rw [vr h1 h2, va h1 h2, rr h1 h2, later_inv bp _ h1 h2]) hcap hlive
    intro t ht he hm
    have q := hQ t ht
    unfold reqLiveQ at q
    simp only [beh] at he hm
    rw [hre] at hm
    have c : ((D ch.req).val t == (D ch.ack).val t && ((D ch.req).val t || decide (risesD (D ch.req) R t < m))) = true := by
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq]
      exact ⟨he, by rcases hm with h | h; exact Or.inl h; exact Or.inr h⟩
    rw [c] at q
    obtain ⟨e, hte, hfe⟩ := exists_of_later bp _ t (by simpa using q)
    exact ⟨e, hte, by simpa [beh] using hfe⟩
  · have hQ := walk_any bp cap fuel R _ (fun s t h1 h2 => by unfold offQ; rw [vr h1 h2, rr h1 h2]) hcap hoff
    intro t ht h1
    have q := hQ t ht
    unfold offQ at q
    simp only [beh] at h1
    rw [h1] at q
    simp only [Offered, hre]; simpa using q
  · intro t ht h0 h1 s hs1 hs2
    have hst : s = t + 1 := by omega
    subst hst
    simp only [beh] at h0 h1
    have hm := (flip_iff (D ch.req) hr t).1 (by rw [h0, h1]; simp)
    have q := List.all_eq_true.1 hrise _ hm
    rw [hre]
    simp only [h1, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
      beq_iff_eq] at q
    rcases q with (q | q) | q
    · omega
    · simp at q
    · exact q
  · have hQ := walk_any bp cap fuel R _ (fun s t h1 h2 => by
      unfold dataQ; rw [vr h1 h2, va h1 h2, rr h1 h2, busVal_inv D ch.data bp sd h1 h2]) hcap hdata
    intro t ht hra h1
    have q := hQ t ht
    unfold dataQ at q
    simp only [beh] at hra
    rw [hre] at h1 ⊢
    have c : (((D ch.req).val t || (D ch.ack).val t) && decide (1 ≤ risesD (D ch.req) R t)) = true := by
      simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]; exact ⟨hra, h1⟩
    rw [c] at q
    simpa using q

/-- **`Spec.EnvOut` for the described behaviour**, from finite checks. -/
theorem envOut_of (ch : OutCh) (Δo : Nat)
    (hok : (D ch.req).ok = true ∧ (D ch.ack).ok = true)
    (hsub : ∀ n ∈ [ch.req, ch.ack], ∀ x ∈ (D n).ts, x ∈ bp) (hcap : ∀ x ∈ bp, x < cap)
    (hlow : (D ch.ack).v0 = false ∧ ∀ τ ∈ (D ch.ack).ts, R < τ)
    (hmv : ackMovesB R (D ch.req) (D ch.ack) = true)
    (hlive : walk bp (ackLiveQ bp (D ch.req) (D ch.ack)) cap fuel R = true)
    (hd : deltaB R Δo (D ch.req) (D ch.ack) = true) :
    EnvOut (beh D) ch R Δo := by
  obtain ⟨hr, ha⟩ := hok
  have sr : ∀ x ∈ (D ch.req).ts, x ∈ bp := hsub _ List.mem_cons_self
  have sa : ∀ x ∈ (D ch.ack).ts, x ∈ bp := hsub _ (List.mem_cons_of_mem _ List.mem_cons_self)
  refine ⟨?_, ackMoves_of R _ _ ha hmv, ?_, ?_⟩
  · intro t ht
    simp only [beh]; rw [val_before (D ch.ack) hlow.2 t ht]; exact val0_false _ hlow.1 hlow.2
  · have hQ := walk_any bp cap fuel R _ (fun s t h1 h2 => by
      unfold ackLiveQ
      rw [val_const_of_gap _ bp sr h1 h2, val_const_of_gap _ bp sa h1 h2, later_inv bp _ h1 h2]) hcap hlive
    intro t ht hne
    have q := hQ t ht
    unfold ackLiveQ at q
    simp only [beh] at hne
    have c : ((D ch.ack).val t == (D ch.req).val t) = false := by simpa using hne
    rw [c] at q
    obtain ⟨e, hte, hfe⟩ := exists_of_later bp _ t (by simpa using q)
    exact ⟨e, hte, by simpa [beh] using hfe⟩
  · intro t ht h0 h1 s hs1 hs2
    simp only [beh] at h0 h1 ⊢
    have hm := (flip_iff (D ch.ack) ha t).1 (by rw [h0, h1]; simp)
    have q := List.all_eq_true.1 hd _ hm
    simp only [h1, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
      Bool.and_eq_true, List.all_eq_true] at q
    rcases q with (q | q) | ⟨q1, q2⟩
    · omega
    · simp at q
    · rw [(D ch.req).val_const (show t + 1 - Δo ≤ s by omega) (fun y hy h3 => by
          have := q2 y hy; simp at this; omega)]
      exact q1
end env

/-! ## Transfer between behaviours that agree on the channel's nodes -/

theorem envIn_congr (x y : Beh) (ch : InCh) (R su : Nat) (n : Option Nat) (vals : Nat → Nat)
    (h : ∀ v ∈ ch.req :: ch.ack :: ch.data, x v = y v) (hy : EnvIn y ch R su n vals) : EnvIn x ch R su n vals := by
  have hr : x ch.req = y ch.req := h _ List.mem_cons_self
  have ha : x ch.ack = y ch.ack := h _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hd : ∀ t, busVal x ch.data t = busVal y ch.data t := fun t =>
    busVal_congr x y _ t (fun v hv => congrFun (h v (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv))) t)
  unfold EnvIn at hy ⊢; rw [hr, ha]; simp only [hd]; exact hy

theorem envOut_congr (x y : Beh) (ch : OutCh) (R Δo : Nat)
    (h : ∀ v ∈ [ch.req, ch.ack], x v = y v) (hy : EnvOut y ch R Δo) : EnvOut x ch R Δo := by
  have hr : x ch.req = y ch.req := h _ List.mem_cons_self
  have ha : x ch.ack = y ch.ack := h _ (List.mem_cons_of_mem _ List.mem_cons_self)
  unfold EnvOut at hy ⊢; rw [hr, ha]; exact hy

end Formal.Target.Wit
