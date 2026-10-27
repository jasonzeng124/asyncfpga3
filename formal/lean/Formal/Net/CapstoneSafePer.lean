import Formal.Net.Handshake

/-!
# Probe C-8m: periodic streams (O2, part 2: list and count lemmas)

`perL L d k` repeats the period `L` forever (`d` if `L` is empty). Counting a property over
a periodic stream (`cnt_per`) and the rank of a selected element in a filtered period
(`filter_rank`, `sel_rank`) are what turn the one-invocation histories of a GcdHw run into
total solutions of the Ops token equations.
-/

namespace Formal.Net.CapSafe
open Formal.Net.Handshake

def cntL (P : Nat → Bool) (L : List Nat) (j : Nat) : Nat := ((L.take j).filter P).length

def perL (L : List Nat) (d : Nat) (k : Nat) : Nat := if L = [] then d else L.getD (k % L.length) 0

theorem cntL_zero (P : Nat → Bool) (L : List Nat) : cntL P L 0 = 0 := by simp [cntL]

theorem cntL_cons_succ (P : Nat → Bool) (x : Nat) (L : List Nat) (j : Nat) :
    cntL P (x :: L) (j + 1) = (if P x then 1 else 0) + cntL P L j := by
  unfold cntL; simp only [List.take_succ_cons, List.filter_cons]
  split <;> simp [Nat.add_comm]

theorem cnt_take (P : Nat → Bool) : ∀ (L : List Nat) (j : Nat), j ≤ L.length →
    cnt (fun i => P (L.getD i 0)) j = cntL P L j := by
  intro L j
  induction j with
  | zero => intro _; simp [cnt, cntL]
  | succ j ih =>
    intro hj
    simp only [cnt]
    rw [ih (by omega)]
    unfold cntL
    rw [List.take_add_one, List.filter_append]
    have : L[j]? = some (L.getD j 0) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show j < L.length by omega)]
    rw [this]; simp only [Option.toList_some, List.filter_cons, List.filter_nil]
    split <;> simp

theorem cnt_add (f : Nat → Bool) (a : Nat) : ∀ b, cnt f (a + b) = cnt f a + cnt (fun i => f (a + i)) b := by
  intro b
  induction b with
  | zero => simp [cnt]
  | succ b ih => rw [show a + (b + 1) = (a + b) + 1 by omega]; simp only [cnt]; rw [ih]; omega

theorem cnt_periodic (f : Nat → Bool) (n : Nat) (hf : ∀ i, f (i + n) = f i) :
    ∀ q j, cnt f (q * n + j) = q * cnt f n + cnt f j := by
  have hshift : ∀ q i, f (q * n + i) = f i := by
    intro q
    induction q with
    | zero => intro i; simp
    | succ q ih => intro i; rw [show (q + 1) * n + i = (q * n + i) + n by rw [Nat.succ_mul]; omega, hf, ih]
  have hs : ∀ q, (fun i => f (q * n + i)) = f := fun q => funext (hshift q)
  have hm : ∀ q, cnt f (q * n) = q * cnt f n := by
    intro q
    induction q with
    | zero => simp [cnt]
    | succ q ih => rw [Nat.succ_mul, cnt_add, hs q, ih, Nat.succ_mul]
  intro q j; rw [cnt_add, hs q, hm q]

theorem perL_ne {L : List Nat} (h : L ≠ []) (d k : Nat) : perL L d k = L.getD (k % L.length) 0 := by
  simp [perL, h]

theorem perL_mod {L : List Nat} (h : L ≠ []) (d k : Nat) : perL L d k = perL L d (k % L.length) := by
  rw [perL_ne h, perL_ne h, Nat.mod_mod]

theorem len_pos {L : List Nat} (h : L ≠ []) : 0 < L.length := List.length_pos_iff.mpr h

/-- Counting a property along a periodic stream. -/
theorem cnt_per (P : Nat → Bool) {L : List Nat} (h : L ≠ []) (d k : Nat) :
    cnt (fun i => P (perL L d i)) k = (k / L.length) * cntL P L L.length + cntL P L (k % L.length) := by
  have hn := len_pos h
  have hf : ∀ i, P (perL L d (i + L.length)) = P (perL L d i) := by
    intro i; simp only [perL_ne h, Nat.add_mod_right]
  have := cnt_periodic (fun i => P (perL L d i)) L.length hf (k / L.length) (k % L.length)
  rw [Nat.div_add_mod' k L.length] at this
  rw [this]
  have e : ∀ j, j ≤ L.length → cnt (fun i => P (perL L d i)) j = cntL P L j := by
    intro j hj
    rw [← cnt_take P L j hj]
    apply cnt_congr_le; intro i hi
    simp only [perL_ne h]
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [e _ (Nat.le_refl _), e _ (Nat.le_of_lt (Nat.mod_lt _ hn))]
where
  cnt_congr_le {f g : Nat → Bool} {j : Nat} (h : ∀ i, i < j → f i = g i) : cnt f j = cnt g j := by
    induction j with
    | zero => rfl
    | succ j ih => simp only [cnt]; rw [ih (fun i hi => h i (by omega)), h j (by omega)]

/-- The selected element of a filtered list sits at its rank. -/
theorem filter_rank (P : Nat → Bool) : ∀ (L : List Nat) (j : Nat), j < L.length →
    P (L.getD j 0) = true → (L.filter P).getD (cntL P L j) 0 = L.getD j 0 := by
  intro L
  induction L with
  | nil => intro j hj; simp at hj
  | cons x L ih =>
    intro j hj hp
    cases j with
    | zero =>
      simp only [List.getD_cons_zero] at hp ⊢
      simp [cntL, List.filter_cons, hp]
    | succ j =>
      rw [cntL_cons_succ]
      simp only [List.getD_cons_succ] at hp ⊢
      have := ih j (by simp at hj; omega) hp
      cases hx : P x
      · simp only [List.filter_cons, hx]; simpa using this
      · simp only [List.filter_cons, hx, ↓reduceIte]
        rw [Nat.add_comm, List.getD_cons_succ]; exact this

theorem filter_len (P : Nat → Bool) (L : List Nat) : (L.filter P).length = cntL P L L.length := by
  simp [cntL]

/-- The same for a branch's routed output: the data of every token whose condition routes it
to side `b`, in order. -/
def sel (b : Bool) (C D : List Nat) : List Nat :=
  (C.zip D).filterMap (fun p => if (p.1 % 2 == 1) = b then some p.2 else none)

def tst (b : Bool) (v : Nat) : Bool := (v % 2 == 1) == b

theorem sel_rank (b : Bool) : ∀ (C D : List Nat) (j : Nat), C.length = D.length → j < C.length →
    tst b (C.getD j 0) = true → (sel b C D).getD (cntL (tst b) C j) 0 = D.getD j 0 := by
  intro C
  induction C with
  | nil => intro D j _ hj; simp at hj
  | cons x C ih =>
    intro D j hl hj hp
    cases D with
    | nil => simp at hl
    | cons y D =>
      cases j with
      | zero =>
        simp only [List.getD_cons_zero] at hp ⊢
        have : (x % 2 == 1) = b := by simpa [tst] using hp
        simp [sel, cntL, this]
      | succ j =>
        rw [cntL_cons_succ]
        simp only [List.getD_cons_succ] at hp ⊢
        have := ih D j (by simpa using hl) (by simp at hj; omega) hp
        unfold sel at this ⊢
        simp only [List.zip_cons_cons, List.filterMap_cons]
        by_cases hx : (x % 2 == 1) = b
        · have h2 : tst b x = true := by simp [tst, hx]
          simp only [hx, h2, ↓reduceIte]
          rw [Nat.add_comm, List.getD_cons_succ]; exact this
        · have h2 : tst b x = false := by simp [tst]; exact hx
          simp only [hx, h2, ↓reduceIte, Bool.false_eq_true, Nat.zero_add]; exact this

theorem sel_len (b : Bool) : ∀ (C D : List Nat), C.length = D.length →
    (sel b C D).length = cntL (tst b) C C.length := by
  intro C
  induction C with
  | nil => intro D _; simp [sel, cntL]
  | cons x C ih =>
    intro D hl
    cases D with
    | nil => simp at hl
    | cons y D =>
      have := ih D (by simpa using hl)
      rw [List.length_cons, cntL_cons_succ]
      unfold sel at this ⊢
      simp only [List.zip_cons_cons, List.filterMap_cons]
      by_cases hx : (x % 2 == 1) = b
      · have : tst b x = true := by simp [tst, hx]
        simp [hx, this]; omega
      · have : tst b x = false := by simp [tst]; exact hx
        simp [hx, this]; omega

end Formal.Net.CapSafe
