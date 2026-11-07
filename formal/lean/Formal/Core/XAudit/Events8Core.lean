import Formal.Core.XAudit.Events7Beh

/-!
# Formal.Core.XAudit.Events8Core — the guarded count as a count of the guarded source (probe WE4g)

See `formal/notes/A-events8.md`.

`Events7.design_verdict7` holds for EVERY monotone guarded count `gc` and assumes
GuardOK about the chosen one. Here the count is FIXED and GuardOK is reduced to
three count-level facts per guarded pin that the log can certify (`Events8Cert`).

* `lineCnt`: what the AND / OR of a delay line's copies reads, as a count
  (`andCnt` / `orCnt` of the copies' minimum and maximum; one copy: its count).
* `gcnt`: the guarded count = the BRANCH count `filt (sel grp) br` of that line count,
  in the guard's label `(grp, br)`. (Not `fmax` of the copies, as `Wip/Events7.lean`
  proposed: with an AND line whose copies are split between `2k` and `2k+1` the pin
  reads LOW while `filt (fmax …)` may be odd.)
* `M8`: the counts of a node family with that guarded count built in (a recursion in
  time, as `Beh7.M`); `beh8`: the `Beh7` whose `gc` is the running maximum of
  `gcnt` of `M8`; **`beh8_M`**: its counts ARE `M8`, so **`beh8_gc`**: its `gc` is
  `gcnt` of its own copy counts (`x.cm`).
* `GuardCnt`: the count-level guard facts (bound, contiguity of the copies, and the
  LABEL fact: once the guard has advanced, an odd line count is a transaction of the
  guard's branch). **`guard_val`**: under them the guarded pin reads its count.
* **`safe8`**: `Beh7.safe` with GuardOK replaced, per guarded pin, by `GuardCnt`
  (certified pins) or by GuardOK's own two conjuncts (uncertified pins, `GuardPin`).
-/

namespace Formal.Core.XAudit.Events8

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Warp)
open Formal.Core.XAudit.Events (ph ph_zero ph_off offB)
open Formal.Core.XAudit.Events2 (cel fmin fmin_le le_fmin fmin_mono fmin_mem ph_xor)
open Formal.Core.XAudit.Events3 (filt filt_mono filt_even filt_odd)
open Formal.Core.XAudit.Events4 (andCnt orCnt)
open Formal.Core.XAudit.Events5
open Formal.Core.XAudit.Events7

/-! ## 1. Line counts and the guarded count -/

/-- The count a delay line (copies' counts `m`, operator `op`: AND = true) reads,
for a source with reset value 0. -/
def lineCnt (op : Bool) (n : Nat) (m : Fin n → Nat) : Nat :=
  if op then andCnt (fmin n m) (fmax n m) else orCnt (fmin n m) (fmax n m)

theorem fmin_le_fmax (n : Nat) (m : Fin n → Nat) (hn : 0 < n) : fmin n m ≤ fmax n m := by
  obtain ⟨i, hi⟩ := fmin_mem n m hn; rw [hi]; exact le_fmax n m i

theorem lineCnt_ge (op : Bool) (n : Nat) (m : Fin n → Nat) (hn : 0 < n) : fmin n m ≤ lineCnt op n m := by
  have := fmin_le_fmax n m hn
  unfold lineCnt andCnt orCnt; split <;> omega

theorem lineCnt_le (op : Bool) (n : Nat) (m : Fin n → Nat) (hn : 0 < n) : lineCnt op n m ≤ fmax n m := by
  have := fmin_le_fmax n m hn
  unfold lineCnt andCnt orCnt; split <;> omega

theorem lineCnt_mono (op : Bool) (n : Nat) (hn : 0 < n) {m m' : Fin n → Nat} (h : ∀ i, m i ≤ m' i) :
    lineCnt op n m ≤ lineCnt op n m' := by
  have h1 := fmin_mono _ _ _ hn h
  have h2 := fmax_mono _ _ _ hn h
  unfold lineCnt andCnt orCnt; split <;> omega

/-- The value of a delay line of a reset-0 source with contiguous copies. -/
theorem lineCnt_val (op : Bool) (n : Nat) (hn : 0 < n) (m : Fin n → Nat) (hc : ContigF n m) :
    (if op then fall n (fun i => ph false (m i)) else fany n (fun i => ph false (m i))) =
      ph false (lineCnt op n m) := by
  unfold lineCnt
  cases op
  · simp only [Bool.false_eq_true, ite_false]; exact orF_val n hn m hc
  · simp only [ite_true]; exact andF_val n hn m hc

/-- **The guarded count** of guarded pin `p` of stage `j` from its copies' counts:
the branch-`br` count (label `(grp, br)`) of the line count. -/
def gcnt {N : Nat} (net : Net4 N) (sel : Nat → Nat → Bool) (j : Fin N) (p : Fin (net.ar j))
    (m : Fin (net.nc j p) → Nat) : Nat :=
  filt (sel (net.grp j p)) (net.br j p) (lineCnt (net.op j p) (net.nc j p) m)

theorem gcnt_mono {N : Nat} (net : Net4 N) (sel : Nat → Nat → Bool) (j : Fin N) (p : Fin (net.ar j))
    {m m' : Fin (net.nc j p) → Nat} (h : ∀ i, m i ≤ m' i) : gcnt net sel j p m ≤ gcnt net sel j p m' :=
  filt_mono _ _ (lineCnt_mono _ _ (net.nc_pos j p) h)

/-- A branch count has the parity of the count when the open transaction (if any)
is of that branch. -/
theorem filt_par (s : Nat → Bool) (β : Bool) (n : Nat) (h : n % 2 = 1 → s (n / 2) = β) :
    filt s β n % 2 = n % 2 := by
  obtain ⟨k, hk | hk⟩ : ∃ k, n = 2 * k ∨ n = 2 * k + 1 := ⟨n / 2, by omega⟩
  · subst hk; have := filt_even s β k; omega
  · subst hk
    have hs := h (by omega)
    rw [show (2 * k + 1) / 2 = k by omega] at hs
    rw [filt_odd, if_pos hs]; have := filt_even s β k; omega

/-- A transaction `k` of the other branch adds nothing to the branch count. -/
theorem filt_skip (s : Nat → Bool) (β : Bool) (k : Nat) (hk : s k ≠ β) :
    filt s β (2 * k + 1) = filt s β (2 * k) ∧ filt s β (2 * k + 2) = filt s β (2 * k) := by
  have e1 : filt s β (2 * k + 1) = filt s β (2 * k) := by rw [filt_odd, if_neg hk]; omega
  refine ⟨e1, ?_⟩
  show filt s β (2 * k + 1 + 1) = _
  rw [filt, e1, show (2 * k + 1) / 2 = k by omega, if_neg hk]; omega

/-- If the branch count passed `filt (2k)` and transaction `k` is of the other
branch, the count passed `2k + 2`. -/
theorem filt_gap (s : Nat → Bool) (β : Bool) (k n : Nat) (hk : s k ≠ β)
    (h : filt s β (2 * k) + 1 ≤ filt s β n) : 2 * k + 3 ≤ n := by
  rcases Nat.lt_or_ge n (2 * k + 3) with hc | hc
  · have h1 : filt s β n ≤ filt s β (2 * k + 2) := filt_mono s β (by omega)
    have h2 := (filt_skip s β k hk).2
    omega
  · exact hc

/-! ## 2. The counts with the guarded count built in -/

section M8
variable {N : Nat} {net : Net4 N} {b : Bands4 net} (sel : Nat → Nat → Bool) {cc : Fin N → Sig}
  (nd : ∀ j, ND7 net b cc j)

/-- `Beh7.pc` with the guarded count `gcnt`. -/
def pc8 (j : Fin N) (p : Fin (net.ar j)) (m : Fin (net.nc j p) → Nat) : Nat :=
  match net.pk j p with
  | PK.multi => if net.op j p then andCnt (fmin _ m) (fmax _ m) else orCnt (fmin _ m) (fmax _ m)
  | PK.filt => filt (sel (net.grp j p)) (net.br j p) (fmax _ m)
  | PK.guard => gcnt net sel j p m
  | PK.plain => fmax _ m

/-- **The counts** of the node family `nd` (as `Beh7.M`, with `pc8`). -/
def M8 (t : Nat) (j : Fin N) : Nat :=
  if h : (nd j).F t < t then
    if net.mg j then
      fsum (net.ar j) (fun p => pc8 sel j p (fun i =>
        if h0 : (nd j).G p i ((nd j).F t) < (nd j).F t then M8 ((nd j).G p i ((nd j).F t)) (net.src j p) else 0)
          + net.off j p)
    else if (nd j).r ((nd j).F t) then 0 else
      fmin (net.ar j) (fun p => pc8 sel j p (fun i =>
        if h0 : (nd j).G p i ((nd j).F t) < (nd j).F t then M8 ((nd j).G p i ((nd j).F t)) (net.src j p) else 0)
          + net.off j p)
  else 0
termination_by t

def E8 (j : Fin N) (s : Nat) : Nat :=
  if net.mg j then fsum (net.ar j) (fun p => pc8 sel j p (fun i => M8 sel nd ((nd j).G p i s) (net.src j p)) + net.off j p)
  else if (nd j).r s then 0 else
    fmin (net.ar j) (fun p => pc8 sel j p (fun i => M8 sel nd ((nd j).G p i s) (net.src j p)) + net.off j p)

theorem M8_zero (j : Fin N) : M8 sel nd 0 j = 0 := by
  rw [M8, dif_neg (by have := (nd j).wF.le_late 0; omega)]

theorem M8_eq (t : Nat) (j : Fin N) (ht : 1 ≤ t) : M8 sel nd t j = E8 sel nd j ((nd j).F t) := by
  have hF : (nd j).F t < t := by have := (nd j).wF.le_late t; have := (nd j).loF1; omega
  rw [M8, dif_pos hF]
  unfold E8
  have e : ∀ p, (fun i => if h0 : (nd j).G p i ((nd j).F t) < (nd j).F t then
        M8 sel nd ((nd j).G p i ((nd j).F t)) (net.src j p) else 0)
      = (fun i => M8 sel nd ((nd j).G p i ((nd j).F t)) (net.src j p)) := by
    intro p; funext i
    by_cases hs : 1 ≤ (nd j).F t
    · rw [dif_pos (by have := ((nd j).wG p i).le_late ((nd j).F t); have := (nd j).loC1 p i; omega)]
    · have h0 : (nd j).G p i ((nd j).F t) = 0 := by have := ((nd j).wG p i).le_late ((nd j).F t); omega
      rw [dif_neg (by omega), h0, M8_zero]
  simp only [e]

end M8

/-! ## 3. Running maximum (makes the chosen count monotone by construction) -/

def rmax (f : Nat → Nat) : Nat → Nat
  | 0 => f 0
  | s + 1 => max (rmax f s) (f (s + 1))

theorem rmax_mono (f : Nat → Nat) : ∀ a s, a ≤ s → rmax f a ≤ rmax f s := by
  intro a s h
  induction s with
  | zero => have : a = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ s ih =>
    rcases Nat.lt_or_ge a (s + 1) with h' | h'
    · have := ih (by omega); simp only [rmax]; omega
    · have : a = s + 1 := by omega
      subst this; exact Nat.le_refl _

theorem rmax_le (f : Nat → Nat) (c : Nat) : ∀ s, (∀ a, a ≤ s → f a ≤ c) → rmax f s ≤ c
  | 0, h => h 0 (Nat.le_refl 0)
  | s + 1, h => by
      have := rmax_le f c s (fun a ha => h a (by omega))
      have := h (s + 1) (Nat.le_refl _)
      simp only [rmax]; omega

theorem le_rmax (f : Nat → Nat) : ∀ s, f s ≤ rmax f s
  | 0 => Nat.le_refl _
  | s + 1 => by simp only [rmax]; omega

theorem rmax_eq (f : Nat → Nat) (s : Nat) (h : ∀ a, a ≤ s → f a ≤ f s) : rmax f s = f s :=
  Nat.le_antisymm (rmax_le f (f s) s h) (le_rmax f s)

/-! ## 4. `beh8`: the `Beh7` with the guarded count `gcnt` -/

section B8
variable {N : Nat} {net : Net4 N} {b : Bands4 net} (sel : Nat → Nat → Bool) {cc : Fin N → Sig}
  (nd : ∀ j, ND7 net b cc j) (mg0 : ∀ j, net.mg j = true → cc j 0 = false)

/-- The chosen guarded count: the running maximum of `gcnt` of the copies' `M8` counts. -/
def gc8 (j : Fin N) (p : Fin (net.ar j)) (s : Nat) : Nat :=
  rmax (fun a => gcnt net sel j p (fun i => M8 sel nd ((nd j).G p i a) (net.src j p))) s

theorem gc8_mono (j : Fin N) (p : Fin (net.ar j)) (a s : Nat) (h : a ≤ s) : gc8 sel nd j p a ≤ gc8 sel nd j p s :=
  rmax_mono _ a s h

/-- **`beh8`**: the `Beh7` of the node family `nd` whose guarded count is `gc8`. -/
noncomputable def beh8 : Beh7 net b sel :=
  ofND7 sel cc nd (gc8 sel nd) (gc8_mono sel nd) mg0

/-- **The counts of `beh8` are `M8`.** -/
theorem beh8_M : ∀ t j, (beh8 sel nd mg0).M t j = M8 sel nd t j := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro j
    rcases Nat.eq_zero_or_pos t with h0 | h1
    · subst h0; rw [Beh7.M_zero, M8_zero]
    · rw [Beh7.M_eq _ t j h1, M8_eq sel nd t j h1]
      have hF : (nd j).F t < t := by have := (nd j).wF.le_late t; have := (nd j).loF1; omega
      show Beh7.E _ j ((nd j).F t) = _
      generalize (nd j).F t = s at hF ⊢
      have hG : ∀ p i a, a ≤ s → ((nd j).G p i a) < t := by
        intro p i a ha
        have := ((nd j).wG p i).le_late a; omega
      have hcm : ∀ p, (beh8 sel nd mg0).cm j p s = (fun i => M8 sel nd ((nd j).G p i s) (net.src j p)) := by
        intro p; funext i; exact ih _ (hG p i s (Nat.le_refl s)) _
      have hpc : ∀ p, (beh8 sel nd mg0).pc j p s ((beh8 sel nd mg0).cm j p s) =
          pc8 sel j p (fun i => M8 sel nd ((nd j).G p i s) (net.src j p)) := by
        intro p
        rw [hcm p]
        unfold Beh7.pc pc8
        cases net.pk j p with
        | multi => rfl
        | filt => rfl
        | plain => rfl
        | guard =>
          show gc8 sel nd j p s = _
          unfold gc8
          apply rmax_eq
          intro a ha
          apply gcnt_mono
          intro i
          rw [← ih _ (hG p i a ha), ← ih _ (hG p i s (Nat.le_refl s))]
          exact Beh7.M_mono _ _ _ _ (((nd j).wG p i).mono _ _ ha)
      unfold Beh7.E Beh7.P E8
      simp only [hpc]
      rfl

/-- **The guarded count of `beh8` is `gcnt` of its own copy counts.** -/
theorem beh8_gc (j : Fin N) (p : Fin (net.ar j)) (s : Nat) :
    (beh8 sel nd mg0).gc j p s = gcnt net sel j p ((beh8 sel nd mg0).cm j p s) := by
  show gc8 sel nd j p s = _
  have hcm : ∀ a, (beh8 sel nd mg0).cm j p a = (fun i => M8 sel nd ((nd j).G p i a) (net.src j p)) := by
    intro a; funext i; exact beh8_M sel nd mg0 _ _
  unfold gc8
  rw [hcm s]
  apply rmax_eq
  intro a ha
  rw [← hcm a, ← hcm s]
  apply gcnt_mono
  intro i
  exact Beh7.M_mono _ _ _ _ (((nd j).wG p i).mono _ _ ha)

end B8

/-! ## 5. The guarded pin reads its count -/

section G
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool} (x : Beh7 net b sel)

/-- Structural side conditions of a certified guarded pin (decidable): a guarded pin
of a reset-0 source, no inversion, offset 0. -/
def GStruct (net : Net4 N) (j : Fin N) (p : Fin (net.ar j)) : Prop :=
  net.pk j p = PK.guard ∧ net.v (net.src j p) = false ∧ net.inv j p = false ∧ net.off j p = 0

instance (j : Fin N) (p : Fin (net.ar j)) : Decidable (GStruct net j p) := by unfold GStruct; exact inferInstance

/-- **The count-level guard facts** of guarded pin `p` of stage `j` (W-E4g): at every
sample outside reset (1) BOUND: the guarded count is at most one ahead of the
feedback; (2) the copies' counts are contiguous; (3) LABEL: once the guard has
advanced, an odd line count is a transaction of the guard's branch. -/
def GuardCnt (j : Fin N) (p : Fin (net.ar j)) : Prop :=
  ∀ s, net.mg j = false → x.r j s = false →
    x.P j p s ≤ x.M (x.Q j s) j + 1 ∧ ContigF (net.nc j p) (x.cm j p s) ∧
    (x.P j (net.gp j p) s = x.M (x.Q j s) j + 1 →
      lineCnt (net.op j p) (net.nc j p) (x.cm j p s) % 2 = 1 →
      sel (net.grp j p) (lineCnt (net.op j p) (net.nc j p) (x.cm j p s) / 2) = net.br j p)

/-- GuardOK (`Beh7.GuardOK`) for ONE guarded pin: the obligation of a guarded pin the
checker did not certify. -/
def GuardPin (j : Fin N) (p : Fin (net.ar j)) : Prop :=
  ∀ s, net.mg j = false → x.r j s = false →
    x.P j p s ≤ x.M (x.Q j s) j + 1 ∧
    (x.P j (net.gp j p) s = x.M (x.Q j s) j + 1 → (x.pin j p s ^^ net.neg j p) = ph (net.v j) (x.P j p s))

/-- **`guard_val`**: a certified guarded pin reads its count once its guard has advanced,
from the values of its source at the copies' sample times. -/
theorem guard_val (j : Fin N) (p : Fin (net.ar j)) (s : Nat) (hst : GStruct net j p)
    (hgc : x.gc j p s = gcnt net sel j p (x.cm j p s)) (hc : ContigF (net.nc j p) (x.cm j p s))
    (hlab : lineCnt (net.op j p) (net.nc j p) (x.cm j p s) % 2 = 1 →
      sel (net.grp j p) (lineCnt (net.op j p) (net.nc j p) (x.cm j p s) / 2) = net.br j p)
    (ih : ∀ i, x.c (net.src j p) (x.G j p i s) = ph (net.v (net.src j p)) (x.cm j p s i)) :
    (x.pin j p s ^^ net.neg j p) = ph (net.v j) (x.P j p s) := by
  obtain ⟨hpk, hv, hinv, hoff⟩ := hst
  have hP : x.P j p s = gcnt net sel j p (x.cm j p s) := by
    unfold Beh7.P Beh7.pc; simp only [hpk]; rw [hoff, hgc]; rfl
  rw [hP, x.hpin j p s]
  simp only [hpk, hinv, Bool.false_xor]
  have e : (fun i => x.c (net.src j p) (x.G j p i s)) = (fun i => ph false (x.cm j p s i)) := by
    funext i; rw [ih, hv]
  rw [e, lineCnt_val _ _ (net.nc_pos j p) _ hc]
  have hneg : net.neg j p = net.v j := by
    unfold Net4.off offB at hoff; rw [hv, hinv] at hoff
    cases h1 : net.neg j p <;> cases h2 : net.v j <;> simp_all
  rw [hneg]
  unfold gcnt
  generalize lineCnt (net.op j p) (net.nc j p) (x.cm j p s) = L at hlab ⊢
  have hpar := filt_par (sel (net.grp j p)) (net.br j p) L hlab
  unfold ph
  by_cases hL : L % 2 = 0
  · have : filt (sel (net.grp j p)) (net.br j p) L % 2 = 0 := by omega
    simp [hL, this]
  · have : ¬ filt (sel (net.grp j p)) (net.br j p) L % 2 = 0 := by omega
    simp [hL, this]

/-- **`safe8`**: `Beh7.safe` with GuardOK replaced, per guarded pin, by the
count-level `GuardCnt` (pins with `cg = true`, whose `gc` is `gcnt`) or by that
pin's own GuardOK (`GuardPin`, pins with `cg = false`). -/
theorem safe8 (hOK : net.OK7) (hsel : x.SelOK) (hline : x.LineOK) (hpinok : x.PinOK) (hexcl : x.ExclOK)
    (cg : (j : Fin N) → Fin (net.ar j) → Bool)
    (hgc : ∀ j p s, net.pk j p = PK.guard → x.gc j p s = gcnt net sel j p (x.cm j p s))
    (hcert : ∀ j p, net.pk j p = PK.guard → cg j p = true → GStruct net j p ∧ GuardCnt x j p)
    (hres : ∀ j p, net.pk j p = PK.guard → cg j p = false → GuardPin x j p) :
    ∀ t (j : Fin N), x.c j t = ph (net.v j) (x.M t j) := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro j
    rcases Nat.eq_zero_or_pos t with ht0 | ht1
    · subst ht0
      rw [x.M_zero, ph_zero]
      by_cases hm : net.mg j = true
      · rw [x.mg0 j hm]; exact ((hOK j ⟨0, net.ar_pos j⟩).2.2.2.1 hm).1.symm
      · rw [x.hc j 0, x.F_zero, x.r0]; simp [hm]
    · have hst : x.F j t < t := x.F_lt j t ht1
      rw [x.hc j t, x.M_eq t j ht1]
      generalize x.F j t = s at hst ⊢
      have hcopy : ∀ p i, x.c (net.src j p) (x.G j p i s) = ph (net.v (net.src j p)) (x.cm j p s i) := by
        intro p i
        unfold Beh7.cm
        rcases Nat.eq_zero_or_pos s with hs0 | hs1
        · have : x.G j p i s = 0 := by have := (x.wG j p i).le_late s; omega
          rw [this]; exact ih 0 (by omega) _
        · exact ih _ (Nat.lt_trans (x.G_lt j p i s hs1) hst) _
      have hpv : ∀ p, net.pk j p ≠ PK.guard → (x.pin j p s ^^ net.neg j p) = ph (net.v j) (x.P j p s) :=
        fun p hk => x.pin_val hOK hsel hline j p s hk (hcopy p)
      unfold Beh7.E
      by_cases hm : net.mg j = true
      · simp only [hm, ite_true]
        have hv0 := ((hOK j ⟨0, net.ar_pos j⟩).2.2.2.1 hm).1
        have e : (fun p => x.pin j p s) = (fun p => ph false (x.P j p s)) := by
          funext p
          obtain ⟨hvj, hng, hkg, _⟩ := (hOK j p).2.2.2.1 hm
          have := hpv p hkg
          rw [hng, Bool.xor_false, hvj] at this; exact this
        rw [e, fany_sum _ _ (hexcl j s hm), hv0]
      · have hm' : net.mg j = false := by simpa using hm
        simp only [hm, Bool.false_eq_true, ite_false]
        by_cases hr : x.r j s = true
        · simp [hr, ph_zero]
        · have hr' : x.r j s = false := by simpa using hr
          simp only [hr, ite_false, Bool.false_eq_true]
          have hs1 : 1 ≤ s := by
            rcases Nat.eq_zero_or_pos s with h | h
            · rw [h, x.r0] at hr'; exact absurd hr' (by decide)
            · exact h
          have hq : x.q j s = ph (net.v j) (x.M (x.Q j s) j) := by
            rw [x.hq j s]; exact ih _ (Nat.lt_trans (x.Q_lt j s hs1) hst) _
          rw [hq]
          refine cel_guards (net.v j) (net.ar j) (net.ar_pos j) (fun p => x.P j p s) _ _
            (fun p => decide (net.pk j p = PK.guard)) (net.gp j) ?_ ?_ ?_ ?_ ?_
          · intro p hp
            have := ((hOK j p).2.2.2.2 (of_decide_eq_true hp)).2
            simpa using this
          · intro p hp
            exact hpv p (by simpa using hp)
          · intro p; exact x.q_le_P j hm' s hr' p
          · intro p
            by_cases hk : net.pk j p = PK.guard
            · cases hcg : cg j p
              · exact (hres j p hk hcg s hm' hr').1
              · exact ((hcert j p hk hcg).2 s hm' hr').1
            · exact hpinok j p s hm' hk
          · intro p hp hadv
            have hk : net.pk j p = PK.guard := of_decide_eq_true hp
            cases hcg : cg j p
            · exact (hres j p hk hcg s hm' hr').2 hadv
            · obtain ⟨hstr, hG⟩ := hcert j p hk hcg
              obtain ⟨_, hcont, hlab⟩ := hG s hm' hr'
              exact guard_val x j p s hstr (hgc j p s hk) hcont (hlab hadv) (hcopy p)

/-- **GuardOK discharged.** For a behaviour whose guarded count is `gcnt`, if every
guarded pin satisfies `GStruct` and `GuardCnt` (and the other count-level facts of
`Beh7.safe` hold), the Events7 hypothesis `Beh7.GuardOK` holds. -/
theorem guardOK_of_cnt (hOK : net.OK7) (hsel : x.SelOK) (hline : x.LineOK) (hpinok : x.PinOK) (hexcl : x.ExclOK)
    (hgc : ∀ j p s, net.pk j p = PK.guard → x.gc j p s = gcnt net sel j p (x.cm j p s))
    (hcert : ∀ j p, net.pk j p = PK.guard → GStruct net j p ∧ GuardCnt x j p) : x.GuardOK := by
  have hsafe := safe8 x hOK hsel hline hpinok hexcl (fun _ _ => true) hgc (fun j p hk _ => hcert j p hk)
    (fun _ _ _ h => absurd h (by decide))
  intro j p s hm hk hr
  obtain ⟨hstr, hG⟩ := hcert j p hk
  obtain ⟨hb, hcont, hlab⟩ := hG s hm hr
  refine ⟨hb, fun hadv => guard_val x j p s hstr (hgc j p s hk) hcont (hlab hadv) (fun i => ?_)⟩
  unfold Beh7.cm; exact hsafe _ _

end G

/-- NEGATIVE CONTROL (why the LABEL fact is needed): a line count `1` (transaction 0
open) whose transaction is of the OTHER branch has branch count 0: the pin reads
high, the guarded count says low. -/
theorem guard_label_neg :
    ph false 1 = true ∧ ph false (filt (fun _ => false) true 1) = false := by
  decide

/-- NEGATIVE CONTROL (why `gcnt` uses the line count, not the copies' maximum, as
`Wip/Events7.lean`'s `guardCnt` did): an AND line with copies at 2 and 3 reads LOW,
while the maximum 3 is odd. -/
theorem guard_fmax_neg :
    fall 2 (fun i => ph false (if i.val = 0 then 2 else 3)) = false ∧
    ph false (fmax 2 (fun i => if i.val = 0 then 2 else 3)) = true ∧
    ph false (lineCnt true 2 (fun i => if i.val = 0 then 2 else 3)) = false := by
  decide

end Formal.Core.XAudit.Events8
