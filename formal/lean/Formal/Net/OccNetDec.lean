import Formal.Net.OccNet

/-!
# A decidable local check for occurrence-net certificates (shard C, S4/S6)

**Problem, plainly.** `OccNet.LCheck` quantifies over all count vectors; to run it on a netlist it must be a
Boolean computation. Here it is one: per node `v`, enumerate the counts of the nodes of `v`'s dependency
list `D v` one node at a time (each from 0 to its number of events), keep only partial vectors that respect
the pairwise lower bounds, and at each full vector compare "`v` may move" with "`v`'s next event is enabled".
The bounds are pairwise, so pruning a partial vector never drops a full one that respects them.

**Proved:** `enumAll_sound` (the enumeration covers every vector that respects the bounds and agrees with
the start vector off the list), `lcheck_of_enum` (a passing enumeration gives `LCheck` at `v`, when `en v`
reads only the nodes of `D v`, `D v` has no duplicates and contains `v` and the causes of `v`'s events, and
(only the last counted event's bound is tested, a weaker filter, so no monotonicity is needed)), and `occnet_dec` (the summary theorem of `OccNet` from passing
Boolean checks).

**Not shown here:** any instance.
-/

namespace Formal.Net.OccNet

variable {α : Type} [DecidableEq α]

/-- Set one count. -/
def setN (n : α → Nat) (u : α) (m : Nat) : α → Nat := fun x => if x = u then m else n x

/-- The bound of `u`'s last counted event on `w`. -/
def pairOK (L : α → Nat → α → Nat) (n : α → Nat) (u w : α) : Bool := n u == 0 || decide (L u (n u - 1) w ≤ n w)

/-- A newly set node `u` against itself and every node set before. -/
def newOK (L : α → Nat → α → Nat) (n : α → Nat) (u : α) (done : List α) : Bool :=
  pairOK L n u u && done.all fun w => pairOK L n u w && pairOK L n w u

/-- Enumerate the counts of the nodes of `rest`, pruning by the bounds, and run `chk` on every full vector. -/
def enumAll (C : Cert α) (L : α → Nat → α → Nat) (chk : (α → Nat) → Bool) :
    List α → List α → (α → Nat) → Bool
  | [], _, n => chk n
  | u :: rest, done, n => (List.range (C.len u + 1)).all fun m =>
      !(newOK L (setN n u m) u done) || enumAll C L chk rest (u :: done) (setN n u m)

theorem pairOK_congr {L : α → Nat → α → Nat} {n n' : α → Nat} {u w : α} (hu : n u = n' u) (hw : n w = n' w) :
    pairOK L n u w = pairOK L n' u w := by
  unfold pairOK; rw [hu, hw]

/-- **Soundness of the enumeration.** -/
theorem enumAll_sound {C : Cert α} {L : α → Nat → α → Nat} {chk : (α → Nat) → Bool} :
    ∀ (rest done : List α) (n0 : α → Nat), enumAll C L chk rest done n0 = true → rest.Nodup →
      (∀ x ∈ rest, x ∉ done) →
      ∀ n : α → Nat, (∀ x, x ∉ rest → n x = n0 x) → (∀ u ∈ rest, n u ≤ C.len u) →
        (∀ u ∈ rest ++ done, ∀ w ∈ rest ++ done, pairOK L n u w = true) → chk n = true
  | [], done, n0, h, _, _, n, hoff, _, _ => by
    have : n = n0 := funext fun x => hoff x (by simp)
    subst this; exact h
  | u :: rest, done, n0, h, hnd, hdis, n, hoff, hlen, hpair => by
    obtain ⟨hu, hnd'⟩ := List.nodup_cons.1 hnd
    simp only [enumAll, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at h
    have hm := h (n u) (Nat.lt_succ_of_le (hlen u (by simp)))
    let n' := setN n0 u (n u)
    have hn'u : n' u = n u := by simp [n', setN]
    have hn'done : ∀ w ∈ done, n' w = n w := by
      intro w hw
      have hwu : w ≠ u := fun e => hdis u (by simp) (e ▸ hw)
      have hwr : w ∉ u :: rest := fun hm' => hdis w hm' hw
      simp only [n', setN, hwu, if_false]; exact (hoff w hwr).symm
    rcases hm with hm | hm
    · -- the pruning test fails: impossible, since `n` respects the bounds
      exfalso
      have : newOK L n' u done = true := by
        unfold newOK
        simp only [Bool.and_eq_true, List.all_eq_true]
        refine ⟨?_, fun w hw => ⟨?_, ?_⟩⟩
        · rw [pairOK_congr hn'u hn'u]; exact hpair u (by simp) u (by simp)
        · rw [pairOK_congr hn'u (hn'done w hw)]; exact hpair u (by simp) w (by simp [hw])
        · rw [pairOK_congr (hn'done w hw) hn'u]; exact hpair w (by simp [hw]) u (by simp)
      rw [this] at hm; cases hm
    · apply enumAll_sound rest (u :: done) n' hm hnd'
      · intro x hx hx'
        rcases List.mem_cons.1 hx' with e | e
        · exact hu (e ▸ hx)
        · exact hdis x (by simp [hx]) e
      · intro x hx
        by_cases e : x = u
        · subst e; exact hn'u.symm
        · have : x ∉ u :: rest := by simp [e, hx]
          simp only [n', setN, e, if_false]; exact hoff x this
      · exact fun w hw => hlen w (by simp [hw])
      · intro a ha b hb
        have hm : ∀ y, y ∈ rest ++ u :: done → y ∈ u :: rest ++ done := by
          intro y hy
          simp only [List.mem_append, List.mem_cons] at hy ⊢
          rcases hy with h | h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl h)
          · exact Or.inr h
        exact hpair a (hm a ha) b (hm b hb)

/-- Boolean form of `Enabled`. -/
def enabledB (C : Cert α) (n : α → Nat) (v : α) : Bool :=
  decide (n v < C.len v) && (C.causes v (n v)).all fun p => decide (p.2 < n p.1)

theorem enabledB_iff (C : Cert α) (n : α → Nat) (v : α) : enabledB C n v = true ↔ Enabled C n v := by
  unfold enabledB Enabled
  simp [List.all_eq_true]

/-- The per-vector test at node `v`. -/
def chkAt (en : α → (α → Bool) → Bool) (s0 : α → Bool) (C : Cert α) (v : α) (n : α → Nat) : Bool :=
  en v (st s0 n) == enabledB C n v

/-- **A passing enumeration gives the local check.** `en v` must read only the nodes of `D v`
(`en v s = F v ((D v).map s)`); `D v` lists `v` and the nodes of the causes of `v`'s events. -/
theorem lcheck_of_enum {en : α → (α → Bool) → Bool} {s0 : α → Bool} {C : Cert α} {L : α → Nat → α → Nat}
    {D : α → List α} {F : α → List Bool → Bool} (hF : ∀ v s, en v s = F v ((D v).map s))
    (v : α) (hnd : (D v).Nodup) (hv : v ∈ D v)
    (hcD : ∀ k, k < C.len v → ∀ p ∈ C.causes v k, p.1 ∈ D v)
    (hE : enumAll C L (chkAt en s0 C v) (D v) [] (fun _ => 0) = true) : LCheck en s0 C L D v := by
  intro n hlen hb
  -- restrict `n` to `D v`
  let r : α → Nat := fun x => if x ∈ D v then n x else 0
  have hr : ∀ x ∈ D v, r x = n x := fun x hx => by simp [r, hx]
  have hchk : chkAt en s0 C v r = true := by
    apply enumAll_sound (D v) [] (fun _ => 0) hE hnd (by simp)
    · intro x hx; simp [r, hx]
    · intro u hu; rw [hr u hu]; exact hlen u hu
    · intro a ha b hb'
      simp only [List.append_nil] at ha hb'
      unfold pairOK
      rw [hr a ha, hr b hb']
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
      by_cases h0 : n a = 0
      · exact Or.inl h0
      · exact Or.inr (hb a ha b hb' (n a - 1) (by omega))
  -- `en v` and `Enabled` agree on `n` and on `r`
  have hst : (D v).map (st s0 r) = (D v).map (st s0 n) := by
    apply List.map_congr_left
    intro x hx; simp [st, hr x hx]
  have hen : en v (st s0 n) = en v (st s0 r) := by rw [hF, hF, hst]
  have hEn : Enabled C n v ↔ Enabled C r v := by
    unfold Enabled
    rw [hr v hv]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun p hp => by rw [hr p.1 (hcD _ h1 p hp)]; exact h2 p hp⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun p hp => by have := h2 p hp; rwa [hr p.1 (hcD _ h1 p hp)] at this⟩
  unfold chkAt at hchk
  rw [hen, hEn, ← enabledB_iff]
  simp only [beq_iff_eq] at hchk
  rw [hchk]

/-! ## Boolean forms of the time-stamp and bound checks -/

/-- `TmOK` over the nodes `U` that have events. -/
def tmOKB (C : Cert α) (U : List α) : Bool :=
  U.all fun u => (List.range (C.len u)).all fun k =>
    (!(decide (k + 1 < C.len u)) || decide (C.tm u k < C.tm u (k + 1))) &&
    (C.causes u k).all fun p => decide (p.2 < C.len p.1) && decide (C.tm p.1 p.2 < C.tm u k)

theorem tmOK_of_B {C : Cert α} {U : List α} (hcov : ∀ u, 0 < C.len u → u ∈ U) (h : tmOKB C U = true) :
    TmOK C := by
  unfold tmOKB at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq] at h
  refine ⟨fun u k hk => ?_, fun u k hk p hp => ?_⟩
  · have := (h u (hcov u (by omega)) k (by omega)).1
    rcases this with h1 | h1
    · exact absurd hk h1
    · exact h1
  · exact (h u (hcov u (by omega)) k hk).2 p hp

/-- `LStep` over `U` and the nodes `W` on which bounds may be nonzero. -/
def lstepB (C : Cert α) (L : α → Nat → α → Nat) (U W : List α) : Bool :=
  U.all fun u => (List.range (C.len u)).all fun k => W.all fun w =>
    decide (L u k w ≤ max (if u = w then k + 1 else 0) (max (if k = 0 then 0 else L u (k - 1) w) (causeBound C L u k w)))

theorem lstep_of_B {C : Cert α} {L : α → Nat → α → Nat} {U W : List α} (hcov : ∀ u, 0 < C.len u → u ∈ U)
    (hW : ∀ u k w, w ∉ W → L u k w = 0) (h : lstepB C L U W = true) : LStep C L := by
  intro u k w hk
  by_cases hw : w ∈ W
  · unfold lstepB at h
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
    exact h u (hcov u (by omega)) k hk w hw
  · rw [hW u k w hw]; exact Nat.zero_le _

/-- **The summary theorem from Boolean checks.** If the time stamps, the bounds and every node's
enumeration pass (`en v` reading only `D v`), then: every valid run that cannot be extended fires each node
exactly `len` times and ends in the certificate's final state; every valid run can be so extended; no valid
run is longer than `Σ len`; and every property of all ideal states holds after every valid run. -/
theorem occnet_dec {en : α → (α → Bool) → Bool} {s0 : α → Bool} {C : Cert α} {L : α → Nat → α → Nat}
    {D : α → List α} {F : α → List Bool → Bool} (hF : ∀ v s, en v s = F v ((D v).map s))
    (U W : List α) (hU : U.Nodup) (hcov : ∀ u, 0 < C.len u → u ∈ U) (hW : ∀ u k w, w ∉ W → L u k w = 0)
    (hT : tmOKB C U = true) (hL : lstepB C L U W = true)
    (hD : ∀ v, (D v).Nodup ∧ v ∈ D v ∧ ∀ k, k < C.len v → ∀ p ∈ C.causes v k, p.1 ∈ D v)
    (hE : ∀ v, enumAll C L (chkAt en s0 C v) (D v) [] (fun _ => 0) = true) :
    (∀ l, Valid en s0 l → (∀ v, en v (after s0 l) = false) →
        (∀ u, l.count u = C.len u) ∧ after s0 l = st s0 C.len) ∧
    (∀ l, Valid en s0 l → ∃ l', Valid en s0 (l ++ l') ∧ ∀ v, en v (after s0 (l ++ l')) = false) ∧
    (∀ l, Valid en s0 l → l.length ≤ sumOver U C.len) ∧
    (∀ P : (α → Bool) → Prop, (∀ c, Ideal C c → P (st s0 c)) → ∀ l, Valid en s0 l → P (after s0 l)) := by
  have hT' := tmOK_of_B hcov hT
  have hL' := lstep_of_B hcov hW hL
  have hloc : ∀ v, LCheck en s0 C L D v := fun v =>
    lcheck_of_enum hF v (hD v).1 (hD v).2.1 (hD v).2.2 (hE v)
  obtain ⟨h1, h2, h3⟩ := occnet_summary hT' hL' hloc U hU hcov
  exact ⟨h1, h2, h3, fun P hP l hv => reach_prop (gcheck_of_local (lsound_of_step hT' hL') hloc) P hP l hv⟩

/-! ## A toy instance (the checks run by `decide`)

Two nodes: `0` rises once on its own, `1` rises once after `0` (`en 1 = s 0 ∧ ¬ s 1`). The certificate:
one event each, `(1, 0)` caused by `(0, 0)`. -/
namespace Toy

def D : Nat → List Nat := fun v => if v = 1 then [1, 0] else [v]
def F : Nat → List Bool → Bool := fun v l =>
  if v = 0 then !(l.getD 0 true) else if v = 1 then l.getD 1 false && !(l.getD 0 true) else false
def en (v : Nat) (s : Nat → Bool) : Bool := F v ((D v).map s)
def C : Cert Nat := ⟨fun u => if u ≤ 1 then 1 else 0, fun u _ => if u = 1 then [(0, 0)] else [], fun u _ => u⟩
def L : Nat → Nat → Nat → Nat := fun u _ w => if u = 1 ∧ w = 0 then 1 else if u = w ∧ u ≤ 1 then 1 else 0

theorem toy :
    (∀ l, Valid en (fun _ => false) l → (∀ v, en v (after (fun _ => false) l) = false) →
        (∀ u, l.count u = C.len u) ∧ after (fun _ => false) l = st (fun _ => false) C.len) ∧
    (∀ l, Valid en (fun _ => false) l → l.length ≤ sumOver [0, 1] C.len) := by
  have h := occnet_dec (en := en) (s0 := fun _ => false) (C := C) (L := L) (D := D) (F := F)
    (fun _ _ => rfl) [0, 1] [0, 1] (by decide)
    (by intro u hu; simp only [C] at hu; split at hu <;> simp_all; omega)
    (by intro u k w hw; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hw; unfold L; repeat' split
        all_goals omega)
    (by decide) (by decide)
    (by intro v; by_cases h1 : v = 1
        · subst h1; refine ⟨by decide, by decide, ?_⟩; intro k hk p hp; simp [C] at hp; simp [D, hp]
        · refine ⟨by simp [D, h1], by simp [D, h1], ?_⟩; intro k hk p hp; simp [C, h1] at hp)
    (by intro v; by_cases h0 : v = 0
        · subst h0; decide
        · by_cases h1 : v = 1
          · subst h1; decide
          · simp only [enumAll, D, h1, if_false, C]
            have : ¬ v ≤ 1 := by omega
            simp [this, List.range, List.range.loop, chkAt, en, F, h0, h1, enabledB])
  exact ⟨h.1, h.2.2.1⟩

end Toy

end Formal.Net.OccNet
