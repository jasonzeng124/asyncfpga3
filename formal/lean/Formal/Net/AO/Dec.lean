import Formal.Net.AO.Timed
import Formal.Net.TimedOccDecX

/-!
# Boolean checkers for AND-OR certificates (shard C)

The enumerator of `OccNetDec` and the data-pin test of `TimedOccDecX`, for `AO.Cert`: `enabledBA` (some alternative
fully counted), `chkXA`, `lcheckXA_of_enum` (a passing enumeration gives `AO.LCheckXA`).
-/

namespace Formal.Net.AO
open Formal.Net.OccNet (st)
open Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Net.OccNet.TimedDecX

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
def enabledBA (C : Cert α) (n : α → Nat) (v : α) : Bool :=
  decide (n v < C.len v) && (C.causes v (n v)).any fun alt => alt.all fun p => decide (p.2 < n p.1)

theorem enabledBA_iff (C : Cert α) (n : α → Nat) (v : α) : enabledBA C n v = true ↔ Enabled C n v := by
  unfold enabledBA Enabled AltIn
  simp [List.all_eq_true, List.any_eq_true]

variable (N : TNet α) (dat : α → Bool) (envEn : α → (α → Bool) → Bool) (s0 : α → Bool) (C : Cert α)
  (cl : List (Claim α)) (gd : α → α → List (Guard α))

/-- The per-vector test: every guarded data assignment. -/
def ownB (v : α) (n : α → Nat) : Bool :=
  (List.range (n v)).all fun k => (C.causes v k).any fun alt => alt.all fun p => decide (p.2 < n p.1)

def chkXA (v : α) (Z : List α) (n : α → Nat) : Bool :=
  !(ownB C v n) || (allBools Z.length).all fun bs =>
    !(Z.all fun z => match dv cl (gd v z) n with | some val => asg Z bs z == val | none => true) ||
    (tEn N envEn v (mix dat (st s0 n) (asg Z bs)) == enabledBA C n v)

/-- **A passing enumeration gives `LCheckX`.** -/
theorem lcheckXA_of_enum {L : α → Nat → α → Nat} {D Z : α → List α} {F : α → List Bool → List Bool → Bool}
    (hF : ∀ v s, tEn N envEn v s = F v ((D v).map s) ((Z v).map s))
    (v : α) (hnd : (D v).Nodup) (hv : v ∈ D v) (hDE : ∀ u ∈ D v, dat u = false)
    (hcD : ∀ k, k < C.len v → ∀ alt ∈ C.causes v k, ∀ p ∈ alt, p.1 ∈ D v)
    (hZ : (Z v).Nodup) (hZd : ∀ z ∈ Z v, dat z = true) (hZpin : ∀ z ∈ Z v, z ∈ N.pins v)
    (hgD : ∀ z ∈ Z v, ∀ g ∈ gd v z, (∀ w, g.st = some w → w.1 ∈ D v) ∧ (∀ w, g.en = some w → w.1 ∈ D v))
    (hE : enumAll C L (chkXA N dat envEn s0 C cl gd v (Z v)) (D v) [] (fun _ => 0) = true) :
    LCheckXA N dat envEn s0 C L D cl gd v := by
  intro n hlen hb hown bb hbb
  let r : α → Nat := fun x => if x ∈ D v then n x else 0
  have hr : ∀ x ∈ D v, r x = n x := fun x hx => by simp [r, hx]
  have hchk : chkXA N dat envEn s0 C cl gd v (Z v) r = true := by
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
  unfold chkXA at hchk
  have hownr : ownB C v r = true := by
    unfold ownB
    apply List.all_eq_true.2
    intro k hk
    rw [List.mem_range, hr v hv] at hk
    obtain ⟨alt, halt, hin⟩ := hown k hk
    apply List.any_eq_true.2
    refine ⟨alt, halt, List.all_eq_true.2 fun p hp => ?_⟩
    have hpD := hcD k (Nat.lt_of_lt_of_le hk (hlen v hv)) alt halt p hp
    simp only [decide_eq_true_eq]; rw [hr p.1 hpD]; exact hin p hp
  rw [hownr] at hchk
  simp only [Bool.not_true, Bool.false_or] at hchk
  have hm := List.all_eq_true.1 hchk ((Z v).map bb) (by
    have := mem_allBools ((Z v).map bb); simpa using this)
  have hdv : ∀ z ∈ Z v, dv cl (gd v z) r = dv cl (gd v z) n :=
    fun z hz => dv_congr cl (gd v z) (D v) (hgD z hz) hr
  have hcons : (Z v).all (fun z => match dv cl (gd v z) r with
      | some val => asg (Z v) ((Z v).map bb) z == val | none => true) = true := by
    apply List.all_eq_true.2
    intro z hz
    rw [hdv z hz, asg_map (Z v) hZ bb z hz]
    cases hd : dv cl (gd v z) n with
    | none => rfl
    | some val =>
      simp only [beq_iff_eq]
      exact hbb z (hZd z hz) (hZpin z hz) val hd
  rw [hcons] at hm
  simp only [Bool.not_true, Bool.false_or, beq_iff_eq] at hm
  have hDm : (D v).map (mix dat (st s0 r) (asg (Z v) ((Z v).map bb))) = (D v).map (mix dat (st s0 n) bb) := by
    apply List.map_congr_left
    intro u hu
    simp only [mix, hDE u hu, Bool.false_eq_true, if_false, st, hr u hu]
  have hZm : (Z v).map (mix dat (st s0 r) (asg (Z v) ((Z v).map bb))) = (Z v).map (mix dat (st s0 n) bb) := by
    apply List.map_congr_left
    intro z hz
    simp only [mix, hZd z hz, if_true]
    exact asg_map (Z v) hZ bb z hz
  have hen : tEn N envEn v (mix dat (st s0 n) bb) = tEn N envEn v (mix dat (st s0 r) (asg (Z v) ((Z v).map bb))) := by
    rw [hF, hF, hDm, hZm]
  have hEn : Enabled C n v ↔ Enabled C r v := by
    unfold Enabled AltIn
    rw [hr v hv]
    constructor
    · rintro ⟨h1, alt, ha, h2⟩
      exact ⟨h1, alt, ha, fun p hp => by rw [hr p.1 (hcD _ h1 alt ha p hp)]; exact h2 p hp⟩
    · rintro ⟨h1, alt, ha, h2⟩
      exact ⟨h1, alt, ha, fun p hp => by have := h2 p hp; rwa [hr p.1 (hcD _ h1 alt ha p hp)] at this⟩
  rw [hen, hEn, ← enabledBA_iff, hm]


end Formal.Net.AO
