import Formal.Net.TimedOccX
import Formal.Net.OccNetDec

/-!
# A Boolean checker for the local check with data inputs (`TimedOccX.LCheckX`) (shard C)

**Problem, plainly.** `LCheckX` quantifies over count vectors and over the values of the gate's data inputs
(constrained only where a guard says the data is stable). As a computation: enumerate the count vectors of the
exact dependency list (OccNetDec's pruned enumeration) and, for each, every Boolean assignment of the data pins
that agrees with the guarded values; compare the move rule with `enabledB`.

**Proved:** `lcheckX_of_enum` (needs: the move rule reads only the exact list `D v` and the data-pin list `Z v`;
`D v` exact, duplicate-free, containing `v` and its causes' nodes and the guards' witness nodes; `Z v` duplicate-free,
data, containing every data pin of `v`).

**Not shown here:** any instance.
-/

namespace Formal.Net.OccNet.TimedDecX
open Formal.Net.OccNet Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX

variable {α : Type} [DecidableEq α]

/-- All Boolean lists of length `k`. -/
def allBools : Nat → List (List Bool)
  | 0 => [[]]
  | k + 1 => (allBools k).flatMap fun l => [false :: l, true :: l]

theorem mem_allBools : ∀ (l : List Bool), l ∈ allBools l.length
  | [] => by simp [allBools]
  | b :: l => by
    simp only [allBools, List.length_cons, List.mem_flatMap, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false]
    exact ⟨l, mem_allBools l, by cases b <;> simp⟩

/-- The assignment given by a list of values for the list `Z`. -/
def asg (Z : List α) (bs : List Bool) (z : α) : Bool :=
  match (Z.zip bs).find? (fun p => p.1 == z) with
  | some p => p.2
  | none => false

theorem asg_map (Z : List α) (hZ : Z.Nodup) (bb : α → Bool) : ∀ z ∈ Z, asg Z (Z.map bb) z = bb z := by
  induction Z with
  | nil => intro z hz; simp at hz
  | cons a Z ih =>
    intro z hz
    obtain ⟨ha, hZ'⟩ := List.nodup_cons.1 hZ
    simp only [asg, List.map_cons, List.zip_cons_cons, List.find?_cons]
    by_cases h : a = z
    · subst h; simp
    · have hzZ : z ∈ Z := by simp [h, Ne.symm h] at hz; exact hz
      have := ih hZ' z hzZ
      simp only [asg] at this
      have hb : (a == z) = false := by simp [h]
      rw [hb]; exact this

variable (N : TNet α) (dat : α → Bool) (envEn : α → (α → Bool) → Bool) (s0 : α → Bool) (C : Cert α)
  (cl : List (Claim α)) (gd : α → α → List (Guard α))

/-- The per-vector test: every guarded data assignment. -/
def chkX (v : α) (Z : List α) (n : α → Nat) : Bool :=
  (allBools Z.length).all fun bs =>
    !(Z.all fun z => match dv cl (gd v z) n with | some val => asg Z bs z == val | none => true) ||
    (tEn N envEn v (mix dat (st s0 n) (asg Z bs)) == enabledB C n v)

theorem guardOn_congr {n n' : α → Nat} (g : Guard α) (S : List α)
    (hS : (∀ w, g.st = some w → w.1 ∈ S) ∧ (∀ w, g.en = some w → w.1 ∈ S)) (h : ∀ x ∈ S, n x = n' x) :
    guardOn n g = guardOn n' g := by
  unfold guardOn
  cases hs : g.st with
  | none => cases he : g.en with
    | none => rfl
    | some w => simp only; rw [h w.1 (hS.2 w he)]
  | some w0 =>
    cases he : g.en with
    | none => simp only; rw [h w0.1 (hS.1 w0 hs)]
    | some w => simp only; rw [h w0.1 (hS.1 w0 hs), h w.1 (hS.2 w he)]

theorem find?_congr' {β : Type} {f f' : β → Bool} : ∀ (l : List β), (∀ g ∈ l, f g = f' g) → l.find? f = l.find? f'
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.find?_cons]
    rw [h a (by simp)]
    split
    · rfl
    · exact find?_congr' l (fun g hg => h g (by simp [hg]))

theorem dv_congr {n n' : α → Nat} (gs : List (Guard α)) (S : List α)
    (hS : ∀ g ∈ gs, (∀ w, g.st = some w → w.1 ∈ S) ∧ (∀ w, g.en = some w → w.1 ∈ S)) (h : ∀ x ∈ S, n x = n' x) :
    dv cl gs n = dv cl gs n' := by
  unfold dv
  have : gs.find? (guardOn n) = gs.find? (guardOn n') := by
    exact find?_congr' gs (fun g hg => guardOn_congr g S (hS g hg) h)
  rw [this]

/-- **A passing enumeration gives `LCheckX`.** -/
theorem lcheckX_of_enum {L : α → Nat → α → Nat} {D Z : α → List α} {F : α → List Bool → List Bool → Bool}
    (hF : ∀ v s, tEn N envEn v s = F v ((D v).map s) ((Z v).map s))
    (v : α) (hnd : (D v).Nodup) (hv : v ∈ D v) (hDE : ∀ u ∈ D v, dat u = false)
    (hcD : ∀ k, k < C.len v → ∀ p ∈ C.causes v k, p.1 ∈ D v)
    (hZ : (Z v).Nodup) (hZd : ∀ z ∈ Z v, dat z = true) (hZpin : ∀ z ∈ Z v, z ∈ N.pins v)
    (hgD : ∀ z ∈ Z v, ∀ g ∈ gd v z, (∀ w, g.st = some w → w.1 ∈ D v) ∧ (∀ w, g.en = some w → w.1 ∈ D v))
    (hE : enumAll C L (chkX N dat envEn s0 C cl gd v (Z v)) (D v) [] (fun _ => 0) = true) :
    LCheckX N dat envEn s0 C L D cl gd v := by
  intro n hlen hb bb hbb
  let r : α → Nat := fun x => if x ∈ D v then n x else 0
  have hr : ∀ x ∈ D v, r x = n x := fun x hx => by simp [r, hx]
  have hchk : chkX N dat envEn s0 C cl gd v (Z v) r = true := by
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
  unfold chkX at hchk
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
    unfold Enabled
    rw [hr v hv]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun p hp => by rw [hr p.1 (hcD _ h1 p hp)]; exact h2 p hp⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun p hp => by have := h2 p hp; rwa [hr p.1 (hcD _ h1 p hp)] at this⟩
  rw [hen, hEn, ← enabledB_iff, hm]

/-! ## Data-gate claims -/

/-- The value check of a claim: every assignment of the pins that agrees with the covered values. -/
def valB (s0 : α → Bool) (c : Claim α) (cov : α → Cov) : Bool :=
  (allBools (N.pins c.z).length).all fun bs =>
    !((N.pins c.z).all fun u => match covWin s0 cl u (cov u) with
      | some w => asg (N.pins c.z) bs u == w.val | none => true) ||
    (N.F c.z ((N.pins c.z).map (asg (N.pins c.z) bs)) == c.val)

theorem valOK_of_B (s0 : α → Bool) (c : Claim α) (cov : α → Cov) (hnd : (N.pins c.z).Nodup)
    (h : valB N cl s0 c cov = true) : ValOK N s0 cl c cov := by
  intro bb hbb
  have hm := List.all_eq_true.1 h ((N.pins c.z).map bb) (by
    have := mem_allBools ((N.pins c.z).map bb); simpa using this)
  have hc : ((N.pins c.z).all fun u => match covWin s0 cl u (cov u) with
      | some w => asg (N.pins c.z) ((N.pins c.z).map bb) u == w.val | none => true) = true := by
    apply List.all_eq_true.2
    intro u hu
    rw [asg_map _ hnd bb u hu]
    cases hw : covWin s0 cl u (cov u) with
    | none => rfl
    | some w => simp only [beq_iff_eq]; exact hbb u hu w hw
  rw [hc] at hm
  simp only [Bool.not_true, Bool.false_or, beq_iff_eq] at hm
  have : (N.pins c.z).map (asg (N.pins c.z) ((N.pins c.z).map bb)) = (N.pins c.z).map bb :=
    List.map_congr_left (fun u hu => asg_map _ hnd bb u hu)
  rw [this] at hm; exact hm

/-- `CovTime` as a Boolean, with the separation table's lookup. -/
def covTimeB (Sep : α → Nat → α → Nat → Option Nat) (c w : Claim α) (hiZ loZ : Nat) : Bool :=
  (match w.A with
    | none => true
    | some e' => match c.A with
      | none => false
      | some e => match Sep e'.1 e'.2 e.1 e.2 with
        | some d => decide ((hiZ : Int) + w.a ≤ c.a + d)
        | none => false) &&
  (match w.B with
    | none => true
    | some e' => match c.B with
      | none => false
      | some e => match Sep e.1 e.2 e'.1 e'.2 with
        | some d => decide (c.b ≤ loZ + w.b + d)
        | none => false)

theorem opt_dec {o : Option Nat} {P : Nat → Prop} [DecidablePred P]
    (h : (match o with | some d => decide (P d) | none => false) = true) : ∃ d, o = some d ∧ P d := by
  cases o with
  | none => simp at h
  | some d => exact ⟨d, rfl, by simpa using h⟩

theorem covTime_of_B (Sep : α → Nat → α → Nat → Option Nat) (c w : Claim α) (hiZ loZ : Nat)
    (h : covTimeB Sep c w hiZ loZ = true) : CovTime Sep c w hiZ loZ := by
  unfold covTimeB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  unfold CovTime
  constructor
  · revert h1
    cases w.A with
    | none => intro _; trivial
    | some e' =>
      cases c.A with
      | none => intro h1; simp at h1
      | some e => intro h1; exact ⟨e, rfl, opt_dec h1⟩
  · revert h2
    cases w.B with
    | none => intro _; trivial
    | some e' =>
      cases c.B with
      | none => intro h2; simp at h2
      | some e => intro h2; exact ⟨e, rfl, opt_dec h2⟩

/-- `GuardTime` as a Boolean. -/
def guardTimeB (Sep : α → Nat → α → Nat → Option Nat) (v z : α) (c : Claim α) (g : Guard α) : Bool :=
  (match c.A with
    | none => true
    | some e => match g.st with
      | none => false
      | some w => match Sep e.1 e.2 w.1 w.2 with
        | some d => decide ((hi' N v z : Int) + c.a ≤ lo' N v w.1 + d)
        | none => false) &&
  (match c.B with
    | none => true
    | some e => match g.en with
      | none => false
      | some w => match Sep w.1 w.2 e.1 e.2 with
        | some d => decide (hi' N v w.1 ≤ lo' N v z + c.b + d)
        | none => false)

theorem guardTime_of_B (Sep : α → Nat → α → Nat → Option Nat) (v z : α) (c : Claim α) (g : Guard α)
    (h : guardTimeB N Sep v z c g = true) : GuardTime N Sep v z c g := by
  unfold guardTimeB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  unfold GuardTime
  constructor
  · revert h1
    cases c.A with
    | none => intro _; trivial
    | some e =>
      cases g.st with
      | none => intro h1; simp at h1
      | some w => intro h1; exact ⟨w, rfl, opt_dec h1⟩
  · revert h2
    cases c.B with
    | none => intro _; trivial
    | some e =>
      cases g.en with
      | none => intro h2; simp at h2
      | some w => intro h2; exact ⟨w, rfl, opt_dec h2⟩

end Formal.Net.OccNet.TimedDecX
