/-!
# Formal.Core.Kleene — three-valued (Kleene) signal values

Shared Core definitions (track 4, shard A). Imported by `Formal.Core.Lut` and by
shards B (cells) and C (composition).

* `K3` = {0, 1, X}. `X` means "not a valid logic level": unknown, in transit,
  metastable, or an intermediate voltage. It is *not* "don't care".
* The **information order** `a ⊑ b` ("b is at least as defined as a"):
  `X ⊑ 0`, `X ⊑ 1`, and `a ⊑ a`. Nothing else.
* `K3.ofBool` embeds `Bool`; `K3.merge` is the greatest lower bound in `⊑`
  (it is exactly what a 2:1 pass-transistor mux outputs when its select is X
  and both data inputs are as given — see `Formal.Core.Lut`).
* Strong-Kleene `not`/`and`/`or` with agreement-on-Bool and monotonicity.
* Small tuple helpers on `Fin k → α` (`vcons`, `vtail`, `setAt`) because Lean
  core has no `Fin.cons`, and we do not import Mathlib here (Core must stay
  cheap to check).

No Mathlib import. Notation `⊑` is scoped to `Formal.Core.K3`: `open Formal.Core K3`.
-/

namespace Formal.Core

/-- Kleene three-valued logic level. -/
inductive K3 where
  | zero
  | one
  | X
  deriving DecidableEq, Repr, Inhabited

namespace K3

/-- Embedding of Boolean levels. -/
def ofBool : Bool → K3
  | false => zero
  | true => one

@[simp] theorem ofBool_false : ofBool false = zero := rfl
@[simp] theorem ofBool_true : ofBool true = one := rfl

theorem ofBool_inj {a b : Bool} : ofBool a = ofBool b ↔ a = b := by
  cases a <;> cases b <;> decide

@[simp] theorem ofBool_ne_X (b : Bool) : ofBool b ≠ X := by cases b <;> decide

/-- Information order: `a ⊑ b` iff `a = X` or `a = b`. -/
def Le (a b : K3) : Prop := a = X ∨ a = b

instance (a b : K3) : Decidable (Le a b) := inferInstanceAs (Decidable (_ ∨ _))

@[inherit_doc] scoped infix:50 " ⊑ " => K3.Le

theorem le_refl (a : K3) : a ⊑ a := Or.inr rfl

theorem X_le (a : K3) : X ⊑ a := Or.inl rfl

theorem le_trans {a b c : K3} : a ⊑ b → b ⊑ c → a ⊑ c := by
  cases a <;> cases b <;> cases c <;> decide

theorem le_antisymm {a b : K3} : a ⊑ b → b ⊑ a → a = b := by
  cases a <;> cases b <;> decide

/-- A defined value is maximal: it can only be refined to itself. -/
theorem ofBool_le_iff {b : Bool} {a : K3} : ofBool b ⊑ a ↔ a = ofBool b := by
  cases b <;> cases a <;> decide

theorem le_ofBool_iff {a : K3} {b : Bool} : a ⊑ ofBool b ↔ a = X ∨ a = ofBool b :=
  Iff.rfl

/-- Every value other than `X` is a Boolean. -/
theorem ne_X_iff {a : K3} : a ≠ X ↔ ∃ b, a = ofBool b := by
  cases a
  · exact ⟨fun _ => ⟨false, rfl⟩, fun _ => by decide⟩
  · exact ⟨fun _ => ⟨true, rfl⟩, fun _ => by decide⟩
  · exact ⟨fun h => absurd rfl h, fun ⟨b, h⟩ => by cases b <;> cases h⟩

/-- Every `K3` value has a Boolean refinement (pick 0 for `X`). -/
def pick : K3 → Bool
  | one => true
  | _ => false

theorem le_ofBool_pick (a : K3) : a ⊑ ofBool (pick a) := by cases a <;> decide

/-- Greatest lower bound in the information order. -/
def merge (a b : K3) : K3 := if a = b then a else X

@[simp] theorem merge_self (a : K3) : merge a a = a := by simp [merge]

theorem merge_comm (a b : K3) : merge a b = merge b a := by
  cases a <;> cases b <;> decide

theorem merge_le_left (a b : K3) : merge a b ⊑ a := by
  cases a <;> cases b <;> decide

theorem merge_le_right (a b : K3) : merge a b ⊑ b := by
  cases a <;> cases b <;> decide

theorem le_merge {a b c : K3} : c ⊑ a → c ⊑ b → c ⊑ merge a b := by
  cases a <;> cases b <;> cases c <;> decide

theorem merge_mono {a b a' b' : K3} : a ⊑ a' → b ⊑ b' → merge a b ⊑ merge a' b' := by
  cases a <;> cases b <;> cases a' <;> cases b' <;> decide

theorem merge_eq_ofBool_iff {a b : K3} {c : Bool} :
    merge a b = ofBool c ↔ a = ofBool c ∧ b = ofBool c := by
  cases a <;> cases b <;> cases c <;> decide

/-! ### Strong-Kleene gates (for convenience of downstream shards) -/

def not : K3 → K3
  | zero => one
  | one => zero
  | X => X

def and : K3 → K3 → K3
  | zero, _ => zero
  | _, zero => zero
  | one, one => one
  | _, _ => X

def or : K3 → K3 → K3
  | one, _ => one
  | _, one => one
  | zero, zero => zero
  | _, _ => X

theorem not_ofBool (a : Bool) : not (ofBool a) = ofBool (!a) := by cases a <;> rfl
theorem and_ofBool (a b : Bool) : and (ofBool a) (ofBool b) = ofBool (a && b) := by
  cases a <;> cases b <;> rfl
theorem or_ofBool (a b : Bool) : or (ofBool a) (ofBool b) = ofBool (a || b) := by
  cases a <;> cases b <;> rfl
theorem not_mono {a a' : K3} : a ⊑ a' → not a ⊑ not a' := by
  cases a <;> cases a' <;> decide
theorem and_mono {a b a' b' : K3} : a ⊑ a' → b ⊑ b' → and a b ⊑ and a' b' := by
  cases a <;> cases b <;> cases a' <;> cases b' <;> decide
theorem or_mono {a b a' b' : K3} : a ⊑ a' → b ⊑ b' → or a b ⊑ or a' b' := by
  cases a <;> cases b <;> cases a' <;> cases b' <;> decide

end K3

/-! ### Tuples `Fin k → α` -/

/-- Prepend `c` as element 0 (input `I0`). -/
def vcons {α : Type} {k : Nat} (c : α) (x : Fin k → α) : Fin (k + 1) → α :=
  fun i => Fin.cases c x i

/-- Drop element 0. -/
def vtail {α : Type} {k : Nat} (x : Fin (k + 1) → α) : Fin k → α :=
  fun i => x i.succ

@[simp] theorem vcons_zero {α : Type} {k : Nat} (c : α) (x : Fin k → α) :
    vcons c x 0 = c := rfl

@[simp] theorem vtail_vcons {α : Type} {k : Nat} (c : α) (x : Fin k → α) :
    vtail (vcons c x) = x := rfl

theorem vcons_vtail {α : Type} {k : Nat} (x : Fin (k + 1) → α) :
    vcons (x 0) (vtail x) = x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- `∀ x : Fin (k+1) → α` splits into the head and the tail. -/
theorem forall_vcons {α : Type} {k : Nat} {P : (Fin (k + 1) → α) → Prop} :
    (∀ x, P x) ↔ ∀ c y, P (vcons c y) :=
  ⟨fun h _ _ => h _, fun h x => vcons_vtail x ▸ h (x 0) (vtail x)⟩

/-- Replace element `j` by `c`. -/
def setAt {α : Type} {k : Nat} (x : Fin k → α) (j : Fin k) (c : α) : Fin k → α :=
  fun i => if i = j then c else x i

/-- Build a tuple from a list (missing entries are `d`). `kvec [a, b, c]`. -/
def ofList {α : Type} (d : α) (l : List α) (k : Nat) : Fin k → α :=
  fun i => l.getD i.val d

/-! ### Vectors of `K3` -/

namespace K3

/-- Pointwise embedding of a Boolean input vector. -/
def ofBoolVec {k : Nat} (x : Fin k → Bool) : Fin k → K3 := fun i => ofBool (x i)

/-- Pointwise information order. -/
def VLe {k : Nat} (u v : Fin k → K3) : Prop := ∀ i, u i ⊑ v i

/-- `x` is a Boolean resolution of `v`: it agrees with every defined entry. -/
def Consistent {k : Nat} (v : Fin k → K3) (x : Fin k → Bool) : Prop :=
  ∀ i, v i ⊑ ofBool (x i)

instance {k : Nat} (v : Fin k → K3) (x : Fin k → Bool) : Decidable (Consistent v x) :=
  inferInstanceAs (Decidable (∀ _ : Fin k, _))

/-- Every `K3` vector has at least one Boolean resolution. -/
theorem consistent_pick {k : Nat} (v : Fin k → K3) : Consistent v (fun i => pick (v i)) :=
  fun i => le_ofBool_pick (v i)

theorem consistent_vcons {k : Nat} {c : K3} {v : Fin k → K3} {b : Bool} {x : Fin k → Bool} :
    Consistent (vcons c v) (vcons b x) ↔ c ⊑ ofBool b ∧ Consistent v x := by
  constructor
  · intro h; exact ⟨h 0, fun i => h i.succ⟩
  · intro ⟨h0, h⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact h0
    · exact h j

theorem consistent_ofBoolVec {k : Nat} {x y : Fin k → Bool} :
    Consistent (ofBoolVec x) y ↔ y = x := by
  constructor
  · intro h; funext i
    have := h i
    simp only [ofBoolVec, ofBool_le_iff] at this
    exact ofBool_inj.mp this
  · intro h; subst h; intro i; exact le_refl _

/-- `K3` tuple literal: `K3.vec [one, zero, X]`; missing entries are `X`. -/
abbrev vec (l : List K3) (k : Nat) : Fin k → K3 := ofList X l k

/-- Strong enumeration of all `K3` tuples, used for `Decidable (∀ v, P v)`. -/
def forallVec : (k : Nat) → ((Fin k → K3) → Bool) → Bool
  | 0, p => p (fun i => i.elim0)
  | k + 1, p =>
      forallVec k (fun y => p (vcons zero y)) &&
      forallVec k (fun y => p (vcons one y)) &&
      forallVec k (fun y => p (vcons X y))

theorem forallVec_iff : ∀ {k : Nat} {p : (Fin k → K3) → Bool},
    forallVec k p = true ↔ ∀ v, p v = true
  | 0, p => by
      constructor
      · intro h v
        have : v = (fun i => i.elim0) := funext (fun i => i.elim0)
        subst this; exact h
      · intro h; exact h _
  | k + 1, p => by
      simp only [forallVec, Bool.and_eq_true, forallVec_iff]
      rw [forall_vcons (P := fun v => p v = true)]
      constructor
      · intro ⟨⟨h0, h1⟩, h2⟩ c y
        cases c
        · exact h0 y
        · exact h1 y
        · exact h2 y
      · intro h; exact ⟨⟨h zero, h one⟩, h X⟩

instance decForallVec {k : Nat} (P : (Fin k → K3) → Prop) [DecidablePred P] :
    Decidable (∀ v, P v) :=
  decidable_of_iff (forallVec k (fun v => decide (P v)) = true)
    (by simp only [forallVec_iff, decide_eq_true_eq])

end K3

/-- Enumeration of all Boolean tuples, used for `Decidable (∀ x, P x)`. -/
def forallBoolVec : (k : Nat) → ((Fin k → Bool) → Bool) → Bool
  | 0, p => p (fun i => i.elim0)
  | k + 1, p =>
      forallBoolVec k (fun y => p (vcons false y)) &&
      forallBoolVec k (fun y => p (vcons true y))

theorem forallBoolVec_iff : ∀ {k : Nat} {p : (Fin k → Bool) → Bool},
    forallBoolVec k p = true ↔ ∀ x, p x = true
  | 0, p => by
      constructor
      · intro h v
        have : v = (fun i => i.elim0) := funext (fun i => i.elim0)
        subst this; exact h
      · intro h; exact h _
  | k + 1, p => by
      simp only [forallBoolVec, Bool.and_eq_true, forallBoolVec_iff]
      rw [forall_vcons (P := fun v => p v = true)]
      constructor
      · intro ⟨h0, h1⟩ c y
        cases c
        · exact h0 y
        · exact h1 y
      · intro h; exact ⟨h false, h true⟩

instance decForallBoolVec {k : Nat} (P : (Fin k → Bool) → Prop) [DecidablePred P] :
    Decidable (∀ x, P x) :=
  decidable_of_iff (forallBoolVec k (fun x => decide (P x)) = true)
    (by simp only [forallBoolVec_iff, decide_eq_true_eq])

end Formal.Core
