/-!
# Formal.Core.Ternary — soundness of ternary (Kleene) simulation w.r.t. binary delay semantics

Bridge between track 4 (Kleene LUT semantics) and track 3 (delay channels).

Classic result (Eichelberger 1965; Brzozowski & Seger, *Asynchronous Circuits*,
1995, ch. 7; Mendler–Shiple–Berry FMSD 2012): when the inputs of a network of
gates change from `a` to `b`,

* **algorithm A** (inputs that change are set to `X`, iterate to a fixed point
  starting from the old stable state) yields `tA`; any node binary in `tA`
  **never changes** (no glitch) under any delay assignment;
* **algorithm B** (inputs set to `b`, iterate from `tA`) yields `tB`; any node
  binary in `tB` **settles** to that value.

## Model

* `K3`, `⊑`, `meet`, `kext` (Kleene extension of a Boolean function, as a
  mux tree) are defined locally (minimal copy; `Formal.Core.Kleene` /
  `Formal.Core.Lut` are the shared versions — same constructor names and the
  same order, so unification is a rename).
* `Net ι ν`: inputs `ι`, nodes `ν` (each node = one gate output = one wire,
  ideal wires). A net is a Boolean next-state function `fb` together with a
  ternary function `F` that is **monotone** and **extends** `fb`. Nothing else
  about `F` is used, so any sound Kleene gate model (the LUT mux tree, strong
  Kleene and/or, ...) plugs in. `LutNet` builds one from LUT tables via `kext`.
* Binary delay semantics, `Causal`: a discrete-time signal `σ : ℕ → ν → Bool`
  in which every node, at every step, either holds or takes the value of its
  Boolean gate function applied to **samples of its inputs taken at arbitrary
  earlier times, a different time per input**. This contains the GMW
  ("general multiple winner", unbounded gate delay, ideal wire) step relation
  (`GStep`, `gmw_causal`), and also transport / pure delays on gates and on
  every wire separately, inertial delays, and any mixture: it is the weakest
  causal assumption. All soundness results are proved for `Causal`.
* Settling needs a bound: `Stale D` says that every node value at time `t ≥ D`
  is the gate function of samples taken in the window `[t-D, t)`. Bounded
  transport delay (all gate+wire delays ≤ D) satisfies it; for inertial gates
  it is a hypothesis (see notes).

## Main results

* `kext_mono`, `kext_bool` : Kleene extension is monotone and extends `f`. (1)
* `iterA_antitone`, `iterA_fix`, `resultA_postfix`, `le_iterA` : algorithm A
  reaches a fixed point within `|ν|+1` steps by monotone iteration, and it is
  the greatest post-fixed point below the start state. (2)
* `sound_postfix`, `soundA` : **every binary state reachable during the
  transition is covered by `tA`** (inputs may move between `a` and `b` in any
  order, even back and forth). `noGlitchA` : binary in `tA` ⇒ never changes. (3)
* `iterB_mono`, `iterB_fix`, `settleB`, `settleB_value` : the B-iterates `tB_k`
  cover every state from time `T0 + k·D` on, so a node binary in `tB_k` has
  settled by `T0 + k·D` and stays there. (4)
* `bdc2_*` : the C-element `bd_c2` (one LUT4 with its own output fed back):
  every single-input transition from every stable state is static-hazard-free
  and settles deterministically — by `decide`.
-/

namespace Formal.Core.Ternary

/-! ## Three-valued levels -/

/-- Kleene three-valued logic level (local minimal copy). -/
inductive K3 where
  | zero
  | one
  | X
  deriving DecidableEq, Repr, Inhabited

namespace K3

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
theorem ofBool_le_iff {b : Bool} {a : K3} : ofBool b ⊑ a ↔ a = ofBool b := by
  cases b <;> cases a <;> decide
theorem le_X_iff {a : K3} : a ⊑ X ↔ a = X := by cases a <;> decide

/-- Greatest lower bound in `⊑`. -/
def meet (a b : K3) : K3 := if a = b then a else X

theorem meet_le_left (a b : K3) : meet a b ⊑ a := by
  cases a <;> cases b <;> decide
theorem meet_le_right (a b : K3) : meet a b ⊑ b := by
  cases a <;> cases b <;> decide
theorem le_meet {a b c : K3} : c ⊑ a → c ⊑ b → c ⊑ meet a b := by
  cases a <;> cases b <;> cases c <;> decide
theorem meet_mono {a b a' b' : K3} (ha : a ⊑ a') (hb : b ⊑ b') : meet a b ⊑ meet a' b' :=
  le_meet (le_trans (meet_le_left _ _) ha) (le_trans (meet_le_right _ _) hb)
theorem meet_self (a : K3) : meet a a = a := by cases a <;> decide

/-- One 2:1 mux of the tree: select `c`, data `d0` (select 0), `d1` (select 1). -/
def sel : K3 → K3 → K3 → K3
  | zero, d0, _ => d0
  | one, _, d1 => d1
  | X, d0, d1 => meet d0 d1

theorem sel_mono {c c' d0 d0' d1 d1' : K3} (hc : c ⊑ c') (h0 : d0 ⊑ d0') (h1 : d1 ⊑ d1') :
    sel c d0 d1 ⊑ sel c' d0' d1' := by
  cases c <;> cases c'
  all_goals first
    | exact absurd hc (by decide)
    | exact h0
    | exact h1
    | exact meet_mono h0 h1
    | exact le_trans (meet_le_left _ _) h0
    | exact le_trans (meet_le_right _ _) h1

end K3

open K3

/-! ## Vectors -/

/-- Pointwise information order on vectors (any index type). -/
def VLe {α : Type} (u v : α → K3) : Prop := ∀ i, u i ⊑ v i

/-- Embedding of Boolean vectors. -/
def vb {α : Type} (s : α → Bool) : α → K3 := fun i => ofBool (s i)

/-- Pointwise meet: the ternary "hull" of two vectors. -/
def vmeet {α : Type} (u v : α → K3) : α → K3 := fun i => meet (u i) (v i)

theorem vle_refl {α : Type} (u : α → K3) : VLe u u := fun _ => le_refl _
theorem vle_trans {α : Type} {u v w : α → K3} (h : VLe u v) (h' : VLe v w) : VLe u w :=
  fun i => le_trans (h i) (h' i)

/-- The hull of `a` and `b` covers every vector each of whose entries comes from `a` or `b`. -/
theorem hull_le {α : Type} {a b c : α → Bool} (h : ∀ x, c x = a x ∨ c x = b x) :
    VLe (vmeet (vb a) (vb b)) (vb c) := by
  intro x
  rcases h x with h | h <;> rw [show vb c x = ofBool (c x) from rfl, h]
  · exact meet_le_left _ _
  · exact meet_le_right _ _

def vcons {α : Type} {k : Nat} (c : α) (x : Fin k → α) : Fin (k + 1) → α :=
  fun i => Fin.cases c x i

def vtail {α : Type} {k : Nat} (x : Fin (k + 1) → α) : Fin k → α := fun i => x i.succ

theorem vcons_vtail {α : Type} {k : Nat} (x : Fin (k + 1) → α) : vcons (x 0) (vtail x) = x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-! ## (1) Kleene extension of a Boolean function -/

/-- Kleene extension of `f : 𝔹^k → 𝔹`, computed as the LUT mux tree (input 0
selects the first rank). Equivalent to "the common value of `f` over all Boolean
refinements, else `X`" (`Formal.Core.Lut.keval_eq_kevalSpec`). -/
def kext : (k : Nat) → ((Fin k → Bool) → Bool) → (Fin k → K3) → K3
  | 0, f, _ => ofBool (f (fun i => i.elim0))
  | k + 1, f, v =>
      sel (v 0) (kext k (fun x => f (vcons false x)) (vtail v))
                (kext k (fun x => f (vcons true x)) (vtail v))

/-- **(1a)** The Kleene extension extends `f`. -/
theorem kext_bool : ∀ {k : Nat} (f : (Fin k → Bool) → Bool) (x : Fin k → Bool),
    kext k f (vb x) = ofBool (f x)
  | 0, f, x => by
      simp only [kext]
      congr 2
      funext i; exact i.elim0
  | k + 1, f, x => by
      have IH0 := kext_bool (fun y => f (vcons false y)) (vtail x)
      have IH1 := kext_bool (fun y => f (vcons true y)) (vtail x)
      have hx := vcons_vtail x
      simp only [kext]
      have e : vtail (vb x) = vb (vtail x) := rfl
      rw [e, IH0, IH1]
      show sel (ofBool (x 0)) _ _ = _
      revert hx
      cases x 0 <;> intro hx <;> rw [← hx] <;> rfl

/-- **(1b)** The Kleene extension is monotone in the information order. -/
theorem kext_mono : ∀ {k : Nat} (f : (Fin k → Bool) → Bool) {u v : Fin k → K3},
    VLe u v → kext k f u ⊑ kext k f v
  | 0, _, _, _, _ => le_refl _
  | k + 1, f, u, v, h => by
      simp only [kext]
      exact sel_mono (h 0) (kext_mono _ (fun i => h i.succ)) (kext_mono _ (fun i => h i.succ))

/-! ## Networks -/

/-- A network with inputs `ι` and nodes `ν`. `fb a s i` is the Boolean
excitation of node `i` (its gate function evaluated on the current inputs and
node values); `F` is the ternary model of the same gates. -/
structure Net (ι ν : Type) where
  fb : (ι → Bool) → (ν → Bool) → ν → Bool
  F : (ι → K3) → (ν → K3) → ν → K3
  /-- Hypothesis: the ternary gate model is monotone (true for `kext`, `kext_mono`). -/
  mono : ∀ u u' t t', VLe u u' → VLe t t' → VLe (F u t) (F u' t')
  /-- Hypothesis: the ternary gate model agrees with the Boolean one on binary values. -/
  ext : ∀ a s i, F (vb a) (vb s) i = ofBool (fb a s i)

namespace Net

variable {ι ν : Type} (N : Net ι ν)

/-- The key covering step: a ternary over-approximation of the inputs and
state over-approximates the Boolean excitation. -/
theorem cover {u : ι → K3} {t : ν → K3} {a : ι → Bool} {s : ν → Bool}
    (hu : VLe u (vb a)) (ht : VLe t (vb s)) (i : ν) : N.F u t i ⊑ ofBool (N.fb a s i) := by
  rw [← N.ext]; exact N.mono _ _ _ _ hu ht i

end Net

/-- A network of LUTs: node `i` is a LUT with `arity i` pins, pin `p` wired to
an input (`inl`) or a node (`inr`), with truth table `tbl i`. -/
structure LutNet (ι ν : Type) where
  arity : ν → Nat
  pin : (i : ν) → Fin (arity i) → ι ⊕ ν
  tbl : (i : ν) → (Fin (arity i) → Bool) → Bool

/-- A LUT network with its Kleene (mux-tree) ternary model. -/
def LutNet.toNet {ι ν : Type} (L : LutNet ι ν) : Net ι ν where
  fb a s i := L.tbl i (fun p => Sum.elim a s (L.pin i p))
  F u t i := kext (L.arity i) (L.tbl i) (fun p => Sum.elim u t (L.pin i p))
  mono u u' t t' hu ht i := by
    apply kext_mono
    intro p
    show Sum.elim u t (L.pin i p) ⊑ Sum.elim u' t' (L.pin i p)
    cases L.pin i p with
    | inl x => exact hu x
    | inr y => exact ht y
  ext a s i := by
    have e : (fun p => Sum.elim (vb a) (vb s) (L.pin i p)) =
        vb (fun p => Sum.elim a s (L.pin i p)) := by
      funext p
      show Sum.elim (vb a) (vb s) (L.pin i p) = ofBool (Sum.elim a s (L.pin i p))
      cases L.pin i p <;> rfl
    simp only [e, kext_bool]

/-! ## Binary delay semantics -/

section Semantics
variable {ι ν : Type}

/-- **Causal arbitrary-delay semantics.** `c t` is the input vector at time `t`
and `σ t` the node values. At each step each node either holds, or takes its
Boolean gate function applied to samples of each input and each node taken at
arbitrary earlier times (per-wire sample times). Transport, inertial, bounded,
unbounded, gate and wire delays are all special cases. -/
def Causal (N : Net ι ν) (c : Nat → ι → Bool) (σ : Nat → ν → Bool) : Prop :=
  ∀ t i, σ (t + 1) i = σ t i ∨
    ∃ (τi : ι → Nat) (τn : ν → Nat), (∀ x, τi x ≤ t) ∧ (∀ j, τn j ≤ t) ∧
      σ (t + 1) i = N.fb (fun x => c (τi x) x) (fun j => σ (τn j) j) i

/-- The GMW step (unbounded gate delay, ideal wires): any subset of nodes
fires, a firing node takes its current excitation. -/
def GStep (N : Net ι ν) (a : ι → Bool) (s s' : ν → Bool) : Prop :=
  ∀ i, s' i = s i ∨ s' i = N.fb a s i

/-- A GMW run is a causal signal. -/
theorem gmw_causal (N : Net ι ν) (c : Nat → ι → Bool) (σ : Nat → ν → Bool)
    (h : ∀ t, GStep N (c t) (σ t) (σ (t + 1))) : Causal N c σ := by
  intro t i
  rcases h t i with h | h
  · exact Or.inl h
  · exact Or.inr ⟨fun _ => t, fun _ => t, fun _ => Nat.le_refl _, fun _ => Nat.le_refl _, h⟩

/-- **Bounded staleness `D`** (bounded-delay hypothesis): from time `D` on, every
node value is its gate function of samples taken within the last `D` steps. -/
def Stale (N : Net ι ν) (c : Nat → ι → Bool) (σ : Nat → ν → Bool) (D : Nat) : Prop :=
  ∀ t i, D ≤ t →
    ∃ (τi : ι → Nat) (τn : ν → Nat), (∀ x, t - D ≤ τi x ∧ τi x < t) ∧
      (∀ j, t - D ≤ τn j ∧ τn j < t) ∧
      σ t i = N.fb (fun x => c (τi x) x) (fun j => σ (τn j) j) i

end Semantics

/-! ## (3) Soundness of post-fixed points (the core of algorithm A) -/

section Sound
variable {ι ν : Type} (N : Net ι ν)

/-- **Soundness.** If `p` is a post-fixed point of the ternary network under
input over-approximation `u` (`p ⊑ F u p`), covers the initial state, and `u`
covers the inputs at every time, then `p` covers the state at every time, for
every causal (arbitrary-delay) behaviour. -/
theorem sound_postfix {u : ι → K3} {p : ν → K3} (hp : VLe p (N.F u p))
    {c : Nat → ι → Bool} {σ : Nat → ν → Bool} (hc : ∀ t, VLe u (vb (c t)))
    (hσ : Causal N c σ) (h0 : VLe p (vb (σ 0))) : ∀ t, VLe p (vb (σ t)) := by
  have key : ∀ t, ∀ t' ≤ t, VLe p (vb (σ t')) := by
    intro t
    induction t with
    | zero => intro t' ht'; rw [Nat.le_zero.mp ht']; exact h0
    | succ t IH =>
      intro t' ht'
      rcases Nat.lt_or_ge t' (t + 1) with hl | hge
      · exact IH t' (by omega)
      · have e : t' = t + 1 := by omega
        subst e
        intro i
        rcases hσ t i with h | ⟨τi, τn, hτi, hτn, h⟩
        · show p i ⊑ ofBool (σ (t + 1) i)
          rw [h]; exact IH t (Nat.le_refl _) i
        · show p i ⊑ ofBool (σ (t + 1) i)
          rw [h]
          refine le_trans (hp i) (N.cover ?_ ?_ i)
          · intro x; exact hc (τi x) x
          · intro j; exact IH (τn j) (hτn j) j
  intro t; exact key t t (Nat.le_refl _)

end Sound

/-! ## (2) Algorithm A: monotone iteration to a fixed point -/

section Iter
variable {ι ν : Type} (N : Net ι ν)

/-- One step of algorithm A: `t ↦ t ⊓ F u t`. -/
def stepA (u : ι → K3) (t : ν → K3) : ν → K3 := fun i => meet (t i) (N.F u t i)

/-- A-iterates from `t0`. -/
def iterA (u : ι → K3) (t0 : ν → K3) : Nat → ν → K3
  | 0 => t0
  | k + 1 => stepA N u (iterA u t0 k)

/-- B-iterates from `t0` with binary inputs `b`. -/
def iterB (b : ι → Bool) (t0 : ν → K3) : Nat → ν → K3
  | 0 => t0
  | k + 1 => N.F (vb b) (iterB b t0 k)

theorem iterA_antitone (u : ι → K3) (t0 : ν → K3) (k : Nat) :
    VLe (iterA N u t0 (k + 1)) (iterA N u t0 k) := fun _ => meet_le_left _ _

/-- The A-iterates dominate every post-fixed point below the start: the
fixed point of algorithm A is the *greatest* (most informative) sound certificate. -/
theorem le_iterA {u : ι → K3} {t0 p : ν → K3} (hp : VLe p (N.F u p)) (h0 : VLe p t0) :
    ∀ k, VLe p (iterA N u t0 k)
  | 0 => h0
  | k + 1 => fun i =>
      le_meet (le_iterA hp h0 k i)
        (le_trans (hp i) (N.mono _ _ _ _ (vle_refl u) (le_iterA hp h0 k) i))

theorem iterB_mono {b : ι → Bool} {t0 : ν → K3} (h0 : VLe t0 (N.F (vb b) t0)) :
    ∀ k, VLe (iterB N b t0 k) (iterB N b t0 (k + 1))
  | 0 => h0
  | k + 1 => N.mono _ _ _ _ (vle_refl _) (iterB_mono h0 k)

end Iter

/-! ### Termination: a fixed point within `|ν| + 1` steps -/

section Count

/-- Generic: an iteration whose every non-stationary step strictly lowers a
natural measure is stationary from step `μ (seq 0)` on. -/
theorem stationary_of_measure {β : Type} (g : β → β) (seq : Nat → β)
    (hseq : ∀ k, seq (k + 1) = g (seq k)) (μ : β → Nat)
    (hdec : ∀ k, g (seq k) = seq k ∨ μ (g (seq k)) < μ (seq k)) :
    ∀ M, μ (seq 0) ≤ M → g (seq M) = seq M := by
  have claim : ∀ k, g (seq k) = seq k ∨ μ (seq k) + k ≤ μ (seq 0) := by
    intro k
    induction k with
    | zero => exact Or.inr (by omega)
    | succ k IH =>
      rcases IH with h | h
      · left; rw [hseq, h, h]
      · rcases hdec k with h' | h'
        · left; rw [hseq, h', h']
        · rcases hdec (k + 1) with h'' | h''
          · exact Or.inl h''
          · right; rw [hseq]; omega
  intro M hM
  rcases claim M with h | h
  · exact h
  · rcases hdec M with h' | h'
    · exact h'
    · omega

/-- Weighted count over a list. -/
def cnt {α : Type} (l : List α) (w : α → Nat) : Nat := (l.map w).sum

theorem cnt_le {α : Type} (l : List α) {w w' : α → Nat} (h : ∀ x, w x ≤ w' x) :
    cnt l w ≤ cnt l w' := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons x l IH => simp only [cnt, List.map_cons, List.sum_cons] at IH ⊢; have := h x; omega

theorem cnt_lt {α : Type} (l : List α) {w w' : α → Nat} (h : ∀ x, w x ≤ w' x)
    {y : α} (hy : y ∈ l) (hlt : w y < w' y) : cnt l w < cnt l w' := by
  induction l with
  | nil => cases hy
  | cons x l IH =>
    simp only [cnt, List.map_cons, List.sum_cons] at IH ⊢
    have hx := h x
    have hl := cnt_le l h
    simp only [cnt] at hl
    rcases List.mem_cons.mp hy with e | e
    · subst e; omega
    · have := IH e; omega

theorem cnt_le_length {α : Type} (l : List α) {w : α → Nat} (h : ∀ x, w x ≤ 1) :
    cnt l w ≤ l.length := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons x l IH => simp only [cnt, List.map_cons, List.sum_cons, List.length_cons] at IH ⊢; have := h x; omega

/-- Number of defined (non-`X`) nodes. -/
def ndef {ν : Type} (l : List ν) (t : ν → K3) : Nat := cnt l (fun i => if t i = X then 0 else 1)
/-- Number of `X` nodes. -/
def nX {ν : Type} (l : List ν) (t : ν → K3) : Nat := cnt l (fun i => if t i = X then 1 else 0)

theorem ndef_lt {ν : Type} {l : List ν} (hl : ∀ i, i ∈ l) {t t' : ν → K3}
    (h : VLe t' t) (hne : t' ≠ t) : ndef l t' < ndef l t := by
  have : ∃ i, t' i ≠ t i := Classical.byContradiction fun hn =>
    hne (funext fun i => Classical.byContradiction fun hi => hn ⟨i, hi⟩)
  obtain ⟨i, hi⟩ := this
  apply cnt_lt l _ (hl i)
  · have := h i
    revert hi this; cases t' i <;> cases t i <;> decide
  · intro j; have := h j
    revert this; cases t' j <;> cases t j <;> decide

theorem nX_lt {ν : Type} {l : List ν} (hl : ∀ i, i ∈ l) {t t' : ν → K3}
    (h : VLe t t') (hne : t' ≠ t) : nX l t' < nX l t := by
  have : ∃ i, t' i ≠ t i := Classical.byContradiction fun hn =>
    hne (funext fun i => Classical.byContradiction fun hi => hn ⟨i, hi⟩)
  obtain ⟨i, hi⟩ := this
  apply cnt_lt l _ (hl i)
  · have := h i
    revert hi this; cases t' i <;> cases t i <;> decide
  · intro j; have := h j
    revert this; cases t' j <;> cases t j <;> decide

variable {ι ν : Type} (N : Net ι ν)

/-- **(2)** Algorithm A is stationary after `|l| ` steps, `l` an enumeration of the nodes. -/
theorem iterA_fix (l : List ν) (hl : ∀ i, i ∈ l) (u : ι → K3) (t0 : ν → K3) :
    stepA N u (iterA N u t0 l.length) = iterA N u t0 l.length := by
  apply stationary_of_measure (stepA N u) (iterA N u t0) (fun _ => rfl) (ndef l)
  · intro k
    by_cases h : stepA N u (iterA N u t0 k) = iterA N u t0 k
    · exact Or.inl h
    · exact Or.inr (ndef_lt hl (iterA_antitone N u t0 k) h)
  · exact cnt_le_length l (fun _ => by split <;> decide)

/-- Algorithm B is stationary after `|l|` steps (when started at a post-fixed point). -/
theorem iterB_fix (l : List ν) (hl : ∀ i, i ∈ l) (b : ι → Bool) {t0 : ν → K3}
    (h0 : VLe t0 (N.F (vb b) t0)) :
    N.F (vb b) (iterB N b t0 l.length) = iterB N b t0 l.length := by
  apply stationary_of_measure (N.F (vb b)) (iterB N b t0) (fun _ => rfl) (nX l)
  · intro k
    by_cases h : N.F (vb b) (iterB N b t0 k) = iterB N b t0 k
    · exact Or.inl h
    · exact Or.inr (nX_lt hl (iterB_mono N h0 k) h)
  · exact cnt_le_length l (fun _ => by split <;> decide)

end Count

/-! ## The transition `a → b` -/

section Transition
variable {ι ν : Type} (N : Net ι ν) (l : List ν) (hl : ∀ i, i ∈ l)

/-- Ternary input of algorithm A: the hull of old and new inputs. -/
def uA (a b : ι → Bool) : ι → K3 := vmeet (vb a) (vb b)

/-- Result of algorithm A, starting from the old (binary) state `s0`. -/
def resultA (a b : ι → Bool) (s0 : ν → Bool) : ν → K3 := iterA N (uA a b) (vb s0) l.length

/-- Result of algorithm B. -/
def resultB (a b : ι → Bool) (s0 : ν → Bool) : ν → K3 :=
  iterB N b (resultA N l a b s0) l.length

include hl in
theorem resultA_postfix (a b : ι → Bool) (s0 : ν → Bool) :
    VLe (resultA N l a b s0) (N.F (uA a b) (resultA N l a b s0)) := by
  intro i
  have h := congrFun (iterA_fix N l hl (uA a b) (vb s0)) i
  simp only [resultA]
  rw [← h]
  exact meet_le_right _ _

theorem resultA_le_start (a b : ι → Bool) (s0 : ν → Bool) : VLe (resultA N l a b s0) (vb s0) := by
  have : ∀ k, VLe (iterA N (uA a b) (vb s0) k) (vb s0) := by
    intro k
    induction k with
    | zero => exact vle_refl _
    | succ k IH => exact vle_trans (iterA_antitone N _ _ k) IH
  exact this _

include hl in
/-- **(3) Soundness of algorithm A.** In any causal (arbitrary-delay) behaviour
starting at `s0`, whose inputs at every time take, input by input, either the
old value `a` or the new value `b`, every state is covered by `resultA`. -/
theorem soundA (a b : ι → Bool) (s0 : ν → Bool)
    (c : Nat → ι → Bool) (σ : Nat → ν → Bool)
    (hc : ∀ t x, c t x = a x ∨ c t x = b x) (hσ : Causal N c σ) (h0 : σ 0 = s0) :
    ∀ t, VLe (resultA N l a b s0) (vb (σ t)) :=
  sound_postfix N (resultA_postfix N l hl a b s0) (fun t => hull_le (hc t)) hσ
    (by rw [h0]; exact resultA_le_start N l a b s0)

include hl in
/-- **No glitch.** A node binary in `resultA` holds that value at all times. -/
theorem noGlitchA (a b : ι → Bool) (s0 : ν → Bool)
    (c : Nat → ι → Bool) (σ : Nat → ν → Bool)
    (hc : ∀ t x, c t x = a x ∨ c t x = b x) (hσ : Causal N c σ) (h0 : σ 0 = s0)
    (i : ν) (v : Bool) (hv : resultA N l a b s0 i = ofBool v) : ∀ t, σ t i = v := by
  intro t
  have h := soundA N l hl a b s0 c σ hc hσ h0 t i
  rw [hv] at h
  exact ofBool_inj.mp (ofBool_le_iff.mp h)

/-- Any other sound certificate is no more informative than `resultA`. -/
theorem resultA_greatest (a b : ι → Bool) (s0 : ν → Bool) {p : ν → K3}
    (hp : VLe p (N.F (uA a b) p)) (h0 : VLe p (vb s0)) : VLe p (resultA N l a b s0) :=
  le_iterA N hp h0 _

include hl in
theorem resultA_postfix_b (a b : ι → Bool) (s0 : ν → Bool) :
    VLe (resultA N l a b s0) (N.F (vb b) (resultA N l a b s0)) :=
  vle_trans (resultA_postfix N l hl a b s0)
    (N.mono _ _ _ _ (hull_le (fun _ => Or.inr rfl)) (vle_refl _))

include hl in
/-- **(4) Settling (algorithm B).** Inputs move between `a` and `b` (per input)
until `T0`, and equal `b` from `T0` on; the behaviour is causal and has bounded
staleness `D`. Then the `k`-th B-iterate covers every state from time
`T0 + k·D` on. -/
theorem settleB (a b : ι → Bool) (s0 : ν → Bool)
    (c : Nat → ι → Bool) (σ : Nat → ν → Bool)
    (hc : ∀ t x, c t x = a x ∨ c t x = b x) (T0 : Nat) (hb : ∀ t, T0 ≤ t → c t = b)
    (hσ : Causal N c σ) (D : Nat) (hD : Stale N c σ D) (h0 : σ 0 = s0) :
    ∀ k t, T0 + k * D ≤ t → VLe (iterB N b (resultA N l a b s0) k) (vb (σ t)) := by
  intro k
  induction k with
  | zero => intro t _; exact soundA N l hl a b s0 c σ hc hσ h0 t
  | succ k IH =>
    intro t ht i
    have hDt : D ≤ t := by rw [Nat.succ_mul] at ht; omega
    obtain ⟨τi, τn, hτi, hτn, h⟩ := hD t i hDt
    show N.F (vb b) (iterB N b (resultA N l a b s0) k) i ⊑ ofBool (σ t i)
    rw [h]
    apply N.cover
    · intro x
      have : c (τi x) = b := hb _ (by have := hτi x; rw [Nat.succ_mul] at ht; omega)
      show vb b x ⊑ ofBool (c (τi x) x)
      rw [this]; exact le_refl _
    · intro j
      exact IH (τn j) (by have := hτn j; rw [Nat.succ_mul] at ht; omega) j

include hl in
/-- A node binary in the `k`-th B-iterate has settled to that value by `T0 + k·D`. -/
theorem settleB_value (a b : ι → Bool) (s0 : ν → Bool)
    (c : Nat → ι → Bool) (σ : Nat → ν → Bool)
    (hc : ∀ t x, c t x = a x ∨ c t x = b x) (T0 : Nat) (hb : ∀ t, T0 ≤ t → c t = b)
    (hσ : Causal N c σ) (D : Nat) (hD : Stale N c σ D) (h0 : σ 0 = s0)
    (k : Nat) (i : ν) (v : Bool) (hv : iterB N b (resultA N l a b s0) k i = ofBool v) :
    ∀ t, T0 + k * D ≤ t → σ t i = v := by
  intro t ht
  have h := settleB N l hl a b s0 c σ hc T0 hb hσ D hD h0 k t ht i
  rw [hv] at h
  exact ofBool_inj.mp (ofBool_le_iff.mp h)

include hl in
/-- The same for `resultB` (= the `|ν|`-th B-iterate, a fixed point). -/
theorem settleResultB (a b : ι → Bool) (s0 : ν → Bool)
    (c : Nat → ι → Bool) (σ : Nat → ν → Bool)
    (hc : ∀ t x, c t x = a x ∨ c t x = b x) (T0 : Nat) (hb : ∀ t, T0 ≤ t → c t = b)
    (hσ : Causal N c σ) (D : Nat) (hD : Stale N c σ D) (h0 : σ 0 = s0)
    (i : ν) (v : Bool) (hv : resultB N l a b s0 i = ofBool v) :
    ∀ t, T0 + l.length * D ≤ t → σ t i = v :=
  settleB_value N l hl a b s0 c σ hc T0 hb hσ D hD h0 l.length i v hv

include hl in
theorem resultB_fix (a b : ι → Bool) (s0 : ν → Bool) :
    N.F (vb b) (resultB N l a b s0) = resultB N l a b s0 :=
  iterB_fix N l hl b (resultA_postfix_b N l hl a b s0)

end Transition

/-! ## Example: the C-element `bd_c2` (cells/rtl/bd_ce.v)

`LUT6 #(.INIT(64'h00E8_00E8_00E8_00E8))` with `I0=a, I1=b, I2=q, I3=rst`,
`I4=I5=0`, output `q`. With `I4=I5=0` only `INIT[15:0] = 0x00E8` is addressed,
so it is modelled as a LUT4 with table `0x00E8`: `q' = maj(a,b,q)·¬rst`.
Inputs `Fin 3` = (a, b, rst); one node (`Unit`) = `q`, fed back to `I2`. -/

section BdC2

/-- LUT address of a Boolean pin vector, `I0` = least significant bit. -/
def addr : {k : Nat} → (Fin k → Bool) → Nat
  | 0, _ => 0
  | _ + 1, x => (x 0).toNat + 2 * addr (vtail x)

/-- Truth table of an INIT constant. -/
def initTbl (init : Nat) {k : Nat} (x : Fin k → Bool) : Bool := Nat.testBit init (addr x)

def bdc2 : LutNet (Fin 3) Unit where
  arity _ := 4
  pin _ p := if p.val = 0 then .inl 0 else if p.val = 1 then .inl 1
    else if p.val = 2 then .inr () else .inl 2
  tbl _ := initTbl 0x00E8

def bdc2Net : Net (Fin 3) Unit := bdc2.toNet

/-- The Boolean function is `maj(a,b,q) ∧ ¬rst`. -/
theorem bdc2_fb (a b r q : Bool) :
    bdc2Net.fb (fun x => if x.val = 0 then a else if x.val = 1 then b else r) (fun _ => q) () =
      (((a && b) || (a && q) || (b && q)) && !r) := by
  revert a b r q; decide

/-- Input vector `(a, b, rst)`. -/
def inp (a b r : Bool) : Fin 3 → Bool := fun x => if x.val = 0 then a else if x.val = 1 then b else r

/-- Flip input `j`. -/
def flip (v : Fin 3 → Bool) (j : Fin 3) : Fin 3 → Bool := fun x => if x = j then !v x else v x

def rA (a : Fin 3 → Bool) (j : Fin 3) (q : Bool) : K3 :=
  resultA bdc2Net [()] a (flip a j) (fun _ => q) ()
def rB (a : Fin 3 → Bool) (j : Fin 3) (q : Bool) : K3 :=
  resultB bdc2Net [()] a (flip a j) (fun _ => q) ()

/-- `a` rises while `b = 0`, `q = 0`: algorithm A gives `0` — `q` never glitches. -/
theorem bdc2_a_rise_hold : rA (inp false false false) 0 false = .zero := by decide

/-- `b` rises while `a = 1`, `q = 0`: A gives `X` (q may move), B gives `1`. -/
theorem bdc2_b_rise_fire :
    rA (inp true false false) 1 false = .X ∧ rB (inp true false false) 1 false = .one := by
  decide

/-- `rst` rises while holding `1`: A gives `X`, B gives `0` (reset wins). -/
theorem bdc2_rst_rise :
    rA (inp true true false) 2 true = .X ∧ rB (inp true true false) 2 true = .zero := by
  decide

/-- **Exhaustive single-input check for bd_c2.** From every stable state
(`q = fb(a,b,rst,q)`), for every single input flip:
(i) algorithm B gives a binary value — the cell settles deterministically, no
oscillation and no unresolved race; and (ii) if that value equals the old `q`,
algorithm A already gives it — no static hazard on `q`. -/
theorem bdc2_single_input_ok :
    ∀ a b r q : Bool, ∀ j : Fin 3,
      bdc2Net.fb (inp a b r) (fun _ => q) () = q →
        rB (inp a b r) j q ≠ .X ∧
        (rB (inp a b r) j q = ofBool q → rA (inp a b r) j q = ofBool q) := by
  decide

/-- The proved check, transported to behaviours: for any causal (arbitrary
delay) behaviour of `bd_c2` in which a single input flips (it may even flip
back and forth), if the final value of `q` equals the initial one, `q` never
changes. -/
theorem bdc2_no_static_hazard (a b r q : Bool) (j : Fin 3)
    (hst : bdc2Net.fb (inp a b r) (fun _ => q) () = q)
    (hsame : rB (inp a b r) j q = ofBool q)
    (c : Nat → Fin 3 → Bool) (σ : Nat → Unit → Bool)
    (hc : ∀ t x, c t x = inp a b r x ∨ c t x = flip (inp a b r) j x)
    (hσ : Causal bdc2Net c σ) (h0 : σ 0 = fun _ => q) : ∀ t, σ t () = q := by
  have hA := ((bdc2_single_input_ok a b r q j hst).2 hsame)
  exact noGlitchA bdc2Net [()] (fun i => by cases i; exact List.mem_singleton.mpr rfl)
    _ _ _ c σ hc hσ h0 () q hA

/-- And it settles: once the input is at its new value from `T0`, with bounded
staleness `D`, `q` equals the B result from `T0 + D` on. -/
theorem bdc2_settles (a b r q : Bool) (j : Fin 3) (v : Bool)
    (hv : rB (inp a b r) j q = ofBool v)
    (c : Nat → Fin 3 → Bool) (σ : Nat → Unit → Bool)
    (hc : ∀ t x, c t x = inp a b r x ∨ c t x = flip (inp a b r) j x)
    (T0 : Nat) (hb : ∀ t, T0 ≤ t → c t = flip (inp a b r) j)
    (hσ : Causal bdc2Net c σ) (D : Nat) (hD : Stale bdc2Net c σ D) (h0 : σ 0 = fun _ => q) :
    ∀ t, T0 + 1 * D ≤ t → σ t () = v :=
  settleResultB bdc2Net [()] (fun i => by cases i; exact List.mem_singleton.mpr rfl)
    _ _ _ c σ hc T0 hb hσ D hD h0 () v hv

/-- The check is not vacuous: `a` rising while `b` falls (`q = 0`, both
opposite-sense changes at once). Algorithm A gives `X` — a glitch is possible
(if `a` arrives first the LUT sees `maj(1,1,0) = 1`) — and algorithm B gives `X`
too: the glitch can be *latched* by the feedback (`maj(1,0,q) = q`), so the
final value is not determined. Multi-input opposite-sense transitions must be
excluded by the protocol. -/
theorem bdc2_two_input_hazard :
    resultA bdc2Net [()] (inp false true false) (inp true false false) (fun _ => false) () = .X ∧
    resultB bdc2Net [()] (inp false true false) (inp true false false) (fun _ => false) () = .X := by
  decide

end BdC2

end Formal.Core.Ternary
