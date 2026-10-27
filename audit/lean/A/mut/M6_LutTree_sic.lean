/-!
# Formal.Core.LutTree — the 7-series LUT as a pass-transistor 2:1 mux tree

Track 4 (gate fidelity), shard A. Self-contained, no Mathlib, core Lean only.
Notes: `formal/notes/A-lut-tree.md`.

A LUT is not a Boolean function. It is a binary tree of 2:1 pass-transistor
muxes. Its leaves are SRAM configuration cells (the INIT bits). The select of every mux on
one level is one LUT input pin, after that pin's input buffer. On a 7-series
LUT6 the root mux is selected by A6 (= "I5"): O6 = A6 ? upper LUT5 : lower LUT5,
and O5 is the lower LUT5 tapped before that root mux. Vivado documents A6/A5 as the fast pins and A1/A2
as the slow ones (UG904/UG903 LOCK_PINS), which fits A6 at the root and A1
at the leaf (SRAM) side of the tree. Inputs are therefore listed here
ROOT FIRST: `[A6, A5, A4, A3, A2, A1]`, and a leaf address `w : List Bool`
is MSB-first, so INIT bit index = A6·32 + … + A1·1 (A1 = bit 0, as Xilinx).

Contents
1. `K3`, `kmux` (Kleene 2:1 mux), information order `Le`.
2. `evalTree`: Kleene evaluation of the mux tree from its INIT.
3. `tableEval`: INIT-table Kleene semantics ("1 if all consistent entries
   are 1, 0 if all are 0, else X"), with `mem_addrs_iff`, `tableEval_eq_one_iff`,
   `tableEval_eq_zero_iff`.
4. **Fidelity theorem** `evalTree_eq_tableEval`: for every k, INIT and K3 input
   vector, the two semantics agree. Corollary `evalTree_swap`: the Kleene
   function does not depend on which input drives which tree level.
5. Timed physical tree `PhysTree` with per-mux select and data delays and
   per-copy input arrival (input buffers + distribution). Explicit hypotheses
   `H_sram`, `H_mux_kleene`. Soundness `PhysTree.node_sound`/`root_sound`:
   every node at every instant is at least as defined as the static Kleene
   value. **Glitch freedom** `PhysTree.glitch_free` (no function hazard ⇒ output
   constant for ANY delays), `PhysTree.sic_glitch_free` (single input change
   with equal output values ⇒ no glitch).
6. Exact (Kleene-equality) timed model `exactNode`: it satisfies the
   hypotheses (`exact_H_mux`), and a two-input change with a function hazard
   does glitch in it depending on arrival order (`and_glitch`,
   `and_no_glitch_other_order`).
7. LUT6_2 (`lut6O6`, `lut6O5`): O6 = kmux A6 O5 upper, and INIT addressing.
-/

namespace Formal.Core.LutTree

/-! ## 1. Three-valued levels and the Kleene mux -/

/-- Kleene level. `X` = not a valid logic level (unknown, in transit, mid-rail). -/
inductive K3 where
  | zero
  | one
  | X
  deriving DecidableEq, Repr

namespace K3

def ofBool : Bool → K3
  | false => zero
  | true => one

@[simp] theorem ofBool_false : ofBool false = zero := rfl
@[simp] theorem ofBool_true : ofBool true = one := rfl

/-- Information order: `Le a b` iff `a = X` or `a = b` (b at least as defined). -/
def Le (a b : K3) : Prop := a = X ∨ a = b

instance (a b : K3) : Decidable (Le a b) := inferInstanceAs (Decidable (_ ∨ _))

theorem Le.refl (a : K3) : Le a a := Or.inr rfl

theorem Le.trans {a b c : K3} : Le a b → Le b c → Le a c := by
  cases a <;> cases b <;> cases c <;> decide

theorem Le.ofBool_eq {c : Bool} {z : K3} (h : Le (ofBool c) z) : z = ofBool c := by
  cases c <;> cases z <;> revert h <;> decide

end K3

open K3

/-- Kleene 2:1 mux: select 0 → `a`, select 1 → `b`, select X → `a` if `a = b`,
else X. This is the hypothesis a pass-transistor mux is asked to meet
(`H_mux_kleene`); it is the definition here. -/
def kmux : K3 → K3 → K3 → K3
  | .zero, a, _ => a
  | .one, _, b => b
  | .X, a, b => if a = b then a else .X

/-- `kmux` is monotone in all three arguments (X-passing). -/
theorem kmux_mono {s s' a a' b b' : K3} :
    Le s s' → Le a a' → Le b b' → Le (kmux s a b) (kmux s' a' b') := by
  cases s <;> cases s' <;> cases a <;> cases a' <;> cases b <;> cases b' <;> decide

/-- Swapping two adjacent tree levels (relabelling the four grand-children)
does not change the Kleene value. -/
theorem kmux_swap_levels (a b p q r s : K3) :
    kmux a (kmux b p q) (kmux b r s) = kmux b (kmux a p r) (kmux a q s) := by
  cases a <;> cases b <;> cases p <;> cases q <;> cases r <;> cases s <;> decide

/-! ## 2. Mux-tree Kleene evaluation -/

/-- Kleene evaluation of a mux tree. The input list is root first, and `g` is
the INIT table addressed by root-first (MSB-first) leaf paths. -/
def evalTree : List K3 → (List Bool → Bool) → K3
  | [], g => ofBool (g [])
  | k :: v, g =>
      kmux k (evalTree v (fun w => g (false :: w))) (evalTree v (fun w => g (true :: w)))

/-! ## 3. INIT-table Kleene semantics -/

/-- Boolean values consistent with one K3 input. -/
def opts : K3 → List Bool
  | .zero => [false]
  | .one => [true]
  | .X => [false, true]

/-- All INIT addresses consistent with a K3 input vector. -/
def addrs : List K3 → List (List Bool)
  | [] => [[]]
  | k :: v => (opts k).flatMap (fun b => (addrs v).map (b :: ·))

/-- Pointwise consistency of an address with a K3 vector. -/
def Consistent : List K3 → List Bool → Prop
  | [], [] => True
  | k :: v, b :: w => (k = .X ∨ k = ofBool b) ∧ Consistent v w
  | _, _ => False

theorem mem_opts_iff (k : K3) (b : Bool) : b ∈ opts k ↔ (k = .X ∨ k = ofBool b) := by
  cases k <;> cases b <;> simp [opts]

theorem mem_addrs_iff : ∀ (v : List K3) (w : List Bool), w ∈ addrs v ↔ Consistent v w
  | [], [] => by simp [addrs, Consistent]
  | [], _ :: _ => by simp [addrs, Consistent]
  | _ :: _, [] => by simp [addrs, Consistent]
  | k :: v, b :: w => by
      simp only [addrs, List.mem_flatMap, List.mem_map, Consistent, mem_addrs_iff v]
      constructor
      · rintro ⟨b', hb', w', hw', h⟩
        cases h
        exact ⟨(mem_opts_iff k b).1 hb', hw'⟩
      · rintro ⟨hk, hw⟩
        exact ⟨b, (mem_opts_iff k b).2 hk, w, hw, rfl⟩

theorem addrs_ne_nil : ∀ v : List K3, addrs v ≠ []
  | [] => by simp [addrs]
  | k :: v => by
      have ih := addrs_ne_nil v
      obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ ih
      cases k <;> simp [addrs, opts] <;> exact ih

/-- Summary of a set of table entries: 1 if all 1, 0 if all 0, else X. -/
def summ (allOne allZero : Bool) : K3 :=
  if allOne then .one else if allZero then .zero else .X

/-- INIT-table Kleene semantics: 1 if every consistent INIT entry is 1, 0 if
every one is 0, X otherwise. -/
def tableEval (v : List K3) (g : List Bool → Bool) : K3 :=
  summ ((addrs v).all g) ((addrs v).all (fun w => !g w))

theorem tableEval_eq_one_iff (v : List K3) (g : List Bool → Bool) :
    tableEval v g = .one ↔ ∀ w, Consistent v w → g w = true := by
  unfold tableEval
  constructor
  · intro h w hw
    cases hA : (addrs v).all g
    · cases hB : (addrs v).all (fun w => !g w) <;> simp [summ, hA, hB] at h
    · exact (List.all_eq_true.1 hA) w ((mem_addrs_iff v w).2 hw)
  · intro h
    have : (addrs v).all g = true :=
      List.all_eq_true.2 (fun w hw => h w ((mem_addrs_iff v w).1 hw))
    simp [summ, this]

theorem tableEval_eq_zero_iff (v : List K3) (g : List Bool → Bool) :
    tableEval v g = .zero ↔ ∀ w, Consistent v w → g w = false := by
  unfold tableEval
  obtain ⟨w0, hw0⟩ := List.exists_mem_of_ne_nil _ (addrs_ne_nil v)
  constructor
  · intro h w hw
    cases hB : (addrs v).all (fun w => !g w)
    · cases hA : (addrs v).all g <;> simp [summ, hA, hB] at h
    · have := (List.all_eq_true.1 hB) w ((mem_addrs_iff v w).2 hw)
      simpa using this
  · intro h
    have hB : (addrs v).all (fun w => !g w) = true :=
      List.all_eq_true.2 (fun w hw => by simp [h w ((mem_addrs_iff v w).1 hw)])
    have hA : (addrs v).all g = false := by
      cases hh : (addrs v).all g
      · rfl
      · have := (List.all_eq_true.1 hh) w0 hw0
        simp [h w0 ((mem_addrs_iff v w0).1 hw0)] at this
    simp [summ, hA, hB]

/-- A nonempty set of entries cannot be both all-1 and all-0. -/
theorem all_and_all_false (v : List K3) (g : List Bool → Bool) :
    ((addrs v).all g && (addrs v).all (fun w => !g w)) = false := by
  obtain ⟨w0, hw0⟩ := List.exists_mem_of_ne_nil _ (addrs_ne_nil v)
  cases hA : (addrs v).all g
  · rfl
  · cases hB : (addrs v).all (fun w => !g w)
    · rfl
    · have h1 := (List.all_eq_true.1 hA) w0 hw0
      have h2 := (List.all_eq_true.1 hB) w0 hw0
      simp [h1] at h2

theorem summ_join (aT aF bT bF : Bool) (ha : (aT && aF) = false) (hb : (bT && bF) = false) :
    summ (aT && bT) (aF && bF) = kmux .X (summ aT aF) (summ bT bF) := by
  cases aT <;> cases aF <;> cases bT <;> cases bF <;> simp_all [summ, kmux]

/-! ## 4. The fidelity theorem -/

/-- **Fidelity theorem.** Kleene evaluation of the mux tree equals the
INIT-table Kleene semantics, for every number of inputs, every INIT and
every K3 input vector. -/
theorem evalTree_eq_tableEval : ∀ (v : List K3) (g : List Bool → Bool),
    evalTree v g = tableEval v g
  | [], g => by cases h : g [] <;> simp [evalTree, tableEval, addrs, summ, h]
  | k :: v, g => by
      rw [evalTree, evalTree_eq_tableEval v, evalTree_eq_tableEval v]
      cases k
      · simp [kmux, tableEval, addrs, opts, List.all_map, Function.comp_def]
      · simp [kmux, tableEval, addrs, opts, List.all_map, Function.comp_def]
      · have h := summ_join _ _ _ _ (all_and_all_false v (fun w => g (false :: w)))
          (all_and_all_false v (fun w => g (true :: w)))
        simp only [tableEval]
        rw [← h]
        simp [addrs, opts, List.all_map, Function.comp_def, List.all_append]

/-- Corollary in Kleene semantics: swapping the input assignment of two adjacent tree levels,
with the INIT permuted to match, gives the same function. So the Kleene
behaviour of the LUT does not depend on which input drives which level, and
any order (A6 at the root as in silicon, or A1 at the root as in
`cells/gls/prims.v`) gives the same Kleene function. Only timing can tell
the orders apart (Section 5). -/
theorem evalTree_swap (a b : K3) (v : List K3) (g : List Bool → Bool) :
    evalTree (a :: b :: v) g =
      evalTree (b :: a :: v) (fun w => match w with
        | p :: q :: r => g (q :: p :: r)
        | w => g w) := by
  simp only [evalTree]
  exact kmux_swap_levels _ _ _ _ _ _

/-- Both semantics agree with the Boolean LUT on Boolean inputs. -/
theorem evalTree_ofBool : ∀ (w : List Bool) (g : List Bool → Bool),
    evalTree (w.map ofBool) g = ofBool (g w)
  | [], g => rfl
  | b :: w, g => by
      cases b <;> simp [evalTree, kmux, evalTree_ofBool w]

/-! ## 5. Timed physical tree, explicit hypotheses, glitch freedom -/

/-- Time in ps (any unit). Delays may be any integers. The theorems below
need no bound on them and no ordering between them. -/
abbrev Time := Int

/-- A physical mux tree of depth `n`, observed at every node.
* `init` — SRAM contents (leaf at path `p`, `p.length = n`).
* `pin i τ` — the 3-valued level of input pin at tree level `i` (0 = root).
* `dsel p` — delay from that pin to the select gate of the mux at node `p`.
  This includes the input buffer and the distribution wire to that mux copy, so different
  copies of one input may see the edge at different times.
* `ddat p b` — delay through the mux at `p` from child `b`.
* `y p τ` — the 3-valued level of the node `p` at time `τ` (root = `[]`). -/
structure PhysTree (n : Nat) where
  init : List Bool → Bool
  pin : Nat → Time → K3
  dsel : List Bool → Time
  ddat : List Bool → Bool → Time
  y : List Bool → Time → K3

namespace PhysTree

variable {n : Nat} (P : PhysTree n)

/-- HYPOTHESIS (silicon): SRAM leaves are static and undisturbed by reads
through the pass network. -/
def H_sram : Prop := ∀ p : List Bool, p.length = n → ∀ τ, P.y p τ = ofBool (P.init p)

/-- HYPOTHESIS (silicon): each pass-transistor mux is Kleene-sound at every
instant. Whenever the Kleene mux of its (delayed) select and data is a
valid level, the node is at that level. In particular, a mid-rail select with
equal data inputs passes the data (no charge-sharing dip below a valid level,
and the output restorer holds). When the Kleene mux is X, nothing is assumed. -/
def H_mux_kleene : Prop :=
  ∀ p : List Bool, p.length < n → ∀ τ,
    Le (kmux (P.pin p.length (τ - P.dsel p))
             (P.y (p ++ [false]) (τ - P.ddat p false))
             (P.y (p ++ [true]) (τ - P.ddat p true)))
       (P.y p τ)

/-- The static K3 vector `v` abstracts the pins: at every instant each pin
is at least as defined as `v` says (X = may do anything). -/
def Abstracts (v : List K3) : Prop :=
  v.length = n ∧ ∀ i (h : i < v.length) τ, Le (v[i]'h) (P.pin i τ)

theorem drop_eq_cons {v : List K3} {i : Nat} (h : i < v.length) :
    v.drop i = v[i] :: v.drop (i + 1) := List.drop_eq_getElem_cons h

/-- Soundness at every node: the node waveform is always at least as defined
as the static Kleene value of its subtree, for any delays. -/
theorem node_sound (hs : P.H_sram) (hm : P.H_mux_kleene) {v : List K3}
    (hv : P.Abstracts v) :
    ∀ m (p : List Bool), p.length + m = n → ∀ τ,
      Le (evalTree (v.drop p.length) (fun w => P.init (p ++ w))) (P.y p τ) := by
  have hlen := hv.1
  intro m
  induction m with
  | zero =>
      intro p hp τ
      have hd : v.drop p.length = [] := by
        apply List.drop_eq_nil_of_le; omega
      rw [hd, hs p (by omega) τ]
      simp only [evalTree, List.append_nil]
      exact Le.refl _
  | succ m ih =>
      intro p hp τ
      have hlt : p.length < v.length := by omega
      rw [drop_eq_cons hlt]
      simp only [evalTree]
      refine Le.trans ?_ (hm p (by omega) τ)
      have h0 := ih (p ++ [false]) (by simp; omega) (τ - P.ddat p false)
      have h1 := ih (p ++ [true]) (by simp; omega) (τ - P.ddat p true)
      simp only [List.length_append, List.length_singleton, List.append_assoc,
        List.singleton_append] at h0 h1
      exact kmux_mono (hv.2 _ hlt _) h0 h1

/-- Soundness at the output, in table semantics (via the fidelity theorem). -/
theorem root_sound (hs : P.H_sram) (hm : P.H_mux_kleene) {v : List K3}
    (hv : P.Abstracts v) (τ : Time) : Le (tableEval v P.init) (P.y [] τ) := by
  have := P.node_sound hs hm hv n [] (by simp) τ
  simpa [evalTree_eq_tableEval] using this

/-- **Glitch freedom (no function hazard ⇒ no glitch, any delays).** If every
INIT entry consistent with the pins' static abstraction has the same value
`c`, the output is `c` at every instant. The changing pins (X in `v`) may
switch in any order, with any skew, any per-mux delays, and may even dwell
mid-rail or ring. -/
theorem glitch_free (hs : P.H_sram) (hm : P.H_mux_kleene) {v : List K3}
    (hv : P.Abstracts v) (c : Bool) (hc : ∀ w, Consistent v w → P.init w = c)
    (τ : Time) : P.y [] τ = ofBool c := by
  have h := P.root_sound hs hm hv τ
  have ht : tableEval v P.init = ofBool c := by
    cases c
    · exact (tableEval_eq_zero_iff v P.init).2 hc
    · exact (tableEval_eq_one_iff v P.init).2 hc
  rw [ht] at h
  exact h.ofBool_eq

/-! ### Single input change -/

/-- Number of positions where two addresses differ. -/
def ndiff : List Bool → List Bool → Nat
  | a :: as, b :: bs => (if a = b then 0 else 1) + ndiff as bs
  | _, _ => 0

/-- Static abstraction of a transition `old → new`: steady pins keep their
value; changing pins are X. -/
def mergeK : List Bool → List Bool → List K3
  | a :: as, b :: bs => (if a = b then ofBool a else .X) :: mergeK as bs
  | _, _ => []

theorem consistent_mergeK_self : ∀ (as w : List Bool), Consistent (mergeK as as) w → w = as
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [mergeK, Consistent] at h
  | _ :: _, [], h => by simp [mergeK, Consistent] at h
  | a :: as, c :: w, h => by
      simp only [mergeK, Consistent] at h
      obtain ⟨hk, hw⟩ := h
      have : c = a := by cases a <;> cases c <;> simp_all
      rw [this, consistent_mergeK_self as w hw]

theorem ndiff_zero_eq : ∀ (as bs : List Bool), as.length = bs.length → ndiff as bs = 0 → as = bs
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: as, b :: bs, hl, h => by
      simp only [ndiff] at h
      have hab : a = b := by
        by_cases hne : a = b
        · exact hne
        · simp [hne] at h
      subst hab
      simp at h hl
      rw [ndiff_zero_eq as bs hl h]

theorem consistent_mergeK_sic : ∀ (old new w : List Bool), old.length = new.length →
    ndiff old new ≤ 1 → Consistent (mergeK old new) w → w = old ∨ w = new
  | [], [], w, _, _, h => by cases w <;> simp_all [mergeK, Consistent]
  | [], _ :: _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, hl, _, _ => by simp at hl
  | a :: as, b :: bs, w, hl, hd, h => by
      cases w with
      | nil => simp [mergeK, Consistent] at h
      | cons c w =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
        simp only [mergeK, Consistent] at h
        obtain ⟨hk, hw⟩ := h
        by_cases hab : a = b
        · subst hab
          have hc : c = a := by cases a <;> cases c <;> simp_all
          simp only [ndiff] at hd
          simp at hd
          rcases consistent_mergeK_sic as bs w hl hd hw with h | h
          · left; rw [hc, h]
          · right; rw [hc, h]
        · simp only [ndiff] at hd
          simp [hab] at hd
          have hz : ndiff as bs = 0 := by omega
          have heq := ndiff_zero_eq as bs hl hz
          subst heq
          have hw' := consistent_mergeK_self as w hw
          subst hw'
          cases a <;> cases b <;> cases c <;> simp_all

/-- **Single-input-change glitch freedom.** If old and new pin vectors
differ in at most one pin, the LUT gives the same value `c` on both, and every
steady pin holds its value (`Abstracts (mergeK old new)`), then the output is
`c` at every instant. This holds for any per-mux and per-copy delays, whichever level
the changing pin drives, and however slowly or untidily that pin moves. -/
theorem sic_glitch_free (hs : P.H_sram) (hm : P.H_mux_kleene) (old new : List Bool)
    (hl : old.length = new.length) (hd : ndiff old new ≤ 2)
    (hv : P.Abstracts (mergeK old new)) (c : Bool)
    (hold : P.init old = c) (hnew : P.init new = c) (τ : Time) :
    P.y [] τ = ofBool c := by
  refine P.glitch_free hs hm hv c ?_ τ
  intro w hw
  rcases consistent_mergeK_sic old new w hl hd hw with h | h <;> subst h <;> assumption

end PhysTree

/-! ## 6. The exact Kleene timed model (an instance), and a multi-input glitch -/

/-- Exact timed tree: every mux output IS the Kleene mux of its delayed
inputs (`fuel` = remaining depth). This is the most optimistic silicon
consistent with `H_mux_kleene`. Pass-transistor muxes with
pure transport delays behave this way. -/
def exactNode (init : List Bool → Bool) (pin : Nat → Time → K3)
    (dsel : List Bool → Time) (ddat : List Bool → Bool → Time) :
    Nat → List Bool → Time → K3
  | 0, p, _ => ofBool (init p)
  | m + 1, p, τ =>
      kmux (pin p.length (τ - dsel p))
        (exactNode init pin dsel ddat m (p ++ [false]) (τ - ddat p false))
        (exactNode init pin dsel ddat m (p ++ [true]) (τ - ddat p true))

/-- The exact model as a `PhysTree`. -/
def exactTree (n : Nat) (init : List Bool → Bool) (pin : Nat → Time → K3)
    (dsel : List Bool → Time) (ddat : List Bool → Bool → Time) : PhysTree n where
  init := init
  pin := pin
  dsel := dsel
  ddat := ddat
  y := fun p τ => exactNode init pin dsel ddat (n - p.length) p τ

theorem exact_H_sram (n : Nat) init pin dsel ddat : (exactTree n init pin dsel ddat).H_sram := by
  intro p hp τ
  simp [exactTree, hp, exactNode]

theorem exact_H_mux (n : Nat) init pin dsel ddat : (exactTree n init pin dsel ddat).H_mux_kleene := by
  intro p hp τ
  have : n - p.length = (n - (p.length + 1)) + 1 := by omega
  simp only [exactTree, List.length_append, List.length_singleton]
  rw [this, exactNode]
  exact Le.refl _

/-- Two-input AND tree (root A = level 0, leaf B = level 1). -/
def andInit : List Bool → Bool
  | [true, true] => true
  | _ => false

/-- A rises at t=0, B falls at t=10 (pin waveforms, unit delays elsewhere). -/
def pinsAB (tA tB : Time) : Nat → Time → K3
  | 0, τ => if τ < tA then .zero else .one
  | _, τ => if τ < tB then .one else .zero

def andOut (tA tB : Time) (τ : Time) : K3 :=
  exactNode andInit (pinsAB tA tB) (fun _ => 1) (fun _ _ => 1) 2 [] τ

/-- Old (A,B) = (0,1) and new = (1,0) both give 0, but the static abstraction
is (X,X), whose consistent entries include 11 ↦ 1: a function hazard, and
the Kleene abstraction says X. -/
theorem and_abstraction_X : tableEval [.X, .X] andInit = .X := by decide

/-- In the exact model the output really glitches when A arrives before B
falls: it is 0, then 1, then 0. -/
theorem and_glitch :
    andOut 0 10 0 = .zero ∧ andOut 0 10 5 = .one ∧ andOut 0 10 20 = .zero := by
  decide

/-- The same change with the opposite arrival order (B falls first): no glitch
at the sampled instants, so the physical result depends on arrival order and
skew. -/
theorem and_no_glitch_other_order :
    andOut 10 0 0 = .zero ∧ andOut 10 0 5 = .zero ∧ andOut 10 0 20 = .zero := by
  decide

/-! ### Single input change in the exact model: one delayed mux

With every pin but one steady, the exact tree's output is ONE Kleene mux,
selected by the changing pin delayed by the delay `D` of the active path, between
two constants (the old and new INIT entries). So a single input change gives
either a constant output (equal entries) or one clean transition, shifted by a
`D` that depends on the pin's tree level and on the address of the active
path. That is the only place where the order of the inputs in the tree shows. -/

/-- Steady bit levels with level `i` overridden. -/
def setb (c : Nat → Bool) (i : Nat) (b : Bool) (j : Nat) : Bool := if j = i then b else c j

/-- Address segment of levels `lo, …, lo+m-1`. -/
def seg (c : Nat → Bool) : Nat → Nat → List Bool
  | _, 0 => []
  | lo, m + 1 => c lo :: seg c (lo + 1) m

theorem seg_setb_gt (c : Nat → Bool) (i : Nat) (b : Bool) :
    ∀ m lo, i < lo → seg (setb c i b) lo m = seg c lo m
  | 0, _, _ => rfl
  | m + 1, lo, h => by
      simp only [seg, setb, Nat.ne_of_gt h, ite_false]
      rw [seg_setb_gt c i b m (lo + 1) (by omega)]

section exact
variable (init : List Bool → Bool) (pin : Nat → Time → K3)
  (dsel : List Bool → Time) (ddat : List Bool → Bool → Time)

theorem kmux_X_comm (a b : K3) : kmux .X a b = kmux .X b a := by
  cases a <;> cases b <;> decide

theorem kmux_ofBool (b : Bool) (a0 a1 : K3) :
    kmux (ofBool b) a0 a1 = if b then a1 else a0 := by cases b <;> rfl

/-- All pins of the subtree steady ⇒ the subtree output is the INIT entry. -/
theorem exact_const (c : Nat → Bool) :
    ∀ m (p : List Bool), (∀ j, p.length ≤ j → j < p.length + m → ∀ τ, pin j τ = ofBool (c j)) →
      ∀ τ, exactNode init pin dsel ddat m p τ = ofBool (init (p ++ seg c p.length m))
  | 0, p, _, τ => by simp [exactNode, seg]
  | m + 1, p, hc, τ => by
      simp only [exactNode]
      rw [hc p.length (Nat.le_refl _) (by omega), kmux_ofBool]
      have h := fun b => exact_const c m (p ++ [b])
        (fun j h1 h2 τ => hc j (by simp at h1; omega) (by simp at h2; omega) τ)
      cases hb : c p.length
      · simp only [Bool.false_eq_true, ite_false]
        rw [h false]; simp [seg, hb]
      · simp only [ite_true]
        rw [h true]; simp [seg, hb]

/-- **SIC in the exact model**: the output is one mux on the changing pin,
delayed by the active path's delay `D`. -/
theorem exact_sic (c : Nat → Bool) (i : Nat) :
    ∀ m (p : List Bool), p.length ≤ i → i < p.length + m →
      (∀ j, j ≠ i → p.length ≤ j → j < p.length + m → ∀ τ, pin j τ = ofBool (c j)) →
      ∃ D : Time, ∀ τ, exactNode init pin dsel ddat m p τ =
        kmux (pin i (τ - D)) (ofBool (init (p ++ seg (setb c i false) p.length m)))
                             (ofBool (init (p ++ seg (setb c i true) p.length m)))
  | 0, _, h1, h2, _ => by omega
  | m + 1, p, h1, h2, hc => by
      by_cases hi : p.length = i
      · subst hi
        refine ⟨dsel p, fun τ => ?_⟩
        have hk := fun b => exact_const init pin dsel ddat c m (p ++ [b])
          (fun j h1 h2 τ => hc j (by simp at h1; omega) (by simp at h1; omega)
            (by simp at h2; omega) τ)
        simp only [exactNode, hk]
        simp [seg, setb, seg_setb_gt c p.length _ m (p.length + 1) (by omega)]
      · have hlt : p.length < i := by omega
        have hroot := hc p.length (Ne.symm (by omega)) (Nat.le_refl _) (by omega)
        cases hb : c p.length
        · obtain ⟨D, hD⟩ := exact_sic c i m (p ++ [false]) (by simp; omega) (by simp; omega)
            (fun j hj h1 h2 τ => hc j hj (by simp at h1; omega) (by simp at h2; omega) τ)
          refine ⟨ddat p false + D, fun τ => ?_⟩
          simp only [exactNode]
          rw [hroot, hb, kmux_ofBool, hD]
          simp [seg, setb, hb, Int.sub_sub, Nat.ne_of_lt hlt]
        · obtain ⟨D, hD⟩ := exact_sic c i m (p ++ [true]) (by simp; omega) (by simp; omega)
            (fun j hj h1 h2 τ => hc j hj (by simp at h1; omega) (by simp at h2; omega) τ)
          refine ⟨ddat p true + D, fun τ => ?_⟩
          simp only [exactNode]
          rw [hroot, hb, kmux_ofBool, hD]
          simp [seg, setb, hb, Int.sub_sub, Nat.ne_of_lt hlt]

/-- A clean pin edge: `b`, then X on `[t1, t2)`, then `!b`. -/
def CleanEdge (w : Time → K3) (b : Bool) (t1 t2 : Time) : Prop :=
  ∀ τ, (τ < t1 → w τ = ofBool b) ∧ (t1 ≤ τ → τ < t2 → w τ = .X) ∧ (t2 ≤ τ → w τ = ofBool (!b))

/-- A clean edge on the one changing pin gives at most one clean transition at
the output: the old entry, then `kmux X A B` (= the entry if `A = B`, else X), then
the new entry, with every boundary shifted by the same path delay `D`. -/
theorem exact_sic_clean (c : Nat → Bool) (i n : Nat) (hi : i < n)
    (hc : ∀ j, j ≠ i → j < n → ∀ τ, pin j τ = ofBool (c j))
    (b : Bool) (t1 t2 : Time) (he : CleanEdge (pin i) b t1 t2) :
    ∃ D : Time, ∀ τ,
      let A := ofBool (init (seg (setb c i b) 0 n))
      let B := ofBool (init (seg (setb c i (!b)) 0 n))
      (τ < t1 + D → exactNode init pin dsel ddat n [] τ = A) ∧
      (t1 + D ≤ τ → τ < t2 + D → exactNode init pin dsel ddat n [] τ = kmux .X A B) ∧
      (t2 + D ≤ τ → exactNode init pin dsel ddat n [] τ = B) := by
  obtain ⟨D, hD⟩ := exact_sic init pin dsel ddat c i n [] (by simp) (by simpa using hi)
    (fun j hj _ h2 τ => hc j hj (by simpa using h2) τ)
  refine ⟨D, fun τ => ?_⟩
  simp only [List.length_nil, List.nil_append] at hD
  obtain ⟨e1, e2, e3⟩ := he (τ - D)
  simp only [Time] at *
  refine ⟨fun h => ?_, fun h h' => ?_, fun h => ?_⟩
  · rw [hD, e1 (by omega)]; cases b <;> rfl
  · rw [hD, e2 (by omega) (by omega)]
    cases b
    · rfl
    · simp only [Bool.not_true]
      exact kmux_X_comm _ _
  · rw [hD, e3 (by omega)]; cases b <;> rfl

end exact

/-! ## 7. LUT6_2: O5/O6 and INIT addressing -/

/-- INIT bit for a root-first (MSB-first) address: `[A6,…,A1]` ↦ bit A6·32+…+A1. -/
def addrOf : List Bool → Nat
  | [] => 0
  | b :: w => (if b then 2 ^ w.length else 0) + addrOf w

def initFun (init : Nat) (w : List Bool) : Bool := init.testBit (addrOf w)

/-- O6 of a LUT6 with pins `a6 :: rest` (`rest = [A5,…,A1]`). -/
def lut6O6 (init : Nat) (a6 : K3) (rest : List K3) : K3 :=
  evalTree (a6 :: rest) (initFun init)

/-- O5: the lower LUT5 (INIT[31:0]), A1..A5 only. -/
def lut6O5 (init : Nat) (rest : List K3) : K3 :=
  evalTree rest (fun w => initFun init (false :: w))

/-- O6 is the root mux of A6 over O5 and the upper LUT5. -/
theorem lut6O6_eq (init : Nat) (a6 : K3) (rest : List K3) :
    lut6O6 init a6 rest =
      kmux a6 (lut6O5 init rest) (evalTree rest (fun w => initFun init (true :: w))) := rfl

/-- With a 5-entry `rest`, the lower half is INIT[31:0]: entry `addrOf w`. -/
theorem initFun_lower (init : Nat) (w : List Bool) :
    initFun init (false :: w) = init.testBit (addrOf w) := by
  simp [initFun, addrOf]

/-- Sanity: LUT2 AND (INIT = 0x8) on the K3 inputs (A2,A1). -/
example : evalTree [.one, .one] (initFun 8) = .one := by decide
example : evalTree [.X, .zero] (initFun 8) = .zero := by decide
example : evalTree [.X, .one] (initFun 8) = .X := by decide
/-- A C-element-like majority LUT3 holding 1 (INIT = 0xE8, feedback = A3):
with feedback 1 and a=1, b going X, the output stays 1. -/
example : evalTree [.one, .one, .X] (initFun 0xE8) = .one := by decide

end Formal.Core.LutTree
