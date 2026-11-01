import Formal.Target.Spec

/-!
# Formal.Target.RoundTrip — re-encode a Lean netlist as FASM features and compare (H_DECODE, S1)

Shard A, 2026-11-01. PROGRAM (H_DECODE): "re-encode the netlist back into FASM lines and compare with the
target, so that a decoder bug shows up". This file is the generic, target-independent part.

* `feats pre g` is the re-encoder: the FASM features gate `g` stands for, computed from the gate's own fields.
  A pip gate (one input, name not `~…` (implicit pip) and not `hop …` (site hop)) is its feature, the name
  `TILE.DST.SRC`. A LUT6 output `<site>.<L>LUT.O6` stands for one feature `<pre site>.<L>LUT.INIT[b]` per set bit
  `b` of its INIT (`pre` maps a site to its FASM prefix `TILE.SLICEx_Xn`, a prjxray table given as data).
* `STree` is a search tree of the target's features, leaf `(feature, index)`. `find_sound`: what it finds is
  there; nothing depends on the tree being ordered (an unordered tree only makes `find` fail).
* `msortF`/`mergeF`/`mergeAll`: fuel-bounded sorting on index lists, each a permutation of its input
  (`*_perm`); the kernel's job is to compute them and compare with `List.range n`.
* `perm_of_idx`: if every produced feature is found, and the found indices together with a list of leftover
  indices are a permutation of `range n`, then produced ++ leftovers is a permutation of the target's features.
-/

namespace Formal.Target.RT
open Formal.Target

/-! ## Strings as byte lists (cheap in the kernel; `String.<` and `String.decEq` decode characters) -/

def bl (s : String) : List UInt8 := s.toByteArray.data.toList

def eqB : List UInt8 → List UInt8 → Bool
  | [], [] => true
  | a :: as, b :: bs => a.toNat == b.toNat && eqB as bs
  | _, _ => false

def ltB : List UInt8 → List UInt8 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a.toNat < b.toNat then true else if a.toNat = b.toNat then ltB as bs else false

theorem eqB_sound : ∀ (a b : List UInt8), eqB a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [eqB] at h
  | _ :: _, [], h => by simp [eqB] at h
  | x :: as, y :: bs, h => by
    simp only [eqB, Bool.and_eq_true, beq_iff_eq] at h
    rw [UInt8.toNat_inj.1 h.1, eqB_sound as bs h.2]

theorem eq_of_bl {s t : String} (h : bl s = bl t) : s = t := by
  obtain ⟨x, hx⟩ := s
  obtain ⟨y, hy⟩ := t
  have : x = y := ByteArray.ext (Array.ext' h)
  subst this
  rfl

theorem eq_of_eqB {s t : String} (h : eqB (bl s) (bl t) = true) : s = t := eq_of_bl (eqB_sound _ _ h)

/-! ## Search trees keyed by strings -/

inductive STree (α : Type) where
  | nil
  | leaf (s : String) (v : α)
  | node (m : String) (l r : STree α)
  deriving Inhabited

def STree.find {α : Type} : STree α → String → Option α
  | .nil, _ => none
  | .leaf s v, t => if eqB (bl t) (bl s) then some v else none
  | .node m l r, t => if ltB (bl t) (bl m) then l.find t else r.find t

def STree.leaves {α : Type} : STree α → List (String × α)
  | .nil => []
  | .leaf s v => [(s, v)]
  | .node _ l r => l.leaves ++ r.leaves

theorem STree.find_sound {α : Type} : ∀ (T : STree α) (t : String) (v : α), T.find t = some v → (t, v) ∈ T.leaves
  | .nil, _, _, h => by simp [find] at h
  | .leaf s w, t, v, h => by
      simp only [find] at h
      split at h
      · rename_i hts
        have := eq_of_eqB hts
        subst this
        simp only [Option.some.injEq] at h
        subst h
        simp [leaves]
      · simp at h
  | .node m l r, t, v, h => by
      simp only [find] at h
      simp only [leaves, List.mem_append]
      split at h
      · exact Or.inl (find_sound l t v h)
      · exact Or.inr (find_sound r t v h)

/-- In a leaf list indexed `0, 1, ..`, a leaf `(t, j)` is the `j`-th feature. -/
theorem getD_of_mem_idx {l : List (String × Nat)} (hl : l.map Prod.snd = List.range l.length) {t : String}
    {j : Nat} (h : (t, j) ∈ l) : (l.map Prod.fst).getD j "" = t := by
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem h
  have h1 : (l.map Prod.snd)[i]? = some j := by
    rw [List.getElem?_map, List.getElem?_eq_getElem hi, he]; rfl
  rw [hl, List.getElem?_range hi] at h1
  have hij : i = j := Option.some.inj h1
  subst hij
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi, he]; rfl

/-! ## Sorting with fuel (permutations whatever the fuel) -/

def mergeF : Nat → List Nat → List Nat → List Nat
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, x :: xs, [] => x :: xs
  | f + 1, x :: xs, y :: ys => if x ≤ y then x :: mergeF f xs (y :: ys) else y :: mergeF f (x :: xs) ys

theorem mergeF_perm : ∀ (f : Nat) (xs ys : List Nat), (mergeF f xs ys).Perm (xs ++ ys)
  | 0, xs, ys => by simp only [mergeF]; exact List.Perm.refl _
  | _ + 1, [], ys => by simp only [mergeF, List.nil_append]; exact List.Perm.refl _
  | _ + 1, x :: xs, [] => by simp only [mergeF, List.append_nil]; exact List.Perm.refl _
  | f + 1, x :: xs, y :: ys => by
    simp only [mergeF]
    split
    · exact (mergeF_perm f xs (y :: ys)).cons x
    · exact ((mergeF_perm f (x :: xs) ys).cons y).trans List.perm_middle.symm

def splitAlt : List Nat → List Nat × List Nat
  | [] => ([], [])
  | [a] => ([a], [])
  | a :: b :: l => ((a :: (splitAlt l).1), (b :: (splitAlt l).2))

theorem splitAlt_perm : ∀ l : List Nat, ((splitAlt l).1 ++ (splitAlt l).2).Perm l
  | [] => List.Perm.refl _
  | [a] => List.Perm.refl _
  | a :: b :: l => by
    simp only [splitAlt, List.cons_append]
    exact ((List.perm_middle).trans ((splitAlt_perm l).cons b)).cons a

def msortF : Nat → List Nat → List Nat
  | 0, l => l
  | _ + 1, [] => []
  | _ + 1, [a] => [a]
  | f + 1, a :: b :: l =>
    mergeF (l.length + 2) (msortF f (splitAlt (a :: b :: l)).1) (msortF f (splitAlt (a :: b :: l)).2)

theorem msortF_perm : ∀ (f : Nat) (l : List Nat), (msortF f l).Perm l
  | 0, l => by simp only [msortF]; exact List.Perm.refl _
  | _ + 1, [] => List.Perm.refl _
  | _ + 1, [a] => List.Perm.refl _
  | f + 1, a :: b :: l => by
    simp only [msortF]
    exact (mergeF_perm _ _ _).trans
      (((msortF_perm f _).append (msortF_perm f _)).trans (splitAlt_perm _))

def mergePairs (f : Nat) : List (List Nat) → List (List Nat)
  | a :: b :: r => mergeF f a b :: mergePairs f r
  | l => l

theorem mergePairs_perm (f : Nat) : ∀ ls : List (List Nat), (mergePairs f ls).flatten.Perm ls.flatten
  | [] => List.Perm.refl _
  | [a] => List.Perm.refl _
  | a :: b :: r => by
    simp only [mergePairs, List.flatten_cons, ← List.append_assoc]
    exact (mergeF_perm f a b).append (mergePairs_perm f r)

def mergeAll (f : Nat) : Nat → List (List Nat) → List Nat
  | 0, ls => ls.flatten
  | _ + 1, [] => []
  | _ + 1, [a] => a
  | g + 1, a :: b :: r => mergeAll f g (mergePairs f (a :: b :: r))

theorem mergeAll_perm (f : Nat) : ∀ (g : Nat) (ls : List (List Nat)), (mergeAll f g ls).Perm ls.flatten
  | 0, ls => by simp only [mergeAll]; exact List.Perm.refl _
  | _ + 1, [] => List.Perm.refl _
  | _ + 1, [a] => by simp only [mergeAll, List.flatten_cons, List.flatten_nil, List.append_nil]; exact List.Perm.refl _
  | g + 1, a :: b :: r => by
    simp only [mergeAll]
    exact (mergeAll_perm f g _).trans (mergePairs_perm f _)

/-! ## The re-encoder -/

/-- The set bits of a LUT6 INIT, low to high. -/
def lutBits (init : Nat) : List Nat := (List.range 64).filter fun b => init.testBit b

/-- **The FASM features gate `g` stands for** (pips and LUT6 INIT bits; every other gate: none). -/
def feats (pre : String → String) (g : Gate) : List String :=
  if g.k = 1 ∧ g.name.front ≠ '~' ∧ g.name.startsWith "hop " = false then [g.name]
  else if g.k = 6 ∧ g.name.endsWith ".O6" = true then
    match g.name.splitOn "." with
    | [site, lut, _] => (lutBits g.init).map fun b => pre site ++ "." ++ lut ++ ".INIT[" ++ toString b ++ "]"
    | _ => []
  else []

/-! ## The comparison -/

theorem map_getD_range (l : List String) : (List.range l.length).map (fun j => l.getD j "") = l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- **The round trip.** `prod` (the produced features) are all found in `T` at indices `idx`; those indices and
the leftover indices `L` are a permutation of `0 .. n-1`, where the leaves of `T` are indexed `0 .. n-1`. Then the
produced features plus the leftover features are exactly the target's features, each once. -/
theorem perm_of_idx (T : STree Nat) (n : Nat) (hl : T.leaves.map Prod.snd = List.range n)
    (prod : List String) (L : List Nat)
    (hfind : ∀ f ∈ prod, (T.find f).isSome = true)
    (hperm : (prod.map (fun f => (T.find f).getD 0) ++ L).Perm (List.range n)) :
    (prod ++ L.map (fun j => (T.leaves.map Prod.fst).getD j "")).Perm (T.leaves.map Prod.fst) := by
  have hn : n = T.leaves.length := by simpa using (congrArg List.length hl).symm
  subst hn
  set tf := T.leaves.map Prod.fst with htf
  have hlen : tf.length = T.leaves.length := by simp [htf]
  have hp : prod.map (fun f => tf.getD ((T.find f).getD 0) "") = prod := by
    conv => rhs; rw [← List.map_id prod]
    apply List.map_congr_left
    intro f hf
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hfind f hf)
    rw [hv, Option.getD_some]
    exact getD_of_mem_idx hl (STree.find_sound T f v hv)
  have := (hperm.map (fun j => tf.getD j ""))
  rw [List.map_append, List.map_map] at this
  rw [← hlen, map_getD_range] at this
  rw [← hp]
  simpa [Function.comp_def] using this

/-! ## Checking a permutation of `0 .. n-1` block by block

The kernel cannot merge 355k indices in one declaration. Index lists are cut into blocks of consecutive
indices (`blocks`); `rows` holds, per producer (gate chunk, leftovers), its indices cut by block; each block is
merged and compared on its own (`hb`); `perm_blocks` reassembles. -/

/-- Consecutive index blocks of lengths `ns` from `s`. -/
def blocks : Nat → List Nat → List (List Nat)
  | _, [] => []
  | s, n :: ns => List.range' s n :: blocks (s + n) ns

theorem blocks_length : ∀ (s : Nat) (ns : List Nat), (blocks s ns).length = ns.length
  | _, [] => rfl
  | s, _ :: ns => by simp only [blocks, List.length_cons, blocks_length _ ns]

theorem blocks_flatten : ∀ (s : Nat) (ns : List Nat), (blocks s ns).flatten = List.range' s ns.sum
  | _, [] => rfl
  | s, n :: ns => by
    simp only [blocks, List.flatten_cons, blocks_flatten (s + n) ns, List.sum_cons]
    exact List.range'_append_1

theorem flatMap_append_perm {α β : Type} (l : List α) (f g : α → List β) :
    (l.flatMap fun a => f a ++ g a).Perm (l.flatMap f ++ l.flatMap g) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons a l ih =>
    simp only [List.flatMap_cons, List.append_assoc]
    refine List.Perm.append_left (f a) ?_
    refine (List.Perm.append_left (g a) ih).trans ?_
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm

theorem flatMap_perm {α β : Type} (l : List α) {f g : α → List β} (h : ∀ a ∈ l, (f a).Perm (g a)) :
    (l.flatMap f).Perm (l.flatMap g) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons a l ih =>
    simp only [List.flatMap_cons]
    exact (h a List.mem_cons_self).append (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem transpose_perm (u : Nat → Nat → List Nat) (K : Nat) : ∀ C : Nat,
    ((List.range C).flatMap fun c => (List.range K).flatMap fun k => u c k).Perm
      ((List.range K).flatMap fun k => (List.range C).flatMap fun c => u c k)
  | 0 => by simp only [List.range_zero, List.flatMap_nil]; exact (List.Perm.refl _).trans (by
      rw [show ((List.range K).flatMap fun _ => ([] : List Nat)) = [] by
        induction (List.range K) with
        | nil => rfl
        | cons _ _ ih => simp [ih]])
  | C + 1 => by
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact ((transpose_perm u K C).append (List.Perm.refl _)).trans (flatMap_append_perm _ _ _).symm

theorem map_getD_range' {α : Type} (l : List α) (d : α) : (List.range l.length).map (fun i => l.getD i d) = l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem flatMap_getD (l : List (List Nat)) : ((List.range l.length).flatMap fun i => l.getD i []) = l.flatten := by
  rw [List.flatMap_def, map_getD_range']

theorem getD_mem' {α : Type} (l : List α) (d : α) {i : Nat} (hi : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact List.getElem_mem hi

/-- **Block-wise permutation check.** Every row (producer) has one index list per block; block `k`'s lists,
merged, are the `k`-th block. Then all rows together are a permutation of `range' 0 (sum ns)`. -/
theorem perm_blocks (F G : Nat) (rows : List (List (List Nat))) (ns : List Nat)
    (hrow : ∀ r ∈ rows, r.length = ns.length)
    (hb : ∀ k, k < ns.length →
      mergeAll F G ((List.range rows.length).map fun c => (rows.getD c []).getD k []) = (blocks 0 ns).getD k []) :
    (rows.map List.flatten).flatten.Perm (List.range' 0 ns.sum) := by
  have e1 : (rows.map List.flatten).flatten = (List.range rows.length).flatMap fun c => (rows.getD c []).flatten := by
    conv_lhs => rw [← map_getD_range' rows []]
    rw [List.map_map, List.flatMap_def]; rfl
  rw [e1]
  refine (flatMap_perm _ (g := fun c => (List.range ns.length).flatMap fun k => (rows.getD c []).getD k [])
    fun c hc => ?_).trans ?_
  · have hm := getD_mem' rows [] (List.mem_range.1 hc)
    rw [← hrow _ hm, flatMap_getD]
  refine (transpose_perm _ _ _).trans ?_
  refine (flatMap_perm _ (g := fun k => (blocks 0 ns).getD k []) fun k hk => ?_).trans ?_
  · rw [← hb k (List.mem_range.1 hk), List.flatMap_def]
    exact (mergeAll_perm _ _ _).symm
  · rw [show ns.length = (blocks 0 ns).length from (blocks_length 0 ns).symm, flatMap_getD, blocks_flatten]

/-! ## Index-keyed feature trees and index certificates

Comparing strings by order in the kernel is expensive (it decodes both); comparing them for equality is cheap.
So every produced feature comes with its index in the target list as certificate data, the kernel finds the
leaf by that (Nat) index and checks only string equality (`chkI`). -/

inductive ITree where
  | nil
  | leaf (s : String) (j : Nat)
  | node (m : Nat) (l r : ITree)
  deriving Inhabited

def ITree.get : ITree → Nat → Option String
  | .nil, _ => none
  | .leaf s j, i => if i = j then some s else none
  | .node m l r, i => if i < m then l.get i else r.get i

def ITree.leaves : ITree → List (String × Nat)
  | .nil => []
  | .leaf s j => [(s, j)]
  | .node _ l r => l.leaves ++ r.leaves

theorem ITree.get_sound : ∀ (T : ITree) (i : Nat) (s : String), T.get i = some s → (s, i) ∈ T.leaves
  | .nil, _, _, h => by simp [get] at h
  | .leaf w j, i, s, h => by
      simp only [get] at h
      split at h
      · rename_i hij
        subst hij
        simp only [Option.some.injEq] at h
        subst h
        simp [leaves]
      · simp at h
  | .node m l r, i, s, h => by
      simp only [get] at h
      simp only [leaves, List.mem_append]
      split at h
      · exact Or.inl (get_sound l i s h)
      · exact Or.inr (get_sound r i s h)

/-- Each feature `fs[k]` is the target feature at index `js[k]`. -/
def chkI (T : ITree) : List String → List Nat → Bool
  | [], [] => true
  | f :: fs, j :: js => (match T.get j with | some s => eqB (bl s) (bl f) | none => false) && chkI T fs js
  | _, _ => false

theorem chkI_sound (T : ITree) {n : Nat} (hl : T.leaves.map Prod.snd = List.range n) :
    ∀ (fs : List String) (js : List Nat), chkI T fs js = true →
      fs = js.map (fun j => (T.leaves.map Prod.fst).getD j "")
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [chkI] at h
  | _ :: _, [], h => by simp [chkI] at h
  | f :: fs, j :: js, h => by
    simp only [chkI, Bool.and_eq_true] at h
    have hn : n = T.leaves.length := by simpa using (congrArg List.length hl).symm
    subst hn
    obtain ⟨h1, h2⟩ := h
    split at h1
    · rename_i s hs
      have := eq_of_eqB h1
      subst this
      rw [List.map_cons, chkI_sound T hl fs js h2, getD_of_mem_idx hl (ITree.get_sound T j s hs)]
    · simp at h1

theorem fm_drop_take {α β : Type} (F : α → List β) (l : List α) (a n : Nat) {x y : List β}
    (h1 : ((l.drop a).take n).flatMap F = x) (h2 : (l.drop (a + n)).flatMap F = y) :
    (l.drop a).flatMap F = x ++ y := by
  rw [← h1, ← h2, ← List.flatMap_append, ← List.drop_drop, List.take_append_drop]

theorem fm_drop_len {α β : Type} (F : α → List β) (l : List α) (a : Nat) (h : l.length ≤ a) :
    (l.drop a).flatMap F = [] := by
  rw [List.drop_eq_nil_of_le h]; rfl

theorem perm_map_getD (tf : List String) (I : List Nat) (h : I.Perm (List.range tf.length)) :
    (I.map fun j => tf.getD j "").Perm tf := by
  have := h.map (fun j => tf.getD j "")
  rwa [map_getD_range] at this

end Formal.Target.RT
