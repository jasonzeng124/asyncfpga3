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

/-! ## Search trees keyed by strings -/

inductive STree (α : Type) where
  | nil
  | leaf (s : String) (v : α)
  | node (m : String) (l r : STree α)
  deriving Inhabited

def STree.find {α : Type} : STree α → String → Option α
  | .nil, _ => none
  | .leaf s v, t => if t = s then some v else none
  | .node m l r, t => if t < m then l.find t else r.find t

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
        subst hts
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
the leftover indices `L` are a permutation of `0 .. n-1`, where `n` is the number of target features. Then the
produced features plus the leftover features are exactly the target's features, each once. -/
theorem perm_of_idx (T : STree Nat) (hl : T.leaves.map Prod.snd = List.range T.leaves.length)
    (prod : List String) (L : List Nat)
    (hfind : ∀ f ∈ prod, (T.find f).isSome = true)
    (hperm : (prod.map (fun f => (T.find f).getD 0) ++ L).Perm (List.range T.leaves.length)) :
    (prod ++ L.map (fun j => (T.leaves.map Prod.fst).getD j "")).Perm (T.leaves.map Prod.fst) := by
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

end Formal.Target.RT
