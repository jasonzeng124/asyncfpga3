import Formal.Core.Kleene
import Formal.Core.Lut
import Formal.Core.LutTree
import Formal.Core.Ternary
import Formal.Core.LutList

/-!
# Formal.Core.Bridge — one Kleene LUT, four encodings

Shard A, probe "bridge". Core Lean only. Nothing upstream is edited: this file
only imports the committed modules and proves that their independent copies
of `K3` and of Kleene LUT evaluation are the same thing.

Canonical API (going forward): `Formal.Core.K3` (Kleene.lean) and
`Formal.Core.Lut` (`Lut k`, `Lut.eval`, `Lut.keval`, `Lut.kevalSpec`).
`Formal.Core.LutTree` and `Formal.Core.Ternary` keep their own `K3`;
`Formal.Core.LutList` (the list view that shard B's `Formal.Cells.Prelim`
used to provide, same names and bodies; `K3` there is Core's `K3`, so its
map below is the identity); they are reached through the maps below.

## 1. The four `K3`s (§1)

| module | type | constructors | glb / X-select mux |
|---|---|---|---|
| Kleene (canonical) | `Formal.Core.K3` | `zero one X` | `K3.merge`; mux `cmux` (defined here) |
| LutTree | `Formal.Core.LutTree.K3` | `zero one X` | `LutTree.kmux` |
| Ternary | `Formal.Core.Ternary.K3` | `zero one X` | `K3.meet`, `K3.sel` |
| LutList (ex Cells.Prelim) | `Formal.Core.LutList.K3` | `f t x` | `K3.join`, `K3.mux` |

For each: `toX : Core.K3 → _`, `ofX`, both inverse laws (packaged as a
`K3Iso`), preservation of `ofBool`, of the information order (Prelim has none:
it uses `admits`, which is preserved instead), of the glb and of the Kleene mux.

## 2. LUT evaluation agrees (§2)

Pin and INIT conventions. A Core `Lut k` holds `init : BitVec (2^k)`; the
Boolean input vector is `x : Fin k → Bool`, `x 0` = pin `I0` = LSB of the
address, `INIT[Σ x_i 2^i]` (`Formal.Core.addr`). The corresponding data in the
other encodings:

* table as a natural number: `N := L.init.toNat`; `L.entry a = N.testBit a`
  (`entry_eq_testBit`).
* Ternary: `kext k f` with `f = Ternary.initTbl N` (`I0` = LSB, `Ternary.addr`
  is the same function as `Core.addr`, `tern_addr_eq`). The Kleene vector is
  the same `Fin k` tuple mapped by `toTern`.
* LutTree: lists are ROOT FIRST. Two readings are related:
  - `lsbList v := List.ofFn (toLT ∘ v)` = `[I0, …, I(k-1)]` with the table
    `fun w => t (lsbAddr w)` (LSB-first address): this is literally the
    same tree as Core's `kevalT` (I0 at the root, as the research GLS);
  - `silList v := (lsbList v).reverse` = `[I(k-1), …, I0]` = `[A6, …, A1]`
    with LutTree's own `initFun N` (MSB-first `addrOf`): the silicon order,
    A6 at the root. For a LUT6, `LutTree.lut6O6 N (v 5) [v 4, …, v 0]` is
    exactly this.
* LutList (ex Cells.Prelim): lists `[I0, …, I(k-1)]` (`List.ofFn (toCells ∘ v)`), the
  table `N`, `lutIdx` = LSB-first.

Theorems (all for every `k`, every INIT, every `K3` vector):

* `tern_kext_eq_keval`   `kext k (initTbl N) (toTern ∘ v) = toTern (L.keval v)`
* `lt_evalTree_lsb_eq_keval`   GLS-order tree = Core
* `lt_evalTree_sil_eq_keval`, `lt_tableEval_sil_eq_kevalSpec`   silicon-order
  tree and LutTree's table semantics = Core
* `cells_muxTree_eq_keval`, `cells_lutK_eq_keval`   shard B's tree / closure = Core
* `lt_lut6O6_eq_keval`, `lt_lut6O5_eq_keval`   LutTree's LUT6_2 O6 / O5 =
  Core `keval` / `Lut62.o5.keval`
* Boolean: `tern_initTbl_eq_eval`, `cells_lutB_eq_eval`, `lsbAddr_ofFn`,
  `addrOf_eq_lsbAddr_reverse`, `tern_addr_eq`.

## 3. Transfer (§3)

* `phys_glitch_free_of_core`: the timed physical tree of LutTree, wired to
  a Core LUT in silicon order: any Core fact `L.keval v = ofBool c` gives
  "output is `c` at every instant, any delays" under LutTree's hypotheses
  `H_sram`, `H_mux_kleene`.
* `phys_sic_of_core`: same with Core's `no_static_hazard_single` discharging
  the INIT condition: a single pin flip with equal Boolean ends never glitches.
* `phys_hull_of_core`: any set of pins moving, subcube condition from Core's
  `keval_hull_eq_ofBool_iff`.
* `phys_bd_c2_contain`: the C-element's X containment (`Init.bd_c2_contain`)
  in the physical tree.
* `tern_bdc2_F_eq_core`: Ternary's `bdc2Net` (LUT4 `0x00E8`) IS
  `Core.Init.bd_c2` (LUT6, `I4 = I5 = 0`) in Kleene semantics, for every
  ternary input and state; `tern_bdc2_fb_eq_core` for the Boolean function;
  `core_bdc2_no_static_hazard` is Ternary's `bdc2_no_static_hazard` with its
  stability hypothesis stated on `Core.Init.bd_c2.eval`.
-/

namespace Formal.Core.Bridge

/-- Canonical Kleene value. -/
abbrev CK := Formal.Core.K3
/-- LutTree's local copy. -/
abbrev LK := Formal.Core.LutTree.K3
/-- Ternary's local copy. -/
abbrev TK := Formal.Core.Ternary.K3
/-- The list view's name (`Formal.Core.LutList.K3`, an abbrev of Core's `K3`;
formerly shard B's `Formal.Cells.K3`). -/
abbrev BK := Formal.Core.LutList.K3

/-- An explicit bijection between the canonical `K3` and a local copy. -/
structure K3Iso (α : Type) where
  toFun : CK → α
  invFun : α → CK
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

/-- The Kleene 2:1 mux on the canonical `K3` (select 0 → `a`, 1 → `b`,
X → glb). This is the mux that `Formal.Core.kevalT` inlines. -/
def cmux : CK → CK → CK → CK
  | .zero, a, _ => a
  | .one, _, b => b
  | .X, a, b => K3.merge a b

theorem kevalT_succ {k : Nat} (t : Nat → Bool) (v : Fin (k + 1) → CK) :
    kevalT (k + 1) t v =
      cmux (v 0) (kevalT k (fun a => t (2 * a)) (vtail v))
                 (kevalT k (fun a => t (2 * a + 1)) (vtail v)) := by
  simp only [kevalT]
  cases v 0 <;> rfl

/-! ## 1. The maps -/

section LT
open Formal.Core.LutTree

def toLT : CK → LK
  | .zero => .zero
  | .one => .one
  | .X => .X

def ofLT : LK → CK
  | .zero => .zero
  | .one => .one
  | .X => .X

theorem ofLT_toLT (a : CK) : ofLT (toLT a) = a := by cases a <;> rfl
theorem toLT_ofLT (a : LK) : toLT (ofLT a) = a := by cases a <;> rfl

def isoLT : K3Iso LK := ⟨toLT, ofLT, ofLT_toLT, toLT_ofLT⟩

@[simp] theorem toLT_ofBool (b : Bool) : toLT (K3.ofBool b) = LutTree.K3.ofBool b := by
  cases b <;> rfl

theorem toLT_le_iff (a b : CK) : LutTree.K3.Le (toLT a) (toLT b) ↔ K3.Le a b := by
  cases a <;> cases b <;> decide

theorem toLT_merge (a b : CK) : toLT (K3.merge a b) = kmux .X (toLT a) (toLT b) := by
  cases a <;> cases b <;> rfl

theorem toLT_cmux (s a b : CK) : toLT (cmux s a b) = kmux (toLT s) (toLT a) (toLT b) := by
  cases s <;> cases a <;> cases b <;> rfl

end LT

section Tern
open Formal.Core.Ternary

def toTern : CK → TK
  | .zero => .zero
  | .one => .one
  | .X => .X

def ofTern : TK → CK
  | .zero => .zero
  | .one => .one
  | .X => .X

theorem ofTern_toTern (a : CK) : ofTern (toTern a) = a := by cases a <;> rfl
theorem toTern_ofTern (a : TK) : toTern (ofTern a) = a := by cases a <;> rfl

def isoTern : K3Iso TK := ⟨toTern, ofTern, ofTern_toTern, toTern_ofTern⟩

@[simp] theorem toTern_ofBool (b : Bool) : toTern (K3.ofBool b) = Ternary.K3.ofBool b := by
  cases b <;> rfl

theorem toTern_le_iff (a b : CK) : Ternary.K3.Le (toTern a) (toTern b) ↔ K3.Le a b := by
  cases a <;> cases b <;> decide

theorem toTern_merge (a b : CK) : toTern (K3.merge a b) = Ternary.K3.meet (toTern a) (toTern b) := by
  cases a <;> cases b <;> rfl

theorem toTern_cmux (s a b : CK) :
    toTern (cmux s a b) = Ternary.K3.sel (toTern s) (toTern a) (toTern b) := by
  cases s <;> cases a <;> cases b <;> rfl

end Tern

section Cells

def toCells : CK → BK
  | .zero => .f
  | .one => .t
  | .X => .x

def ofCells : BK → CK
  | .f => .zero
  | .t => .one
  | .x => .X

theorem ofCells_toCells (a : CK) : ofCells (toCells a) = a := by cases a <;> rfl
theorem toCells_ofCells (a : BK) : toCells (ofCells a) = a := by cases a <;> rfl

def isoCells : K3Iso BK := ⟨toCells, ofCells, ofCells_toCells, toCells_ofCells⟩

@[simp] theorem toCells_ofBool (b : Bool) : toCells (K3.ofBool b) = Formal.Core.LutList.K3.ofBool b := by
  cases b <;> rfl

/-- Prelim has no information order; its `admits a b` is "`b` is a Boolean
refinement of `a`", i.e. Core's `a ⊑ ofBool b`. -/
theorem toCells_admits (a : CK) (b : Bool) :
    Formal.Core.LutList.K3.admits (toCells a) b = true ↔ K3.Le a (K3.ofBool b) := by
  cases a <;> cases b <;> decide

theorem toCells_merge (a b : CK) : toCells (K3.merge a b) = Formal.Core.LutList.K3.join (toCells a) (toCells b) := by
  cases a <;> cases b <;> rfl

theorem toCells_cmux (s a b : CK) :
    toCells (cmux s a b) = Formal.Core.LutList.K3.mux (toCells s) (toCells a) (toCells b) := by
  cases s <;> cases a <;> cases b <;> rfl

theorem toCells_not (a : CK) : toCells (K3.not a) = Formal.Core.LutList.K3.not (toCells a) := by
  cases a <;> rfl

end Cells

/-! ## 2. LUT evaluations agree -/

/-- INIT entry `a` of a Core LUT is bit `a` of the INIT as a natural number. -/
theorem entry_eq_testBit {k : Nat} (L : Lut k) (a : Nat) : L.entry a = L.init.toNat.testBit a :=
  rfl

/-! ### Ternary.kext -/

theorem tern_addr_eq : ∀ {k : Nat} (x : Fin k → Bool), Ternary.addr x = Formal.Core.addr x
  | 0, _ => rfl
  | k + 1, x => by
      show (x 0).toNat + 2 * Ternary.addr (Ternary.vtail x) = (x 0).toNat + 2 * addr (vtail x)
      rw [tern_addr_eq]; rfl

/-- **Ternary's mux tree is Core's**, for any table indexed by the
LSB-first address. -/
theorem tern_kext_eq_kevalT : ∀ (k : Nat) (t : Nat → Bool) (v : Fin k → CK),
    Ternary.kext k (fun x => t (Ternary.addr x)) (fun i => toTern (v i)) = toTern (kevalT k t v)
  | 0, t, v => by simp [Ternary.kext, kevalT, Ternary.addr]
  | k + 1, t, v => by
      rw [kevalT_succ, toTern_cmux, ← tern_kext_eq_kevalT k, ← tern_kext_eq_kevalT k]
      simp only [Ternary.kext]
      congr 2
      · funext y; congr 1
        show (false.toNat + 2 * Ternary.addr y) = 2 * Ternary.addr y
        simp
      · funext y; congr 1
        show (true.toNat + 2 * Ternary.addr y) = 2 * Ternary.addr y + 1
        simp [Nat.add_comm]

/-- **Ternary.kext on a LUT table = Core `keval`.** -/
theorem tern_kext_eq_keval {k : Nat} (L : Lut k) (v : Fin k → CK) :
    Ternary.kext k (Ternary.initTbl L.init.toNat) (fun i => toTern (v i)) = toTern (L.keval v) :=
  tern_kext_eq_kevalT k L.entry v

theorem tern_kext_eq_kevalSpec {k : Nat} (L : Lut k) (v : Fin k → CK) :
    Ternary.kext k (Ternary.initTbl L.init.toNat) (fun i => toTern (v i)) = toTern (L.kevalSpec v) := by
  rw [tern_kext_eq_keval, Lut.keval_eq_kevalSpec]

/-- And on Boolean tables: Ternary's Boolean LUT is Core's `eval`. -/
theorem tern_initTbl_eq_eval {k : Nat} (L : Lut k) (x : Fin k → Bool) :
    Ternary.initTbl L.init.toNat x = L.eval x := by
  simp [Ternary.initTbl, Lut.eval, tern_addr_eq, entry_eq_testBit]

/-! ### LutTree.evalTree, GLS order (I0 at the root) -/

/-- LSB-first address of a list `[I0, I1, …]` (= shard B's `lutIdx`). -/
def lsbAddr : List Bool → Nat
  | [] => 0
  | b :: w => b.toNat + 2 * lsbAddr w

theorem lsbAddr_eq_lutIdx : ∀ w : List Bool, lsbAddr w = Formal.Core.LutList.lutIdx w
  | [] => rfl
  | b :: w => by cases b <;> simp [lsbAddr, Formal.Core.LutList.lutIdx, lsbAddr_eq_lutIdx w]

theorem lsbAddr_ofFn : ∀ {k : Nat} (x : Fin k → Bool), lsbAddr (List.ofFn x) = addr x
  | 0, _ => rfl
  | k + 1, x => by
      rw [List.ofFn_succ]
      show (x 0).toNat + 2 * lsbAddr (List.ofFn (vtail x)) = _
      rw [lsbAddr_ofFn]; rfl

/-- Kleene vector as a LutTree list, `[I0, …, I(k-1)]`. -/
def lsbList {k : Nat} (v : Fin k → CK) : List LK := List.ofFn (fun i => toLT (v i))

/-- Kleene vector as a LutTree list in silicon order, `[I(k-1), …, I0]`
(= `[A6, …, A1]` for a LUT6). -/
def silList {k : Nat} (v : Fin k → CK) : List LK := (lsbList v).reverse

/-- Every LutTree input list is the `lsbList` of a Core vector, so the theorems
below cover every LutTree list of length `k` (and, reversed, `silList`). -/
theorem lsbList_surj (l : List LK) : lsbList (fun i : Fin l.length => ofLT l[i]) = l := by
  simp [lsbList, toLT_ofLT]

theorem silList_surj (l : List LK) :
    silList (fun i : Fin l.reverse.length => ofLT l.reverse[i]) = l := by
  simp only [silList, lsbList_surj, List.reverse_reverse]

theorem lsbList_length {k : Nat} (v : Fin k → CK) : (lsbList v).length = k := by
  simp [lsbList]

theorem silList_length {k : Nat} (v : Fin k → CK) : (silList v).length = k := by
  simp [silList, lsbList_length]

theorem lt_evalTree_lsb_eq_kevalT : ∀ (k : Nat) (t : Nat → Bool) (v : Fin k → CK),
    LutTree.evalTree (lsbList v) (fun w => t (lsbAddr w)) = toLT (kevalT k t v)
  | 0, t, v => by simp [lsbList, LutTree.evalTree, kevalT, lsbAddr]
  | k + 1, t, v => by
      rw [kevalT_succ, toLT_cmux, ← lt_evalTree_lsb_eq_kevalT k, ← lt_evalTree_lsb_eq_kevalT k]
      simp only [lsbList, List.ofFn_succ, LutTree.evalTree]
      congr 2
      · funext w; simp [lsbAddr]
      · funext w; simp [lsbAddr, Nat.add_comm]

/-- **LutTree's mux tree in GLS order (I0 at the root) = Core `keval`.** -/
theorem lt_evalTree_lsb_eq_keval {k : Nat} (L : Lut k) (v : Fin k → CK) :
    LutTree.evalTree (lsbList v) (fun w => L.init.toNat.testBit (lsbAddr w)) = toLT (L.keval v) :=
  lt_evalTree_lsb_eq_kevalT k L.entry v

/-! ### LutTree, silicon order (A6 = I(k-1) at the root), via `tableEval` -/

section Rev
open Formal.Core.LutTree

theorem consistent_length : ∀ (v : List LK) (w : List Bool),
    LutTree.Consistent v w → v.length = w.length
  | [], [], _ => rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: v, _ :: w, h => by simp [consistent_length v w h.2]

theorem consistent_append : ∀ (v1 v2 : List LK) (w1 w2 : List Bool), v1.length = w1.length →
    (LutTree.Consistent (v1 ++ v2) (w1 ++ w2) ↔ LutTree.Consistent v1 w1 ∧ LutTree.Consistent v2 w2)
  | [], _, [], _, _ => by simp [LutTree.Consistent]
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h
  | a :: v1, v2, b :: w1, w2, h => by
      simp only [List.cons_append, LutTree.Consistent]
      rw [consistent_append v1 v2 w1 w2 (by simpa using h)]
      exact ⟨fun ⟨x, y, z⟩ => ⟨⟨x, y⟩, z⟩, fun ⟨⟨x, y⟩, z⟩ => ⟨x, y, z⟩⟩

theorem consistent_reverse_reverse : ∀ (v : List LK) (u : List Bool),
    LutTree.Consistent v.reverse u.reverse ↔ LutTree.Consistent v u
  | [], [] => Iff.rfl
  | [], b :: u => by
      simp only [List.reverse_nil, List.reverse_cons]
      constructor
      · intro h; have := consistent_length _ _ h; simp at this
      · intro h; exact h.elim
  | a :: v, [] => by
      simp only [List.reverse_nil, List.reverse_cons]
      constructor
      · intro h; have := consistent_length _ _ h; simp at this
      · intro h; exact h.elim
  | a :: v, b :: u => by
      simp only [List.reverse_cons]
      by_cases hl : v.length = u.length
      · rw [consistent_append _ _ _ _ (by simpa using hl), consistent_reverse_reverse v u]
        simp only [LutTree.Consistent, and_true]
        exact ⟨fun ⟨x, y⟩ => ⟨y, x⟩, fun ⟨x, y⟩ => ⟨y, x⟩⟩
      · constructor
        · intro h; have := consistent_length _ _ h; simp at this; omega
        · intro h; have := consistent_length _ _ h; simp at this; omega

theorem consistent_reverse (v : List LK) (w : List Bool) :
    LutTree.Consistent v.reverse w ↔ LutTree.Consistent v w.reverse := by
  have := consistent_reverse_reverse v w.reverse
  rwa [List.reverse_reverse] at this

/-- A `tableEval` value is determined by its two "all entries are b" facts. -/
theorem tableEval_ext (v v' : List LK) (g g' : List Bool → Bool)
    (h : ∀ b : Bool, (∀ w, LutTree.Consistent v w → g w = b) ↔
                     (∀ w, LutTree.Consistent v' w → g' w = b)) :
    tableEval v g = tableEval v' g' := by
  have h1 := (tableEval_eq_one_iff v g).trans ((h true).trans (tableEval_eq_one_iff v' g').symm)
  have h0 := (tableEval_eq_zero_iff v g).trans ((h false).trans (tableEval_eq_zero_iff v' g').symm)
  revert h1 h0
  cases tableEval v g <;> cases tableEval v' g' <;> simp

theorem tableEval_reverse (v : List LK) (g : List Bool → Bool) :
    tableEval v.reverse (fun w => g w.reverse) = tableEval v g := by
  apply tableEval_ext
  intro b
  constructor
  · intro h u hu
    have := h u.reverse ((consistent_reverse v u.reverse).2 (by rwa [List.reverse_reverse]))
    rwa [List.reverse_reverse] at this
  · intro h w hw
    exact h _ ((consistent_reverse v w).1 hw)

theorem lsbAddr_append (l : List Bool) (b : Bool) :
    lsbAddr (l ++ [b]) = lsbAddr l + 2 ^ l.length * b.toNat := by
  induction l with
  | nil => simp [lsbAddr]
  | cons c l ih =>
      simp only [List.cons_append, lsbAddr, ih, List.length_cons, Nat.pow_succ]
      generalize 2 ^ l.length = p
      cases b <;> simp <;> rw [Nat.mul_add] <;> simp [Nat.mul_comm, Nat.add_assoc]

/-- LutTree's MSB-first address is the LSB-first address of the reversed list. -/
theorem addrOf_eq_lsbAddr_reverse : ∀ w : List Bool, addrOf w = lsbAddr w.reverse
  | [] => rfl
  | b :: w => by
      rw [List.reverse_cons, lsbAddr_append, ← addrOf_eq_lsbAddr_reverse w, List.length_reverse]
      cases b <;> simp [addrOf, Nat.add_comm]

end Rev

/-- **LutTree in silicon order with its own `initFun` = Core `keval`.** -/
theorem lt_evalTree_sil_eq_keval {k : Nat} (L : Lut k) (v : Fin k → CK) :
    LutTree.evalTree (silList v) (LutTree.initFun L.init.toNat) = toLT (L.keval v) := by
  rw [← lt_evalTree_lsb_eq_keval, LutTree.evalTree_eq_tableEval, LutTree.evalTree_eq_tableEval,
    silList, ← tableEval_reverse (lsbList v)]
  congr 1
  funext w
  simp [LutTree.initFun, addrOf_eq_lsbAddr_reverse]

/-- The same in LutTree's table semantics, against Core's specification. -/
theorem lt_tableEval_sil_eq_kevalSpec {k : Nat} (L : Lut k) (v : Fin k → CK) :
    LutTree.tableEval (silList v) (LutTree.initFun L.init.toNat) = toLT (L.kevalSpec v) := by
  rw [← LutTree.evalTree_eq_tableEval, lt_evalTree_sil_eq_keval, Lut.keval_eq_kevalSpec]

/-- LutTree's LUT6 `O6` (A6 = `v 5` at the root) is Core's `keval`. -/
theorem lt_lut6O6_eq_keval (L : Lut 6) (v : Fin 6 → CK) :
    LutTree.lut6O6 L.init.toNat (toLT (v 5)) [toLT (v 4), toLT (v 3), toLT (v 2), toLT (v 1), toLT (v 0)]
      = toLT (L.keval v) := by
  rw [← lt_evalTree_sil_eq_keval]; rfl

/-! ### The list view `Formal.Core.LutList` (ex `Cells.Prelim`; `muxTree`, `lutK`) -/

theorem cells_muxTree_eq_kevalT : ∀ (k : Nat) (t : Nat → Bool) (v : Fin k → CK),
    Formal.Core.LutList.muxTree t (List.ofFn (fun i => toCells (v i))) = toCells (kevalT k t v)
  | 0, t, v => by simp [Formal.Core.LutList.muxTree, kevalT]
  | k + 1, t, v => by
      rw [kevalT_succ, toCells_cmux, ← cells_muxTree_eq_kevalT k, ← cells_muxTree_eq_kevalT k,
        List.ofFn_succ]
      rfl

theorem cells_muxTree_eq_keval {k : Nat} (L : Lut k) (v : Fin k → CK) :
    Formal.Core.LutList.muxTree L.init.toNat.testBit (List.ofFn (fun i => toCells (v i))) =
      toCells (L.keval v) :=
  cells_muxTree_eq_kevalT k L.entry v

/-- **Shard B's closure semantics `lutK` (hypothesis H_KLEENE_LUT) = Core `keval`
= Core `kevalSpec`.** -/
theorem cells_lutK_eq_keval {k : Nat} (L : Lut k) (v : Fin k → CK) :
    Formal.Core.LutList.lutK L.init.toNat (List.ofFn (fun i => toCells (v i))) = toCells (L.keval v) := by
  rw [← Formal.Core.LutList.muxTree_eq_lutK, cells_muxTree_eq_keval]

theorem cells_lutK_eq_kevalSpec {k : Nat} (L : Lut k) (v : Fin k → CK) :
    Formal.Core.LutList.lutK L.init.toNat (List.ofFn (fun i => toCells (v i))) = toCells (L.kevalSpec v) := by
  rw [cells_lutK_eq_keval, Lut.keval_eq_kevalSpec]

theorem cells_lutB_eq_eval {k : Nat} (L : Lut k) (x : Fin k → Bool) :
    Formal.Core.LutList.lutB L.init.toNat (List.ofFn x) = L.eval x := by
  simp [Formal.Core.LutList.lutB, ← lsbAddr_eq_lutIdx, lsbAddr_ofFn, Lut.eval, entry_eq_testBit]

/-! ### LUT6_2 `O5` -/

theorem lt_evalTree_congr : ∀ (v : List LK) (g g' : List Bool → Bool),
    (∀ w : List Bool, w.length = v.length → g w = g' w) →
    LutTree.evalTree v g = LutTree.evalTree v g'
  | [], g, g', h => by simp [LutTree.evalTree, h [] rfl]
  | a :: v, g, g', h => by
      simp only [LutTree.evalTree]
      rw [lt_evalTree_congr v (fun w => g (false :: w)) (fun w => g' (false :: w))
            (fun w hw => h _ (by simp [hw])),
          lt_evalTree_congr v (fun w => g (true :: w)) (fun w => g' (true :: w))
            (fun w hw => h _ (by simp [hw]))]

theorem addrOf_lt : ∀ w : List Bool, LutTree.addrOf w < 2 ^ w.length
  | [] => by simp [LutTree.addrOf]
  | b :: w => by
      have := addrOf_lt w
      simp only [LutTree.addrOf, List.length_cons, Nat.pow_succ]
      cases b <;> simp <;> omega

/-- LutTree's `lut6O5` (lower LUT5, INIT[31:0], pins `[A5, …, A1]`) is Core's
`Lut62.o5`. -/
theorem lt_lut6O5_eq_keval (L : Lut62) (v : Fin 5 → CK) :
    LutTree.lut6O5 L.init.toNat (silList v) = toLT (L.o5.keval v) := by
  rw [← lt_evalTree_sil_eq_keval]
  apply lt_evalTree_congr
  intro w hw
  rw [silList_length] at hw
  have hlt := addrOf_lt w
  rw [hw] at hlt
  rw [LutTree.initFun_lower]
  simp only [LutTree.initFun, Lut62.o5, BitVec.testBit_toNat, BitVec.getLsbD_setWidth]
  have : LutTree.addrOf w < 32 := hlt
  simp [this]

/-! ## 3. Transfer of headline theorems -/

/-- **Core facts drive the timed physical tree.** A LutTree physical mux tree
whose SRAM holds a Core LUT's INIT in silicon order (A6 = `I(k-1)` at the
root), under LutTree's explicit hypotheses `H_sram` and `H_mux_kleene`, with
pins abstracted by `v` (pins that are `X` in `v` may do anything): whenever
Core computes `L.keval v = ofBool c`, the output is `c` at every instant, for
every per-mux and per-copy delay. -/
theorem phys_glitch_free_of_core {k : Nat} (L : Lut k) (v : Fin k → CK) (P : LutTree.PhysTree k)
    (hinit : P.init = LutTree.initFun L.init.toNat) (hs : P.H_sram) (hm : P.H_mux_kleene)
    (hv : P.Abstracts (silList v)) (c : Bool) (hc : L.keval v = K3.ofBool c)
    (τ : LutTree.Time) : P.y [] τ = LutTree.K3.ofBool c := by
  have h := P.root_sound hs hm hv τ
  rw [hinit, ← LutTree.evalTree_eq_tableEval, lt_evalTree_sil_eq_keval, hc, toLT_ofBool] at h
  exact h.ofBool_eq

/-- **Single input change, INIT condition discharged by Core's
`Lut.no_static_hazard_single`.** Pin `j` moves (it is `X` in the abstraction,
so it may move slowly, ring, dwell mid-rail), all other pins hold `x`, and the
Boolean LUT gives the same value at both ends: the physical output never
leaves that value. -/
theorem phys_sic_of_core {k : Nat} (L : Lut k) (x : Fin k → Bool) (j : Fin k)
    (h : L.eval (setAt x j (!x j)) = L.eval x) (P : LutTree.PhysTree k)
    (hinit : P.init = LutTree.initFun L.init.toNat) (hs : P.H_sram) (hm : P.H_mux_kleene)
    (hv : P.Abstracts (silList (setAt (K3.ofBoolVec x) j K3.X))) (τ : LutTree.Time) :
    P.y [] τ = LutTree.K3.ofBool (L.eval x) :=
  phys_glitch_free_of_core L _ P hinit hs hm hv _ (L.no_static_hazard_single x j h) τ

/-- Multi-input version via Core's `Lut.keval_hull_eq_ofBool_iff`: every pin
that differs between `x` and `x'` may move arbitrarily; if the whole subcube
between them evaluates to `b`, the physical output is `b` throughout. -/
theorem phys_hull_of_core {k : Nat} (L : Lut k) (x x' : Fin k → Bool) (b : Bool)
    (h : ∀ y, (∀ i, x i = x' i → y i = x i) → L.eval y = b) (P : LutTree.PhysTree k)
    (hinit : P.init = LutTree.initFun L.init.toNat) (hs : P.H_sram) (hm : P.H_mux_kleene)
    (hv : P.Abstracts (silList (Lut.hull x x'))) (τ : LutTree.Time) :
    P.y [] τ = LutTree.K3.ofBool b :=
  phys_glitch_free_of_core L _ P hinit hs hm hv b ((L.keval_hull_eq_ofBool_iff x x' b).2 h) τ

/-- **X containment of the C-element, physically.** `bd_c2` (bd_ce.v:34) as a
LUT6 tree in silicon order `[A6, A5, A4, A3, A2, A1] = [0, 0, rst=0, q, b, a]`:
with `a = b` steady, `rst = 0`, and the feedback pin `q` doing anything at all,
the output is `a` at every instant (from `Init.bd_c2_contain`). -/
theorem phys_bd_c2_contain (a : Bool) (P : LutTree.PhysTree 6)
    (hinit : P.init = LutTree.initFun Init.bd_c2.init.toNat) (hs : P.H_sram) (hm : P.H_mux_kleene)
    (hv : P.Abstracts [.zero, .zero, .zero, .X, LutTree.K3.ofBool a, LutTree.K3.ofBool a])
    (τ : LutTree.Time) : P.y [] τ = LutTree.K3.ofBool a := by
  have e : silList (kvec [K3.ofBool a, K3.ofBool a, K3.X, K3.zero, K3.zero, K3.zero] 6) =
      [.zero, .zero, .zero, .X, LutTree.K3.ofBool a, LutTree.K3.ofBool a] := by
    cases a <;> rfl
  exact phys_glitch_free_of_core _ _ P hinit hs hm (e ▸ hv) a (Init.bd_c2_contain a) τ

/-! ### Ternary's `bd_c2` network is Core's `Init.bd_c2` -/

theorem bdc2_lut4_eq_lut6 (a b q r : CK) :
    kevalT 4 (Nat.testBit 0x00E8) (kvec [a, b, q, r] 4) =
      Init.bd_c2.keval (kvec [a, b, q, r, .zero, .zero] 6) := by
  cases a <;> cases b <;> cases q <;> cases r <;> decide

/-- **Ternary's `bdc2Net` (a LUT4 with table `0x00E8`, pins a, b, q, rst) is,
in Kleene semantics, exactly Core's `Init.bd_c2` LUT6 with `I4 = I5 = 0`**, for
every ternary input vector and state. -/
theorem tern_bdc2_F_eq_core (u : Fin 3 → TK) (t : Unit → TK) :
    Ternary.bdc2Net.F u t () =
      toTern (Init.bd_c2.keval
        (kvec [ofTern (u 0), ofTern (u 1), ofTern (t ()), ofTern (u 2), .zero, .zero] 6)) := by
  rw [← bdc2_lut4_eq_lut6]
  have hw : @Eq (Fin 4 → TK) (fun p => Sum.elim u t (Ternary.bdc2.pin () p))
      (fun i => toTern (kvec [ofTern (u 0), ofTern (u 1), ofTern (t ()), ofTern (u 2)] 4 i)) := by
    funext p
    match p with
    | ⟨0, _⟩ => exact (toTern_ofTern _).symm
    | ⟨1, _⟩ => exact (toTern_ofTern _).symm
    | ⟨2, _⟩ => exact (toTern_ofTern _).symm
    | ⟨3, _⟩ => exact (toTern_ofTern _).symm
  show Ternary.kext 4 (Ternary.initTbl 0x00E8) (fun p => Sum.elim u t (Ternary.bdc2.pin () p)) = _
  exact (congrArg (Ternary.kext 4 (Ternary.initTbl 0x00E8)) hw).trans (tern_kext_eq_kevalT 4 _ _)

/-- The Boolean function agrees too. -/
theorem tern_bdc2_fb_eq_core (a b r q : Bool) :
    Ternary.bdc2Net.fb (Ternary.inp a b r) (fun _ => q) () =
      Init.bd_c2.eval (bvec [a, b, q, r, false, false] 6) := by
  revert a b r q; decide

/-- Ternary's `bdc2_no_static_hazard` with its stability hypothesis stated on
Core's `Init.bd_c2` (`q = bd_c2(a, b, q, rst)`, INIT `64'h00E8_00E8_00E8_00E8`).
The single-input-change hypothesis `hsame` stays in Ternary's algorithm-B form;
`Ternary.bdc2_single_input_ok` decides it for every stable state. -/
theorem core_bdc2_no_static_hazard (a b r q : Bool) (j : Fin 3)
    (hst : Init.bd_c2.eval (bvec [a, b, q, r, false, false] 6) = q)
    (hsame : Ternary.rB (Ternary.inp a b r) j q = Ternary.K3.ofBool q)
    (c : Nat → Fin 3 → Bool) (σ : Nat → Unit → Bool)
    (hc : ∀ t x, c t x = Ternary.inp a b r x ∨ c t x = Ternary.flip (Ternary.inp a b r) j x)
    (hσ : Ternary.Causal Ternary.bdc2Net c σ) (h0 : σ 0 = fun _ => q) : ∀ t, σ t () = q :=
  Ternary.bdc2_no_static_hazard a b r q j (by rw [tern_bdc2_fb_eq_core]; exact hst) hsame c σ hc hσ h0

end Formal.Core.Bridge
