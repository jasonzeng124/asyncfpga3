import Formal.Core.Kleene
import Formal.Core.Lut

/-!
# Formal.Core.LutList — the list-indexed view of Core's LUTs

Shard A. This is the list-based LUT API that `Formal/Cells/Prelim.lean`
(shard B) provides, moved into Core so that Prelim can be deleted
(notes/B-port-core.md "What remains to delete Prelim", notes/A-lutlist.md).
Every name of Prelim is here with the same body, under the namespace
`Formal.Core.LutList` instead of `Formal.Cells`. The proof that each one is
the same function as Prelim's is in `Wip/LutList/PrelimEq.lean` (`rfl`, or list
induction for the recursive ones);
it is not claimed, because it imports Prelim, which is to be deleted.

Nothing here is new semantics. Every name is either Core's object or a
list-indexed view of it whose agreement with Core is proved in this file:

* `K3` IS `Formal.Core.K3` (an `abbrev`). `K3.f`, `K3.t`, `K3.x` are
  `@[match_pattern]` names for Core's constructors `zero`, `one`, `X`.
  `K3.ofBool` is Core's (`abbrev`). `K3.join` and `K3.not` are Core's
  `K3.merge` and `K3.not` (`join_eq_merge`, `not_eq_core`, both `rfl`); they
  are separate constants only so that `simp [K3.join]` unfolds to the `if`.
  `K3.mux` is the Kleene 2:1 mux that Core's `kevalT` inlines (`mux_eq`).
  `K3.admits a b` is Core's `a ⊑ ofBool b` (`admits_iff_le`).
* `lutB init ins`: binary LUT, the INIT bit addressed by `ins = [I0, I1, …]`,
  I0 = LSB. `lutB_ofFn`: on `List.ofFn x` it is Core's `Lut.eval` (any `k`).
* `muxTree g ins`: the Kleene mux tree over the table `g`, I0 at the root.
  `muxTree_ofFn`: on `List.ofFn v` it is Core's `kevalT`, node for node.
* `lutK init ins := muxTree init.testBit ins`: Kleene LUT. `lutK_ofFn`: on
  `List.ofFn v` it is `Lut.keval`; `lutK_ofFn_spec`: it is `Lut.kevalSpec`
  (the closure: `t`/`f` iff every INIT entry consistent with the inputs is
  1/0, else `x`). `muxTree_eq_lutK` (`rfl`) replaces
  `Formal.Cells.MuxTree.muxTree_eq_lutK` for importers that only need that.
* `completions`: all Boolean vectors consistent with a Kleene list.
* LUT6_2: `o6B/o6K = INIT[I5..I0]`, `o5B/o5K = INIT[31:0][I4..I0]`.

Assumed: nothing beyond Core's definitions. The physical reading of
`lutK`/`muxTree` is hypothesis H_KLEENE_LUT (a 7-series LUT is a
pass-transistor mux tree whose X-select mux passes a value only when both
legs carry it), exactly as in Core's `Lut.keval`; this file adds no
hypothesis. Not covered: the physical order of the pins in the silicon tree
(this is the I0-at-root order of Core's `kevalT`; `Core.Bridge` relates it to
the silicon order), timing, and lists whose length differs from the LUT width
(`lutB`/`lutK` are total on lists, the agreement theorems are for `List.ofFn`
of a `Fin k` vector).
-/

namespace Formal.Core.LutList

/-- Kleene three-valued signal level: Core's `K3`. `x` = not a valid logic level. -/
abbrev K3 := Formal.Core.K3

namespace K3
/-- Logic 0 (Core `K3.zero`). -/
@[match_pattern, reducible] def f : K3 := Formal.Core.K3.zero
/-- Logic 1 (Core `K3.one`). -/
@[match_pattern, reducible] def t : K3 := Formal.Core.K3.one
/-- Not a valid level (Core `K3.X`). -/
@[match_pattern, reducible] def x : K3 := Formal.Core.K3.X

/-- Core's embedding of `Bool`. -/
abbrev ofBool : Bool → K3 := Formal.Core.K3.ofBool

/-- Join of two readings of the same node: equal values stay, else `x`.
Core's `K3.merge`, by `rfl` (`join_eq_merge`). -/
def join (a b : K3) : K3 := if a = b then a else x

theorem join_eq_merge : join = Formal.Core.K3.merge := rfl

/-- Kleene 2:1 mux: select `f` takes `a`, `t` takes `b`, `x` passes a value
only when both legs carry it. The mux that Core's `kevalT` inlines. -/
def mux (s a b : K3) : K3 :=
  match s with
  | f => a
  | t => b
  | x => join a b

/-- Strong-Kleene negation; Core's `K3.not` by `rfl` (`not_eq_core`). -/
def not : K3 → K3
  | f => t
  | t => f
  | x => x

theorem not_eq_core : not = Formal.Core.K3.not := rfl

/-- Is a Bool consistent with a K3 reading? (Core: `a ⊑ ofBool b`, `admits_iff_le`.) -/
def admits : K3 → Bool → Bool
  | f, b => !b
  | t, b => b
  | x, _ => true

theorem admits_iff_le (a : K3) (b : Bool) :
    admits a b = true ↔ Formal.Core.K3.Le a (Formal.Core.K3.ofBool b) := by
  cases a <;> cases b <;> decide
end K3

/-- Address of a LUT entry: `ins` is `[I0, I1, ...]`, I0 the least significant bit. -/
def lutIdx : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * lutIdx bs

/-- Binary LUT. -/
def lutB (init : Nat) (ins : List Bool) : Bool := init.testBit (lutIdx ins)

/-- All Boolean vectors consistent with a Kleene input vector. -/
def completions : List K3 → List (List Bool)
  | [] => [[]]
  | a :: as =>
    let rest := completions as
    (if K3.admits a false then rest.map (false :: ·) else []) ++
    (if K3.admits a true then rest.map (true :: ·) else [])

/-- A mux tree over the table `g` (entry `j` = `g j`), the head input at the
root (the order of Core's `kevalT`). -/
def muxTree : (g : Nat → Bool) → (ins : List K3) → K3
  | g, [] => K3.ofBool (g 0)
  | g, s :: ss => K3.mux s (muxTree (fun j => g (2 * j)) ss) (muxTree (fun j => g (2 * j + 1)) ss)

/-- Kleene LUT (hypothesis H_KLEENE_LUT): Core's mux-tree semantics. -/
def lutK (init : Nat) (ins : List K3) : K3 := muxTree init.testBit ins

/-- `lutK` is the mux tree over the INIT bits (by definition). -/
theorem muxTree_eq_lutK (init : Nat) (ins : List K3) :
    muxTree init.testBit ins = lutK init ins := rfl

/-! The LUT6_2 outputs. Pins listed `[I0, I1, I2, I3, I4, I5]`. -/
def o6B (init : Nat) (ins : List Bool) : Bool := lutB init ins
def o5B (init : Nat) (ins : List Bool) : Bool := lutB (init % 2 ^ 32) (ins.take 5)
def o6K (init : Nat) (ins : List K3) : K3 := lutK init ins
def o5K (init : Nat) (ins : List K3) : K3 := lutK (init % 2 ^ 32) (ins.take 5)

/-! ## Agreement with Core (`Formal.Core.Lut`)

Inputs as a Core vector `x : Fin k → _` (`x 0` = pin I0) are the list
`List.ofFn x`; a Core `Lut k` with INIT `L.init : BitVec (2^k)` is the number
`L.init.toNat`. -/

section CoreAgree

theorem mux_eq (s a b : K3) :
    K3.mux s a b = match s with
      | .zero => a
      | .one => b
      | .X => Formal.Core.K3.merge a b := by
  cases s <;> rfl

theorem lutIdx_ofFn : ∀ {k : Nat} (x : Fin k → Bool), lutIdx (List.ofFn x) = addr x
  | 0, _ => rfl
  | k + 1, x => by
      rw [List.ofFn_succ, lutIdx, addr, lutIdx_ofFn]
      cases x 0 <;> rfl

theorem entry_eq_testBit {k : Nat} (L : Lut k) (a : Nat) : L.entry a = L.init.toNat.testBit a :=
  (BitVec.testBit_toNat L.init).symm

/-- `lutB` on an input vector is Core's `Lut.eval`. -/
theorem lutB_ofFn {k : Nat} (L : Lut k) (x : Fin k → Bool) :
    lutB L.init.toNat (List.ofFn x) = L.eval x := by
  rw [lutB, lutIdx_ofFn, Lut.eval, entry_eq_testBit]

/-- `muxTree` on an input vector is Core's mux tree `kevalT`, for any table. -/
theorem muxTree_ofFn : ∀ (k : Nat) (g : Nat → Bool) (v : Fin k → K3),
    muxTree g (List.ofFn v) = kevalT k g v
  | 0, _, _ => rfl
  | k + 1, g, v => by
      rw [List.ofFn_succ, muxTree, muxTree_ofFn k, muxTree_ofFn k]
      rw [kevalT, mux_eq]
      cases v 0 <;> rfl

theorem muxTree_congr : ∀ (g g' : Nat → Bool) (ins : List K3), (∀ j, g j = g' j) →
    muxTree g ins = muxTree g' ins
  | g, g', [], h => by simp [muxTree, h 0]
  | g, g', s :: ss, h => by
      simp only [muxTree]
      rw [muxTree_congr _ (fun j => g' (2 * j)) ss (fun j => h _),
        muxTree_congr _ (fun j => g' (2 * j + 1)) ss (fun j => h _)]

/-- `lutK` on an input vector is Core's `Lut.keval`. -/
theorem lutK_ofFn {k : Nat} (L : Lut k) (v : Fin k → K3) :
    lutK L.init.toNat (List.ofFn v) = L.keval v := by
  rw [lutK, muxTree_ofFn, Lut.keval]
  exact (congrArg (fun g => kevalT k g v) (funext (entry_eq_testBit L))).symm

/-- `lutK` on an input vector is Core's specification `Lut.kevalSpec`. -/
theorem lutK_ofFn_spec {k : Nat} (L : Lut k) (v : Fin k → K3) :
    lutK L.init.toNat (List.ofFn v) = L.kevalSpec v := by
  rw [lutK_ofFn, Lut.keval_eq_kevalSpec]

end CoreAgree

end Formal.Core.LutList
