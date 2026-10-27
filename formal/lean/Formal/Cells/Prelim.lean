import Formal.Core.Kleene
import Formal.Core.Lut

/-!
# Shard B preliminaries: the cell proofs' names for Core's values and LUTs

Since the Phase-1 port (formal/notes/B-port-core.md) this file defines nothing
of its own semantics: every name is Core's object, or a list-indexed view of
it whose agreement with Core is proved here.

* `K3` IS `Formal.Core.K3` (an `abbrev`). `K3.f`, `K3.t`, `K3.x` are
  `@[match_pattern]` names for Core's constructors `zero`, `one`, `X`, kept so
  that the cell files read as before. `K3.ofBool` is Core's;
  `K3.join` and `K3.not` are Core's `K3.merge` and `K3.not` (`join_eq_merge`,
  `not_eq_core`, both `rfl`; separate constants only so that existing
  `simp [K3.join]` calls keep unfolding them).
* `lutB init ins`   binary LUT: the INIT bit addressed by the inputs, I0 = LSB.
  `lutB_ofFn`: on `List.ofFn x` it is Core's `Lut.eval` (any width `k`).
* `muxTree g ins`   the Kleene mux tree over the table `g`, I0 at the root.
  `muxTree_ofFn`: on `List.ofFn v` it is Core's `kevalT` (the mux tree that
  defines `Lut.keval`), node for node.
* `lutK init ins := muxTree init.testBit ins`   Kleene LUT = Core's mux-tree
  semantics. `lutK_ofFn`: on `List.ofFn v` it is `Lut.keval`; with
  `Lut.keval_eq_kevalSpec` it is also the closure specification ("t/f if every
  INIT entry consistent with the inputs is 1/0, else x"). That closure form,
  which was this file's definition of `lutK` before the port, is the theorem
  `MuxTree.lutK_eq_closure` (file `MuxTree.lean`).
  Hypothesis **H_KLEENE_LUT**: a 7-series LUT is a pass-transistor mux tree,
  and a mux whose select is intermediate passes a definite value when both
  data legs carry it, and an intermediate value otherwise (`K3.mux`).
  Test: GLS with an X-driven select pin and equal data, or board injection of a
  slow edge on one LUT pin with the other INIT legs equal.
* LUT6_2: `O6 = INIT[I5..I0]`, `O5 = INIT[0,I4..I0]` (lower 32 bits).
-/

namespace Formal.Cells

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
This is Core's `K3.merge` (the glb in the information order), by `rfl`
(`join_eq_merge`); it is kept as its own constant so that `simp [K3.join]`
unfolds it to the `if`. -/
def join (a b : K3) : K3 := if a = b then a else x

theorem join_eq_merge : join = Formal.Core.K3.merge := rfl

/-- Kleene 2:1 mux (the per-mux form of H_KLEENE_LUT): select `f` takes `a`,
`t` takes `b`, `x` passes a value only when both legs carry it. This is the
mux that Core's `kevalT` inlines at every node. -/
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
root: it selects between the even entries (head = 0) and the odd ones, each
an identical tree over the remaining inputs. The physical I0..I5 order of the
silicon tree is not known; this is one order (the research GLS order, and the
order of Core's `kevalT`). -/
def muxTree : (g : Nat → Bool) → (ins : List K3) → K3
  | g, [] => K3.ofBool (g 0)
  | g, s :: ss => K3.mux s (muxTree (fun j => g (2 * j)) ss) (muxTree (fun j => g (2 * j + 1)) ss)

/-- Kleene LUT (hypothesis H_KLEENE_LUT): Core's mux-tree semantics. -/
def lutK (init : Nat) (ins : List K3) : K3 := muxTree init.testBit ins

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
open Formal.Core

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

end Formal.Cells
