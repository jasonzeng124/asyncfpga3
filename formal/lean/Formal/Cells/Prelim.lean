/-!
# Shard B preliminaries: values and LUT semantics for the cell proofs

Local stand-in until shard A's `Formal/Core/` lands (PROGRAM.md, Shards).
Core Lean only, no Mathlib, so cell files that need no reals check fast.

* `lutB init ins`   binary LUT: the INIT bit addressed by the inputs, I0 = LSB.
* `lutK init ins`   Kleene LUT: `t`/`f` if every INIT entry consistent with the
  inputs is 1/0, else `x`. This is hypothesis **H_KLEENE_LUT**: a 7-series LUT
  is a pass-transistor mux tree, and we assume a mux whose select is
  intermediate passes a definite value when both data legs carry it, and an
  intermediate value otherwise (`K3.mux`). Whether this per-mux hypothesis,
  applied level by level up `muxTree`, gives exactly `lutK` is proved (or
  not) in `Formal/Cells/MuxTree.lean`.
  Test: GLS with an X-driven select pin and equal data, or board injection of a
  slow edge on one LUT pin with the other INIT legs equal.
* LUT6_2: `O6 = INIT[I5..I0]`, `O5 = INIT[0,I4..I0]` (lower 32 bits).
-/

namespace Formal.Cells

/-- Kleene three-valued signal level. `x` = not a valid logic level. -/
inductive K3 where
  | f | t | x
  deriving DecidableEq, Repr, Inhabited

namespace K3
def ofBool : Bool → K3
  | true => t
  | false => f

/-- Join of two readings of the same node: equal values stay, else `x`. -/
def join (a b : K3) : K3 := if a = b then a else x

/-- Kleene 2:1 mux (the per-mux form of H_KLEENE_LUT): select `f` takes `a`,
`t` takes `b`, `x` passes a value only when both legs carry it. -/
def mux (s a b : K3) : K3 :=
  match s with
  | f => a
  | t => b
  | x => join a b

def not : K3 → K3
  | f => t
  | t => f
  | x => x

/-- Is a Bool consistent with a K3 reading? -/
def admits : K3 → Bool → Bool
  | f, b => !b
  | t, b => b
  | x, _ => true
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

/-- Kleene LUT (closure semantics; hypothesis H_KLEENE_LUT). -/
def lutK (init : Nat) (ins : List K3) : K3 :=
  let vs := (completions ins).map (lutB init)
  if vs.all id then .t else if vs.all (!·) then .f else .x

/-- A mux tree over the table `g` (entry `j` = `g j`), the head input at the
root: it selects between the even entries (head = 0) and the odd ones, each
an identical tree over the remaining inputs. The physical I0..I5 order of the
silicon tree is not known; this is one order. -/
def muxTree : (g : Nat → Bool) → (ins : List K3) → K3
  | g, [] => K3.ofBool (g 0)
  | g, s :: ss => K3.mux s (muxTree (fun j => g (2 * j)) ss) (muxTree (fun j => g (2 * j + 1)) ss)

/-! The LUT6_2 outputs. Pins listed `[I0, I1, I2, I3, I4, I5]`. -/
def o6B (init : Nat) (ins : List Bool) : Bool := lutB init ins
def o5B (init : Nat) (ins : List Bool) : Bool := lutB (init % 2 ^ 32) (ins.take 5)
def o6K (init : Nat) (ins : List K3) : K3 := lutK init ins
def o5K (init : Nat) (ins : List K3) : K3 := lutK (init % 2 ^ 32) (ins.take 5)

end Formal.Cells
