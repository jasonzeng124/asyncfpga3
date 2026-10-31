import Formal.Net.CoreLut

/-!
# Track 11a: imported netlists and their generic interpreter

`Formal/Net/Import/Cells.lean` is GENERATED from yosys `write_json` output by
`formal/tools/import/yosys2lean.py` (run `formal/tools/import/import.sh`). It
contains one `Netlist` value per library cell, exactly as the project's
synthesis flow (`synth_xilinx`, yosys 0.62) leaves it: the instantiated
`LUTk`/`LUT6_2` primitives with their `INIT` as a `Nat`, the `IBUF`/`OBUF`
pads `synth_xilinx` inserts at a top level, and every pin -> net connection.

This file is the hand-written half: the data types and ONE interpreter, used
for every cell, parametric in the value domain:

* `boolSem`   LUTs read by shard A's Core `Lut.eval` (`Formal.Net.CoreLut.evalL`),
* `kleeneSem` LUTs read by Core `Lut.keval` (`kevalL`, the Kleene mux tree,
  hypothesis H_KLEENE_LUT), values in `Formal.Core.K3`.

(Probe 11e moved this file off shard B's `Formal.Cells.Prelim`;
`Formal.Net.CoreLutPrelim` proves the two semantics equal, and
`Formal.Net.Import.PrelimSem` keeps the Prelim-valued reading for the theorems
that compare with B's still-Prelim transcriptions.)

`LUT6_2` follows Core's `Lut62`: `O6 = lut INIT [I0..I5]`, `O5 = lut (INIT mod 2^32)
[I0..I4]`. `IBUF`/`OBUF` are identity (hypothesis **H_PAD_IDENTITY**: a pad
buffer is a zero-delay wire; it only appears because the cell is synthesized
as a top level, and in a real design the cell is flattened into its context
with no pads at all).

## Semantics: one combinational step with the feedback nets as state

`Netlist.state` lists the nets the importer cut to break every cycle (targets
of DFS back edges; for every library cell this is exactly the LUT outputs that
are routed back to their own LUT). Given values for the input ports and for
the state nets, every other net is a combinational function of them (computed
by `evalNet`, with fuel = number of cells, so a cycle not cut by `state`
makes evaluation fail with `none` rather than loop). `next` gives, for each
state net, the value its driver cell produces: the next-state function of
the loop, with the feedback pin read as an independent input. This is the
same reading as shard B's `next` in `Formal/Cells/CElemFn.lean`; the timing of
the feedback wire is not modelled here (B's H_FB_SETTLED / probe 5b).

Every function returns `Option`: a missing pin, an undriven net or an uncut
cycle gives `none`, so a theorem `next .. = some v` also certifies that the
imported netlist is well formed on that input.
-/

namespace Formal.Net.Import
open Formal.Net.CoreLut

/-- Primitive pins (UNISIM names). -/
inductive Pin where
  | I | I0 | I1 | I2 | I3 | I4 | I5 | O | O5 | O6
  deriving DecidableEq, Repr

/-- What a pin is connected to: a net (yosys bit id) or a constant tie. -/
inductive Src where
  | net (n : Nat)
  | const (b : Bool)
  deriving DecidableEq, Repr

/-- Primitive types the importer accepts (anything else is an import error). -/
inductive Kind where
  | lut (k : Nat)   -- LUT1 .. LUT6, output `O`
  | lut6_2          -- fractured LUT6_2, outputs `O5`, `O6`
  | ibuf | obuf     -- pads, `I` -> `O`
  deriving DecidableEq, Repr

structure Cell where
  name : String
  kind : Kind
  /-- `INIT` parameter, bit `j` = output for input address `j` (I0 = LSB). -/
  init : Nat
  /-- The cell carried `(* keep *)` in the netlist. -/
  keep : Bool
  /-- The pin -> net map. -/
  conn : List (Pin × Src)
  deriving Repr

structure Netlist where
  top : String
  /-- Input ports, bit-blasted, in declaration order: name -> net. -/
  inputs : List (String × Nat)
  outputs : List (String × Nat)
  /-- Feedback nets cut as state. -/
  state : List Nat
  /-- Net names (for reading only; the interpreter does not use them). -/
  nets : List (Nat × String)
  cells : List Cell
  deriving Repr

/-- A value domain: how a LUT reads its table, and what a tie drives. -/
structure Sem (V : Type) where
  lut : Nat → List V → V
  const : Bool → V

def boolSem : Sem Bool := ⟨evalL, id⟩
def kleeneSem : Sem Formal.Core.K3 := ⟨kevalL, Formal.Core.K3.ofBool⟩

def inPins : Kind → List Pin
  | .lut k => [Pin.I0, .I1, .I2, .I3, .I4, .I5].take k
  | .lut6_2 => [.I0, .I1, .I2, .I3, .I4, .I5]
  | .ibuf | .obuf => [.I]

def outPins : Kind → List Pin
  | .lut _ => [.O]
  | .lut6_2 => [.O5, .O6]
  | .ibuf | .obuf => [.O]

/-- The value on output pin `p` of `c`, given its input pin values in
`inPins` order. -/
def Cell.out {V : Type} (sem : Sem V) (c : Cell) (p : Pin) (ins : List V) : Option V :=
  match c.kind, p with
  | .lut _, .O => some (sem.lut c.init ins)
  | .lut6_2, .O6 => some (sem.lut c.init ins)
  | .lut6_2, .O5 => some (sem.lut (c.init % 2 ^ 32) (ins.take 5))
  | .ibuf, .O => ins.head?
  | .obuf, .O => ins.head?
  | _, _ => none

/-- The (first) cell output pin driving net `n`. The importer rejects multiply
driven nets, so "first" is "the". -/
def Netlist.driver (nl : Netlist) (n : Nat) : Option (Cell × Pin) :=
  nl.cells.findSome? fun c =>
    (outPins c.kind).findSome? fun p =>
      if c.conn.lookup p = some (.net n) then some (c, p) else none

/-- Value of net `n`: from `env` (inputs and state) if given there, else
computed from its driver. `fuel` bounds the combinational depth. -/
def evalNet {V : Type} (sem : Sem V) (nl : Netlist) (env : List (Nat × V)) :
    Nat → Nat → Option V
  | 0, _ => none
  | fuel + 1, n =>
    match env.lookup n with
    | some v => some v
    | none =>
      match nl.driver n with
      | none => none
      | some (c, p) => do
        let ins ← (inPins c.kind).mapM fun q =>
          match c.conn.lookup q with
          | some (.const b) => some (sem.const b)
          | some (.net m) => evalNet sem nl env fuel m
          | none => none
        c.out sem p ins

/-- Read one source pin. -/
def evalSrc {V : Type} (sem : Sem V) (nl : Netlist) (env : List (Nat × V)) (fuel : Nat) :
    Option Src → Option V
  | some (.const b) => some (sem.const b)
  | some (.net m) => evalNet sem nl env fuel m
  | none => none

def Netlist.fuel (nl : Netlist) : Nat := nl.cells.length + 1

/-- The environment: input ports (declaration order) and state nets
(`state` order) bound to the given values. -/
def Netlist.env {V : Type} (nl : Netlist) (ins st : List V) : List (Nat × V) :=
  (nl.inputs.map Prod.snd).zip ins ++ nl.state.zip st

/-- Next value of every state net: its driver evaluated on the current
environment. -/
def Netlist.next {V : Type} (sem : Sem V) (nl : Netlist) (ins st : List V) :
    Option (List V) :=
  let env := nl.env ins st
  nl.state.mapM fun s => do
    let (c, p) ← nl.driver s
    let vs ← (inPins c.kind).mapM fun q => evalSrc sem nl env nl.fuel (c.conn.lookup q)
    c.out sem p vs

/-- Output ports (declaration order) as a function of inputs and state. -/
def Netlist.outs {V : Type} (sem : Sem V) (nl : Netlist) (ins st : List V) :
    Option (List V) :=
  nl.outputs.mapM fun (_, n) => evalNet sem nl (nl.env ins st) nl.fuel n

/-- The unit-step run of the netlist: state at step `t` under an input
sequence. (`none` propagates.) Not used by the theorems below except as the
obvious iteration of `next`. -/
def Netlist.run {V : Type} (sem : Sem V) (nl : Netlist) (inp : Nat → List V) (s0 : List V) :
    Nat → Option (List V)
  | 0 => some s0
  | t + 1 => (nl.run sem inp s0 t).bind (nl.next sem (inp t))

/-- Structural facts checked by `decide` on an imported netlist: names of the
ports in order, and which cells carry `(* keep *)`. -/
def Netlist.inputNames (nl : Netlist) : List String := nl.inputs.map Prod.fst
def Netlist.outputNames (nl : Netlist) : List String := nl.outputs.map Prod.fst
def Netlist.stateNames (nl : Netlist) : List String := nl.state.map fun s => (nl.nets.lookup s).getD "?"

end Formal.Net.Import
