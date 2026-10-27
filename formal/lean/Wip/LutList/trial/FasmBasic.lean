import Formal.Core.LutList
import Formal.Cells.CElemTiming

/-!
# Track 11b: the physical LUT netlist read from the FASM (the bits the board runs)

`formal/tools/fasm2lean/fasm2lean.py` reads a routed design's FASM plus
prjxray-db, never nextpnr's routed JSON or SDF, and emits a `PNet`: each used
LUT site with its PHYSICAL INIT (addressed by the physical pins A6..A1, i.e.
after the placer's pin permutation and the FASM writer's re-encoding) and, for
each physical pin, the source the active pips connect it to.

Semantics (gate relations, shard B's discrete-time traces and window channel
`WinDelay` from `Formal.Cells.CElemTiming`, LUT function `lutB`/`o5B` from
`Formal.Core.LutList`; nothing is redefined):

* every LUT pin has its OWN trace (`pin i k`), a bounded-delay copy of its
  source: the route from a different source, or to a different sink, is a
  different wire with a different delay (`H_ROUTE`);
* every LUT output is a bounded-delay copy of the LUT function of its pin
  traces (`H_LUT`);
* a tie (`GND_WIRE`/`VCC_WIRE` through a GFAN) is constant (`H_TIE`).

`exc` (below) is the zero-delay "next-state function" of the net: what each
LUT output is being driven towards by the current values of its sources.
-/

namespace Formal.Net.Fasm
open Formal.Cells Formal.Cells.CElemTiming

inductive LOut | o6 | o5
  deriving DecidableEq, Repr

/-- Where a physical LUT pin (or an output port) gets its value. -/
inductive Src
  | const (v : Bool)          -- a tie-off (GND_WIRE / VCC_WIRE)
  | port (i : Nat)            -- input port `i` (an IOB I pin, through ILOGIC bypass)
  | lut (i : Nat) (o : LOut)  -- output `o` of LUT `i`
  deriving DecidableEq, Repr

/-- One used LUT site. `pins` = sources of physical pins `[A1, A2, ..., A6]`. -/
structure PLut where
  site : String
  init : Nat
  pins : List Src

structure PNet where
  luts : List PLut
  outs : List (String × Src)

/-- LUT function of a physical pin vector `[A1..A6]`: O6 = INIT[A6..A1],
O5 = INIT[31:0][A5..A1] (7-series LUT6_2). -/
def PLut.fn (L : PLut) : LOut → List Bool → Bool
  | .o6, v => Formal.Core.LutList.o6B L.init v
  | .o5, v => Formal.Core.LutList.o5B L.init v

def Src.val (ins : List Bool) (st : Nat → LOut → Bool) : Src → Bool
  | .const v => v
  | .port i => ins.getD i false
  | .lut i o => st i o

/-- Zero-delay excitation of output `o` of LUT `i`. -/
def PNet.exc (N : PNet) (i : Nat) (o : LOut) (ins : List Bool) (st : Nat → LOut → Bool) : Bool :=
  match N.luts[i]? with
  | some L => L.fn o (L.pins.map (Src.val ins st))
  | none => false

/-! ## Name-based views, so theorems do not depend on the router's LUT order -/

def lookup (env : List (String × Bool)) (n : String) : Bool :=
  match env.find? (·.1 == n) with
  | some p => p.2
  | none => false

/-- Input vector in `ports` order, from a name -> value environment. -/
def portVals (ports : List String) (env : List (String × Bool)) : List Bool :=
  ports.map (lookup env)

/-- Current LUT state from the values at the OUTPUT PORTS each LUT drives
(`outs` says which LUT output drives which port). -/
def outState (N : PNet) (env : List (String × Bool)) : Nat → LOut → Bool :=
  fun i o => match N.outs.find? (fun p => p.2 == Src.lut i o) with
    | some p => lookup env p.1
    | none => false

/-- Next value of the LUT driving output port `n`. -/
def PNet.outNext (N : PNet) (n : String) (ins : List Bool) (st : Nat → LOut → Bool) : Bool :=
  match N.outs.find? (·.1 == n) with
  | some (_, .lut i o) => N.exc i o ins st
  | some (_, s) => s.val ins st
  | none => false

/-! ## Gate-relation semantics -/

/-- The trace a route starts from. -/
def Src.trace (ins : Nat → Trace) (out : Nat → LOut → Trace) : Src → Trace
  | .const v => fun _ => v
  | .port i => ins i
  | .lut i o => out i o

/-- **The physical net's gate relations.** `pin i k` is physical pin `A(k+1)` of
LUT `i` as seen at the LUT; `out i o` its output pin; `ins j` input port `j`
at its IOB I pin. Delay bounds: `dl i` for LUT `i`'s core (pin to O), `dw i k`
for the route into pin `k` (pips, wires and the site-pin delay; the tool
reports the intrinsic sums in ps). -/
structure Behaves (N : PNet) (ins : Nat → Trace) (out : Nat → LOut → Trace)
    (pin : Nat → Nat → Trace) (dl : Nat → Nat × Nat) (dw : Nat → Nat → Nat × Nat) : Prop where
  /-- **H_LUT**: as `CElemTiming.Loop.H_LUT`, on the physical pins and the
  physical INIT. -/
  H_LUT : ∀ i L o, N.luts[i]? = some L →
    WinDelay (dl i).1 (dl i).2 (fun t => L.fn o ((List.range 6).map (fun k => pin i k t))) (out i o)
  /-- **H_ROUTE**: every routed pin is a bounded-delay copy of its source.
  Test: SDF/Elmore per sink at fast-min / slow-max (claude/research's delay
  calculator), scatter over seeds. -/
  H_ROUTE : ∀ i L k s, N.luts[i]? = some L → L.pins[k]? = some s →
    (∀ v, s ≠ .const v) → WinDelay (dw i k).1 (dw i k).2 (s.trace ins out) (pin i k)
  /-- **H_TIE**: a pin routed from a tie-off is constant from configuration on
  (the GFAN/GND_WIRE path has no other driver; the tool checks there is
  exactly one active driver per node). -/
  H_TIE : ∀ i L k v, N.luts[i]? = some L → L.pins[k]? = some (.const v) → ∀ t, pin i k t = v

end Formal.Net.Fasm
