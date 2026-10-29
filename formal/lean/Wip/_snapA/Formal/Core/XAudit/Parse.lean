import Lean.Data.Json
import Std.Data.HashMap
import Formal.Core.XAudit.Design

/-!
# Formal.Core.XAudit.Parse — the TRUSTED yosys-JSON parser shared by the executables

Factored out of `Main.lean` (xaudit) and `EventsMain.lean` (xevents), which
carried verbatim copies; `Events2Main.lean` (xevents2) uses it too. No `main`
here, so every executable can import it.

TRUSTED (not proved): everything in this file. It turns a yosys `write_json`
netlist and a band file into a `Design` (`buildDesign`): wire 0 = const0,
wire 1 = const1; every non-constant LUT pin gets its own routed wire and a
buffer gate (`k = 1`, INIT `0b10`) with that arc's band; LUT1..6 = one gate;
LUT6_2 = two gates (O6 full INIT, O5 = INIT mod 2^32 on I0..I4); pads are
buffer gates; clocked/hard storage and unknown cells are rejected. What the
proved theorems say about the resulting `Design` is in `Design.lean`
(`sat_build_iff`) and the per-domain files. See `formal/notes/A-xaudit.md`.
-/

namespace Formal.Core.XAudit.Parse

open Lean (Json)
open Formal.Core
open Formal.Core.XAudit
/-! ## Small helpers -/

def jget (j : Json) (k : String) : Option Json := (j.getObjVal? k).toOption

def jobj (j : Json) : List (String × Json) :=
  match j.getObj? with
  | .ok kvs => kvs.toList
  | .error _ => []

def jnat (j : Json) : Option Nat :=
  match j.getNat? with
  | .ok n => some n
  | .error _ => match j.getStr? with
    | .ok s => s.toNat?
    | .error _ => none

/-- Parse a yosys binary parameter string (MSB first). -/
def binStr (s : String) : Except String Nat :=
  s.foldl (fun acc c => do
    let a ← acc
    if c == '0' then pure (2 * a) else if c == '1' then pure (2 * a + 1)
    else throw s!"non-binary INIT digit '{c}' in {s}") (pure 0)

/-- A yosys bit: a net number, or a constant. -/
inductive Bit where
  | net (b : Nat)
  | c0
  | c1
  | cx
  deriving BEq, Repr

def parseBit (j : Json) : Except String Bit :=
  match j.getNat? with
  | .ok b => pure (.net b)
  | .error _ => match j.getStr? with
    | .ok "0" => pure .c0
    | .ok "1" => pure .c1
    | .ok s => if s == "x" || s == "z" then pure .cx else throw s!"bad bit {s}"
    | .error _ => throw s!"bad bit {j.compress}"

def bitsOf (j : Json) : Except String (List Bit) := do
  let a ← j.getArr?
  a.toList.mapM parseBit

/-! ## Bands -/

structure Bands where
  unit : Nat := 25
  lut : Nat × Nat := (45, 124)
  route : Nat × Nat := (100, 700)
  /-- default band of a LUT's own feedback arc (output net routed back to one
  of its own pins); `none`: same as `route`. -/
  feedback : Option (Nat × Nat) := none
  /-- pads (IBUF/OBUF): in steps, not ps. -/
  pad : Nat × Nat := (1, 1)
  cells : List (String × (Nat × Nat)) := []
  arcs : List (String × (Nat × Nat)) := []

def pairOf (j : Json) : Option (Nat × Nat) := do
  let a ← j.getArr?.toOption
  match a.toList with
  | [x, y] => do pure (← jnat x, ← jnat y)
  | _ => none

def parseBands (j : Json) : Bands :=
  let d : Bands := {}
  { unit := ((jget j "unit_ps").bind jnat).getD d.unit
    lut := ((jget j "lut").bind pairOf).getD d.lut
    route := ((jget j "route").bind pairOf).getD d.route
    feedback := (jget j "feedback").bind pairOf
    pad := ((jget j "pad_steps").bind pairOf).getD d.pad
    cells := ((jget j "cells").map jobj).getD [] |>.filterMap (fun (k, v) => (pairOf v).map (k, ·))
    arcs := ((jget j "arcs").map jobj).getD [] |>.filterMap (fun (k, v) => (pairOf v).map (k, ·)) }

/-- ps band → step band: `lo` rounded down (at least 1), `hi` rounded up. -/
def toSteps (u : Nat) (b : Nat × Nat) : Nat × Nat × Bool :=
  let lo := b.1 / u
  let hi := (b.2 + u - 1) / u
  (max 1 lo, max (max 1 lo) hi, lo == 0)

/-! ## Netlist → Design -/

structure GInfo where
  /-- `lut`, `route`, `pad` -/
  kind : String
  cell : String
  pin : String
  /-- for a LUT: indices (into the gate list) of the route gates of its pins. -/
  storage : Bool := false
  deriving Inhabited

structure Built where
  d : Design
  info : Array GInfo
  wname : Array String
  /-- input port bit name → wire -/
  inputs : List (String × Nat)
  raised : List String
  unit : Nat

structure St where
  nw : Nat := 2
  netW : List (Nat × Nat) := []
  names : Array String := #["<const0>", "<const1>"]
  gates : Array GSpec := #[]
  info : Array GInfo := #[]
  raised : List String := []

abbrev M := StateT St (Except String)

def newWire (nm : String) : M Nat := do
  let s ← get
  set { s with nw := s.nw + 1, names := s.names.push nm }
  pure s.nw

def netWire (b : Nat) (nm : String) : M Nat := do
  match (← get).netW.lookup b with
  | some w => pure w
  | none =>
      let w ← newWire nm
      modify fun s => { s with netW := (b, w) :: s.netW }
      pure w

def addGate (g : GSpec) (i : GInfo) : M Unit :=
  modify fun s => { s with gates := s.gates.push g, info := s.info.push i }

def lutArity (ty : String) : Option Nat :=
  match ty with
  | "LUT1" => some 1 | "LUT2" => some 2 | "LUT3" => some 3
  | "LUT4" => some 4 | "LUT5" => some 5 | "LUT6" => some 6 | _ => none

def isPad (ty : String) : Bool :=
  ty == "IBUF" || ty == "OBUF" || ty == "BUF" || ty == "IBUF_IBUFDISABLE" || ty == "OBUFT_NOTRI"

def isFF (ty : String) : Bool :=
  ["FDRE", "FDSE", "FDCE", "FDPE", "LDCE", "LDPE", "FDRE_1", "SRL16E", "SRLC32E", "RAMB18E1",
    "RAMB36E1", "DSP48E1"].contains ty

/-- `toSteps`, but an inverted band (`lo > hi` ps) is REJECTED instead of being
narrowed to `[lo, lo]` (probe E8Mux finding; spec: `SoundInertial.checkedSteps_ok`,
`checkedSteps_inverted`, `toSteps_hi_ceil`). Well-formed bands: same as `toSteps`. -/
def checkedSteps (u : Nat) (b : Nat × Nat) : Except String (Nat × Nat × Bool) :=
  if b.2 < b.1 then .error s!"inverted band [{b.1}, {b.2}] ps (lo > hi): NOT RECOGNISED"
  else .ok (toSteps u b)

def bandFor (B : Bands) (key : String) (dflt : Nat × Nat) (alts : List (String × (Nat × Nat))) :
    M (Nat × Nat) := do
  let b := (alts.lookup key).getD dflt
  let (lo, hi, r) ← match checkedSteps B.unit b with
    | .ok v => pure v
    | .error e => throw s!"band of {key}: {e}"
  if r then modify fun s => { s with raised := key :: s.raised }
  pure (lo, hi)

/-- Build the design from the top module. -/
def buildDesign (B : Bands) (top : Json) : Except String Built := do
  let ports := jobj ((jget top "ports").getD Json.null)
  let cells := jobj ((jget top "cells").getD Json.null)
  let netnames := jobj ((jget top "netnames").getD Json.null)
  -- a display name per net bit (prefer visible names)
  let mut nm : List (Nat × String) := []
  for (n, v) in netnames do
    let hide := ((jget v "hide_name").bind jnat).getD 0
    let bs ← bitsOf ((jget v "bits").getD (Json.arr #[]))
    let w := bs.length
    for (b, i) in bs.zip (List.range w) do
      match b with
      | .net k =>
          let s := if w == 1 then n else s!"{n}[{i}]"
          match nm.lookup k with
          | none => nm := (k, s) :: nm
          | some _ => if hide == 0 then nm := (k, s) :: nm.filter (·.1 != k)
      | _ => pure ()
  let nameOf (k : Nat) : String := (nm.lookup k).getD s!"net{k}"
  -- input ports, and the drivers of nets
  let mut inBits : List (String × Nat) := []
  let mut drivers : List (Nat × (String × String)) := []
  for (pn, pv) in ports do
    let dir := ((jget pv "direction").bind (·.getStr?.toOption)).getD ""
    let bs ← bitsOf ((jget pv "bits").getD (Json.arr #[]))
    if dir == "input" then
      for (b, i) in bs.zip (List.range bs.length) do
        match b with
        | .net k =>
            inBits := ((if bs.length == 1 then pn else s!"{pn}[{i}]"), k) :: inBits
            drivers := (k, ("<port>", pn)) :: drivers
        | _ => pure ()
  for (cn, cv) in cells do
    let conns := jobj ((jget cv "connections").getD Json.null)
    let dirs := jobj ((jget cv "port_directions").getD Json.null)
    for (pin, bj) in conns do
      let dir := ((dirs.lookup pin).bind (·.getStr?.toOption)).getD ""
      if dir == "output" then
        for b in (← bitsOf bj) do
          match b with
          | .net k =>
              if let some o := drivers.lookup k then
                throw s!"net {nameOf k} has two drivers: {o.1}.{o.2} and {cn}.{pin}"
              drivers := (k, (cn, pin)) :: drivers
          | _ => pure ()
  let prog : M Unit := do
    -- input nets first, so their wires have low indices
    for (_, k) in inBits.reverse do
      let _ ← netWire k (nameOf k)
    for (cn, cv) in cells do
      let ty := ((jget cv "type").bind (·.getStr?.toOption)).getD ""
      let conns := jobj ((jget cv "connections").getD Json.null)
      let one (pin : String) : M Bit := do
        match conns.lookup pin with
        | none => throw s!"cell {cn} ({ty}): pin {pin} not connected"
        | some bj =>
            match ← liftM (bitsOf bj) with
            | [b] => pure b
            | _ => throw s!"cell {cn}: pin {pin} is not 1 bit"
      -- the wire a pin reads: constant, or a routed arc from its net
      let pinWire (pin : String) : M Nat := do
        match ← one pin with
        | .c0 => pure 0
        | .c1 => pure 1
        | .cx => throw s!"cell {cn}: pin {pin} tied to x/z"
        | .net k =>
            if (drivers.lookup k).isNone then
              throw s!"cell {cn}: pin {pin} reads net {nameOf k}, which has no driver"
            let nw ← netWire k (nameOf k)
            let pw ← newWire s!"{cn}/{pin}"
            let own := (drivers.lookup k).any (fun o => o.1 == cn)
            let dflt := if own then B.feedback.getD B.route else B.route
            let (lo, hi) ← bandFor B s!"{cn}/{pin}" dflt B.arcs
            addGate { name := s!"{cn}/{pin}", k := 1, init := 2, ins := [nw], out := pw, lo := lo, hi := hi }
              { kind := "route", cell := cn, pin := pin }
            pure pw
      let outWire (pin : String) : M Nat := do
        match ← one pin with
        | .net k => netWire k (nameOf k)
        | _ => throw s!"cell {cn}: output {pin} is a constant"
      if ty == "$scopeinfo" then
        pure ()
      else if let some k := lutArity ty then
        let initS := ((jget ((jget cv "parameters").getD Json.null) "INIT").bind
          (·.getStr?.toOption)).getD ""
        let init ← liftM (binStr initS)
        let ins ← (List.range k).mapM (fun i => pinWire s!"I{i}")
        let o ← outWire "O"
        let (lo, hi) ← bandFor B cn B.lut B.cells
        addGate { name := s!"{cn}/O", k := k, init := init % 2 ^ 2 ^ k, ins := ins, out := o, lo := lo, hi := hi }
          { kind := "lut", cell := cn, pin := "O" }
      else if ty == "LUT6_2" then
        let initS := ((jget ((jget cv "parameters").getD Json.null) "INIT").bind
          (·.getStr?.toOption)).getD ""
        let init ← liftM (binStr initS)
        let ins ← (List.range 6).mapM (fun i => pinWire s!"I{i}")
        let o6 ← outWire "O6"
        let o5 ← outWire "O5"
        let (lo6, hi6) ← bandFor B s!"{cn}/O6" B.lut B.cells
        let (lo5, hi5) ← bandFor B s!"{cn}/O5" B.lut B.cells
        addGate { name := s!"{cn}/O6", k := 6, init := init % 2 ^ 64, ins := ins, out := o6, lo := lo6, hi := hi6 } { kind := "lut", cell := cn, pin := "O6" }
        addGate { name := s!"{cn}/O5", k := 5, init := init % 2 ^ 32, ins := ins.take 5, out := o5, lo := lo5, hi := hi5 } { kind := "lut", cell := cn, pin := "O5" }
      else if isPad ty then
        let i ← match ← one "I" with
          | .net k => netWire k (nameOf k)
          | .c0 => pure 0
          | .c1 => pure 1
          | .cx => throw s!"pad {cn}: input x"
        let o ← outWire "O"
        addGate { name := s!"{cn}/O", k := 1, init := 2, ins := [i], out := o, lo := B.pad.1, hi := B.pad.2 } { kind := "pad", cell := cn, pin := "O" }
      else if isFF ty then
        throw s!"cell {cn}: {ty} is clocked/hard storage; xaudit models LUTs, routes and pads only (no clock, setup/hold or BRAM/DSP model)"
      else
        throw s!"cell {cn}: unsupported cell type {ty}"
  let ((), s) ← prog.run {}
  -- storage: a LUT one of whose pins is routed from its own output net
  let mut info := s.info
  let gates := s.gates
  for i in [0:gates.size] do
    let g := gates[i]!
    if info[i]!.kind == "lut" then
      let selfFb := g.ins.any (fun pw =>
        gates.any (fun r => r.out == pw && r.ins == [g.out]))
      if selfFb then info := info.set! i { info[i]! with storage := true }
  let inputs := inBits.reverse.filterMap (fun (n, k) => (s.netW.lookup k).map (n, ·))
  pure { d := { m := s.nw - 1, gates := gates.toList }, info, wname := s.names,
         inputs, raised := s.raised.reverse, unit := B.unit }

/-! ## Inertial gate channels (probe XInert, additive; `formal/notes/A-xinert.md`)

Optional. A gate may be an inertial channel with rejection window `ρ` ps
(`DelayInertial.BoundedInertial ρ L H`). `XSimChanReal.boundedInertial_chanCells`
covers it with step band `[lo, hi]` iff (`inertial_wide_not_chanCells`)
`ρ ≤ (hi + 1 - lo) · unit`. `widenHi` is the least `hi' ≥ hi` meeting that;
`XAudit.SoundInertial` proves the widened design's verdicts sound. With `ρ = 0`
nothing changes (`SoundInertial.widenHi_zero`). Nothing here is used unless
the executable is given `--inertial`. -/

/-- A rejection window: a number of ps, or `delay` = the gate's own delay
(Verilog/iverilog default inertial: reject limit = path delay), taken at its
largest value, the band's `hi` in ps. -/
inductive RhoSpec where
  | ps (n : Nat)
  | delay
  deriving Repr, BEq, Inhabited

def RhoSpec.val : RhoSpec → Nat → Nat
  | .ps n, _ => n
  | .delay, H => H

def RhoSpec.show : RhoSpec → String
  | .ps n => s!"{n} ps"
  | .delay => "delay"

/-- Rejection windows per gate kind, with per-cell / per-arc overrides (same keys
as `Bands.cells` / `Bands.arcs`). Pads are always transport. -/
structure Inert where
  lut : RhoSpec := .ps 0
  route : RhoSpec := .ps 0
  feedback : Option RhoSpec := none
  cells : List (String × RhoSpec) := []
  arcs : List (String × RhoSpec) := []

def rhoOf (j : Json) : Option RhoSpec :=
  match j.getStr? with
  | .ok "delay" => some .delay
  | _ => (jnat j).map .ps

/-- The `inertial` entry of a band file: a number / `"delay"` (every LUT and
route), or `{lut, route, feedback, cells{}, arcs{}}`. Absent: all 0. -/
def parseInert (j : Json) : Inert :=
  match jget j "inertial" with
  | none => {}
  | some ij =>
      match rhoOf ij with
      | some r => { lut := r, route := r }
      | none =>
          { lut := ((jget ij "lut").bind rhoOf).getD (.ps 0)
            route := ((jget ij "route").bind rhoOf).getD (.ps 0)
            feedback := (jget ij "feedback").bind rhoOf
            cells := ((jget ij "cells").map jobj).getD [] |>.filterMap (fun (k, v) => (rhoOf v).map (k, ·))
            arcs := ((jget ij "arcs").map jobj).getD [] |>.filterMap (fun (k, v) => (rhoOf v).map (k, ·)) }

/-- The least `hi' ≥ hi` with `ρ ≤ (hi' + 1 - lo) · u`: `max hi (lo + ⌈ρ/u⌉ - 1)`. -/
def widenHi (u lo hi ρ : Nat) : Nat := max hi (lo + (ρ + u - 1) / u - 1)

def widenGate (u : Nat) (g : GSpec) (ρ : Nat) : GSpec := { g with hi := widenHi u g.lo g.hi ρ }

/-- The design the executable simulates under `--inertial`: gate `g` with window
`ρ` gets `hi := widenHi u g.lo g.hi ρ`. -/
def widenD (u m : Nat) (ps : List (GSpec × Nat)) : Design :=
  { m := m, gates := ps.map (fun p => widenGate u p.1 p.2) }

/-- First-match lookup table of an association list (as `List.lookup`). -/
def tbl {α : Type} (l : List (String × α)) : Std.HashMap String α :=
  l.reverse.foldl (fun m (k, v) => m.insert k v) {}

/-- Apply the inertial windows: the widened `Built` (same wires, names, storage
flags; only `hi` changes) and the list of widened gates `(name, lo, hi, hi', ρ)`.
The ps band and window of each gate are reconstructed from the band file exactly
as `buildDesign` chose the band (LUT: key `cell` or `cell/O6|O5`; route: key
`cell/pin`, own-feedback default when the arc's net is driven by the same cell);
pads keep `ρ = 0`. Fails if a reconstructed band does not round to the gate's step
band. -/
def applyInertial (B : Bands) (I : Inert) (bt : Built) :
    Except String (Built × List (String × Nat × Nat × Nat × Nat)) := do
  let gs := bt.d.gates.toArray
  let bc := tbl B.cells
  let ba := tbl B.arcs
  let ic := tbl I.cells
  let ia := tbl I.arcs
  -- the cell driving each wire (LUT outputs only)
  let mut drv : Array String := Array.replicate bt.d.n ""
  for j in [0:gs.size] do
    if bt.info[j]!.kind == "lut" && gs[j]!.out < drv.size then
      drv := drv.set! gs[j]!.out bt.info[j]!.cell
  let mut rs : Array Nat := #[]
  let mut ch := []
  for i in [0:gs.size] do
    let g := gs[i]!
    let inf := bt.info[i]!
    let pr : Option (String × (Nat × Nat) × Nat) :=
      if inf.kind == "lut" then
        let key := if inf.pin == "O" then inf.cell else s!"{inf.cell}/{inf.pin}"
        let b := bc.getD key B.lut
        some (key, b, (ic.getD key I.lut).val b.2)
      else if inf.kind == "route" then
        let key := s!"{inf.cell}/{inf.pin}"
        let own := drv[g.ins.headD 0]?.getD "" == inf.cell
        let b := ba.getD key (if own then B.feedback.getD B.route else B.route)
        some (key, b, (ia.getD key (if own then I.feedback.getD I.route else I.route)).val b.2)
      else none
    match pr with
    | none => rs := rs.push 0
    | some (key, b, r) =>
        let (lo, hi, _) := toSteps B.unit b
        if lo != g.lo || hi != g.hi then
          throw s!"inertial: band reconstruction mismatch on {g.name} (key {key}): {b} ps -> [{lo},{hi}], gate has [{g.lo},{g.hi}]"
        rs := rs.push r
        let h' := widenHi B.unit g.lo g.hi r
        if h' != g.hi then ch := (g.name, g.lo, g.hi, h', r) :: ch
  let d' := widenD B.unit bt.d.m (bt.d.gates.zip rs.toList)
  pure ({ bt with d := d' }, ch.reverse)

/-! ## Command line and file helpers -/

def getArg (args : List String) (k : String) : Option String :=
  match args.dropWhile (· != k) with
  | _ :: v :: _ => some v
  | _ => none

def readJson (p : String) : IO Json := do
  match Json.parse (← IO.FS.readFile p) with
  | .ok j => pure j
  | .error e => throw (IO.userError s!"{p}: {e}")

def pickTop (j : Json) (top? : Option String) : Except String (String × Json) := do
  let mods := jobj ((jget j "modules").getD Json.null)
  match top? with
  | some t => match mods.lookup t with
      | some m => pure (t, m)
      | none => throw s!"no module {t}"
  | none =>
      let tops := mods.filter (fun (_, m) =>
        match (jget m "attributes").bind (jget · "top") with
        | some v => match v.getStr? with
            | .ok s => s.any (· == '1')
            | .error _ => (v.getNat?.toOption.getD 0) != 0
        | none => false)
      match tops, mods with
      | [t], _ => pure t
      | _, [t] => pure t
      | _, _ => throw "several modules and no unique top attribute: use --top"

end Formal.Core.XAudit.Parse
