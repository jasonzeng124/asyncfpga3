import Lean.Data.Json
import Formal.Core.XAudit.Design
import Formal.Core.XAudit.Untimed
import Formal.Core.XAudit.Fast

/-!
# `xaudit` — whole-design X/hazard audit (executable main)

    xaudit NETLIST.json [--top T] [--bands BANDS.json] [--stim STIM.json]
           [--all] [--emit-lean]

TRUSTED (not proved): everything in this file. It parses the yosys JSON, the
band file and the stimulus into a `Design` and a `Stim`, calls the PROVED
functions `Formal.Core.XAudit.Fast.auditF` (proved equal to `XSim.val`,
`Fast.auditF_eq`; `--kernel-sim` calls `audit` = `XSim.hist` itself and
`--crosscheck` runs both and compares every value), `rowsFixedF`,
`Untimed.runA`/`runB` (= `Ternary.iterA`/`iterB`), and prints what they
return. What the printed verdicts mean is stated by `audit_binary`,
`noX_sound`, `settled_forever`, `untimed_noGlitch` and `untimed_settles`.
Compiled code is trusted to agree with the kernel definitions (the Lean
compiler, not the kernel, runs it). See `formal/notes/A-xaudit.md`.
-/

namespace Formal.Core.XAudit.Main

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

def bandFor (B : Bands) (key : String) (dflt : Nat × Nat) (alts : List (String × (Nat × Nat))) :
    M (Nat × Nat) := do
  let b := (alts.lookup key).getD dflt
  let (lo, hi, r) := toSteps B.unit b
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

/-! ## Stimulus -/

def k3OfJson (j : Json) : Option K3 :=
  match j.getNat? with
  | .ok 0 => some .zero
  | .ok 1 => some .one
  | _ => match j.getStr? with
    | .ok "x" => some .X
    | .ok "X" => some .X
    | _ => none

/-- Assignments of one `set` object: port name or `port[i]`; a bus takes an
integer (bit i = value bit i) or "x". -/
def assigns (bt : Built) (o : Json) : Except String (List (Nat × K3)) := do
  let mut r := []
  for (k, v) in jobj o do
    match bt.inputs.lookup k with
    | some w =>
        match k3OfJson v with
        | some x => r := (w, x) :: r
        | none => throw s!"bad value for {k}: {v.compress}"
    | none =>
        let bits := bt.inputs.filter (fun (n, _) => n.startsWith (k ++ "["))
        if bits.isEmpty then throw s!"stimulus names unknown input {k}"
        for (n, w) in bits do
          let idx := ((n.drop (k.length + 1)).takeWhile Char.isDigit).toNat!
          match v.getNat? with
          | .ok val => r := (w, if val.testBit idx then .one else .zero) :: r
          | .error _ =>
              match k3OfJson v with
              | some .X => r := (w, .X) :: r
              | _ => throw s!"bad value for bus {k}: {v.compress}"
  pure r.reverse

structure StimIn where
  st : Stim
  horizon : Nat
  /-- (step, assignments) per event group, for the untimed phases. -/
  groups : List (Nat × List (Nat × K3))

def parseStim (bt : Built) (j : Json) : Except String StimIn := do
  let u := bt.unit
  let hz := ((jget j "horizon_ps").bind jnat).getD 20000
  let init ← assigns bt ((jget j "init").getD (Json.mkObj []))
  let evs := ((jget j "events").bind (·.getArr?.toOption)).getD #[]
  let mut gs := []
  for e in evs do
    let tps := ((jget e "t_ps").bind jnat).getD 0
    if tps % u != 0 then throw s!"event time {tps} ps is not a multiple of unit {u} ps"
    let a ← assigns bt ((jget e "set").getD (Json.mkObj []))
    gs := (tps / u, a) :: gs
  let groups := gs.reverse
  let events := groups.flatMap (fun (t, a) => a.map (fun (w, v) => (t, w, v)))
  let consts := [(0, K3.zero), (1, K3.one)]
  pure { st := { init := consts ++ init, events }, horizon := hz / u, groups }

/-! ## Report -/

def k3s : K3 → String
  | .zero => "0" | .one => "1" | .X => "X"

/-- Maximal runs of equal values in a column. -/
def runs (col : List K3) : List (Nat × Nat × K3) :=
  let rec go (l : List K3) (i : Nat) (acc : List (Nat × Nat × K3)) : List (Nat × Nat × K3) :=
    match l, acc with
    | [], _ => acc.reverse
    | v :: l, (s, _, v') :: acc' => if v == v' then go l (i + 1) ((s, i, v) :: acc')
        else go l (i + 1) ((i, i, v) :: (s, i - 1, v') :: acc')
    | v :: l, [] => go l (i + 1) [(i, i, v)]
  go col 0 []

def tps (u t : Nat) : String := s!"{t * u}"

/-- Classify the X runs of a storage column. `xmax`: an X window longer than this many steps between two different
values is reported as a possible stored X, not as a transition (presentation
only: every X is printed). -/
def classify (u : Nat) (T xmax : Nat) (col : List K3) : List String × Nat := Id.run do
  let rs := runs col
  let mut out := []
  let mut bad := 0
  for i in [0:rs.length] do
    let (s, e, v) := rs[i]!
    if v == .X then
      let prev := if i == 0 then none else some (rs[i-1]!.2.2)
      let next := if i + 1 < rs.length then some (rs[i+1]!.2.2) else none
      let w := s!"[{tps u s}, {tps u e}] ps"
      match prev, next with
      | none, some _ => out := out ++ [s!"    X {w}: power-up, resolved at {tps u (e+1)} ps"]
      | none, none =>
          out := out ++ [s!"    X {w}: power-up, NEVER RESOLVED (to the horizon {tps u T} ps)"]
          bad := bad + 1
      | some p, none =>
          out := out ++ [s!"    X {w}: after {k3s p}, UNRESOLVED to the horizon: X cannot be excluded"]
          bad := bad + 1
      | some p, some q =>
          if p == q then
            out := out ++ [s!"    X {w}: {k3s p} -> X -> {k3s q}: POSSIBLE GLITCH (static hazard not excluded)"]
            bad := bad + 1
          else if e + 1 - s > xmax then
            out := out ++ [s!"    X {w}: {k3s p} -> X -> {k3s q}, {(e + 1 - s) * u} ps long (> --xmax): STORED X POSSIBLE, value undetermined for the whole window"]
            bad := bad + 1
          else out := out ++ [s!"    X {w}: transition {k3s p} -> {k3s q} ({(e + 1 - s) * u} ps of timing uncertainty)"]
  pure (out, bad)

def changed (a b : Nat → Bool) (ws : List (String × Nat)) : List String :=
  ws.filterMap (fun (n, w) => if a w != b w then some s!"{n}{if b w then "+" else "-"}" else none)

def tk (v : Formal.Core.Ternary.K3) : String :=
  match v with | .zero => "0" | .one => "1" | .X => "X"

/-! ## Lean literal (for the kernel cross-check) -/

def emitLean (bt : Built) (si : StimIn) : String :=
  let g2s (g : GSpec) := s!"⟨{repr g.name}, {g.k}, {g.init}, {g.ins}, {g.out}, {g.lo}, {g.hi}⟩"
  let gs := ",\n    ".intercalate (bt.d.gates.map g2s)
  let kv (v : K3) := match v with | .zero => ".zero" | .one => ".one" | .X => ".X"
  let ini := ", ".intercalate (si.st.init.map (fun (w, v) => s!"({w}, {kv v})"))
  let evs := ", ".intercalate (si.st.events.map (fun (t, w, v) => s!"({t}, {w}, {kv v})"))
  s!"def design : Design := ⟨{bt.d.m}, [\n    {gs}]⟩\n\ndef stim : Stim := ⟨[{ini}],\n  [{evs}]⟩\n\ndef horizon : Nat := {si.horizon}\n"

/-! ## Main -/

def usage : String :=
  "usage: xaudit NETLIST.json [--top T] [--bands BANDS.json] [--stim STIM.json] [--xmax PS] [--all] [--emit-lean] [--kernel-sim | --crosscheck] [--timed-only]"

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

def run (args : List String) : IO UInt32 := do
  let some net := args.head? | IO.eprintln usage; return 2
  let all := args.contains "--all"
  let j ← readJson net
  let B ← match getArg args "--bands" with
    | some p => pure (parseBands (← readJson p))
    | none => pure ({} : Bands)
  let (tname, top) ← IO.ofExcept (pickTop j (getArg args "--top"))
  let bt ← IO.ofExcept (buildDesign B top)
  let sj ← match getArg args "--stim" with
    | some p => readJson p
    | none => pure (Json.mkObj [])
  let si ← IO.ofExcept (parseStim bt sj)
  let d := bt.d
  let u := bt.unit
  let xmax := (((getArg args "--xmax").bind String.toNat?).getD 2000) / u
  if !d.wfB then
    IO.eprintln "xaudit: design not well formed (Design.WF failed)"; return 1
  if args.contains "--emit-lean" then
    IO.println (emitLean bt si); return 0
  let ng := d.gates.length
  let nl := (bt.info.toList.filter (·.kind == "lut")).length
  let nr := (bt.info.toList.filter (·.kind == "route")).length
  let stor := (List.range ng).filter (fun i => bt.info[i]!.storage)
  IO.println s!"xaudit: {net} top {tname}: {d.n} wires, {ng} gates ({nl} LUT outputs, {nr} routed arcs), {stor.length} storage nodes (LUTs with own feedback)"
  IO.println s!"bands: 1 step = {u} ps; LUT {B.lut} ps, route {B.route} ps, own feedback {B.feedback.getD B.route} ps (defaults unless overridden: {B.cells.length} cell, {B.arcs.length} arc entries); pads {B.pad} steps"
  if !bt.raised.isEmpty then
    IO.println s!"  NOTE lo < 1 step raised to 1 step (sub-unit delay not modelled) on: {bt.raised}"
  IO.println s!"inputs: {bt.inputs.map (·.1)}"
  -- timed
  let T := si.horizon
  let ufun : Fin d.n → Nat → K3 := fun w t => si.st.u w t
  let kernelSim := args.contains "--kernel-sim"
  let HF := if kernelSim then #[] else Fast.auditF d ufun T
  let HL := if kernelSim || args.contains "--crosscheck" then audit d ufun T else []
  let col (w : Nat) : List K3 := (List.range (T + 1)).map (fun s =>
    if kernelSim then valAt HL T s w else Fast.valF HF s w)
  let fixed := if kernelSim then rowsFixed HL T d.maxHi else Fast.rowsFixedF HF T d.maxHi
  if args.contains "--crosscheck" then
    let mism := (List.range (T + 1)).flatMap (fun s => (List.range d.n).filterMap (fun w =>
      if valAt HL T s w == Fast.valF HF s w then none else some (s, w)))
    IO.println s!"crosscheck audit (XSim.hist) vs auditF: {mism.length} mismatches over {(T + 1) * d.n} values"
  let quiet := si.st.last + d.maxHi ≤ T
  IO.println s!"\nTIMED (XSim: {if kernelSim then "XAudit.audit = XSim.hist" else "Fast.auditF, = XSim.val by auditF_eq"}; horizon {T} steps = {T * u} ps; power-up all X)"
  IO.println s!"  end state: {if fixed && quiet then "FIXED POINT (inputs constant from " ++ tps u si.st.last ++ " ps, last " ++ toString (d.maxHi + 1) ++ " rows equal): binary values hold forever (settled_forever)" else "not a fixed point at the horizon"}"
  let mut totalBad := 0
  let shown := if all then (List.range ng).filter (fun i => bt.info[i]!.kind != "route") else stor
  for i in shown do
    let g := d.gates[i]!
    let c := col g.out
    let (lines, bad) := classify u T xmax c
    totalBad := totalBad + bad
    let fin := k3s (c.getLast?.getD .X)
    IO.println s!"  {if bt.info[i]!.storage then "STORAGE" else "node   "} {g.name} (wire {g.out} '{bt.wname[g.out]!}'): final {fin}, {bad} flagged"
    for l in lines do IO.println l
  -- untimed
  if args.contains "--timed-only" then
    IO.println s!"\nSUMMARY: timed: {totalBad} flagged X windows on {stor.length} storage nodes; untimed: not run"
    return (if totalBad == 0 then 0 else 3)
  IO.println s!"\nUNTIMED (Eichelberger A/B, Formal.Core.Ternary; any gate and wire delays)"
  let D := Untimed.drvTable d
  let N := Untimed.net d D
  let vec (as : List (Nat × K3)) : Option (Nat → Bool) :=
    if as.any (fun (_, v) => v == .X) then none
    else some (fun w => (as.reverse.lookup w) == some .one)
  let mut cur : List (Nat × K3) := si.st.init
  let mut r : Array Formal.Core.Ternary.K3 := Untimed.rowX d.n
  let mut prevA : Option (Nat → Bool) := vec cur
  let toB (f : Nat → Bool) : Fin d.n → Bool := fun w => f w.val
  let mut ok := true
  let mut untimedBad := 0
  let phases := (0, []) :: si.groups
  let mut idx := 0
  for (t, as) in phases do
    let nxt := cur ++ as
    match prevA, vec nxt with
    | some a, some b =>
        if !ok then
          IO.println s!"  phase {idx} @ {tps u t} ps: skipped (an earlier phase had X inputs)"
        else
          let ra := Untimed.runA N (toB a) (toB b) r
          let rb := Untimed.runB N (toB a) (toB b) r
          let ch := changed a b bt.inputs
          let mut flags := []
          let mut lines := []
          for i in stor do
            let w := d.gates[i]!.out
            let s0 := r[w]!
            let va := ra[w]!
            let vb := rb[w]!
            let f :=
              if vb == .X && s0 == .X then "X held (unknown since an earlier phase, e.g. an unwritten latch)"
              else if vb == .X then "NO SETTLE (B = X: final value not determined)"
              else if va == .X && s0 == vb && s0 != .X then "POSSIBLE STATIC HAZARD (A = X, start = end)"
              else if va == .X then "transition"
              else "stable (A binary: no glitch, any delays)"
            let isBad := s0 != .X && (vb == .X || (va == .X && s0 == vb))
            if isBad then flags := d.gates[i]!.name :: flags
            if isBad || all then
              lines := lines ++ [s!"    {d.gates[i]!.name}: start {tk s0} A {tk va} B {tk vb}: {f}"]
          IO.println s!"  phase {idx} @ {tps u t} ps: inputs {if idx == 0 then "held at init (power-up X state)" else toString ch}: {flags.length} of {stor.length} storage nodes flagged"
          untimedBad := untimedBad + flags.length
          for l in lines do IO.println l
          r := rb
    | _, _ =>
        IO.println s!"  phase {idx} @ {tps u t} ps: an input is X; the untimed algorithms need binary inputs, stopping"
        ok := false
    cur := nxt
    prevA := vec nxt
    idx := idx + 1
  IO.println s!"\nSUMMARY: timed: {totalBad} flagged X windows on {stor.length} storage nodes; untimed: {untimedBad} flagged (node, phase) pairs"
  return (if totalBad == 0 then 0 else 3)

end Formal.Core.XAudit.Main

def main (args : List String) : IO UInt32 := Formal.Core.XAudit.Main.run args
