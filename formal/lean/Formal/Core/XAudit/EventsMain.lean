import Lean.Data.Json
import Formal.Core.XAudit.EventsDesign

/-!
# `xevents` — counter-domain (event) check of closed Muller networks (executable main)

    xevents NETLIST.json [--top T] [--bands BANDS.json]

Probe A-events. TRUSTED (not proved): the parser (a VERBATIM copy of
`Formal.Core.XAudit.Main`'s `buildDesign`/`parseBands`, copied because that
module defines `main` and cannot be imported by another executable; the lead
may factor it into a shared module), the recogniser `recognise`, and the
report. What is NOT trusted: the recogniser's output is re-checked by the
proved-decidable `Recog` (compiled `decide`), and `Pairing` and `Race` are
evaluated by their `Decidable` instances. When all three hold, the printed
verdict is `Events.design_safe`: every behaviour of the parsed netlist (all
delays in the parsed bands, any power-up, reset released once) has every
C-element node equal to its reset value flipped `M t j` times, at every time:
no X, no glitch, ever.

The event-spacing bounds printed per node are the max cycle ratio of the
counter graph (sum of LUT+route delays / tokens on each simple cycle). That
number is COMPUTED, not proved, except for ring3 where `EventsRing` proves
`[3d, 3D]` and `EventsDesign.Ring3D.ring3_design` proves it on the parsed
netlist.
-/

namespace Formal.Core.XAudit.EventsMain

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


/-! ## Muller recognition and report (events) -/

def c2n : Nat := 0x00B200B200B200B2
def c2nSet : Nat := 0xFFB2FFB2FFB2FFB2

def bufOf (gs : List GSpec) (w : Nat) : Option GSpec :=
  gs.find? (fun g => g.out == w && g.k == 1 && g.init == 2 && g.ins.length == 1)

/-- Simple cycles of the counter graph (edge `src j p → j`), by DFS from each
smallest node; returns, per cycle, (Σ lo, Σ hi, Σ tokens). -/
partial def cycles (N : Nat) (edges : List (Nat × Nat × Nat × Nat × Nat)) : List (Nat × Nat × Nat) :=
  -- edges: (from, to, lo, hi, tok)
  let rec go (s cur : Nat) (seen : List Nat) (lo hi tok : Nat) : List (Nat × Nat × Nat) :=
    edges.foldl (fun acc (a, b, l, h, k) =>
      if a != cur then acc
      else if b == s then (lo + l, hi + h, tok + k) :: acc
      else if b < s || seen.contains b then acc
      else acc ++ go s b (b :: seen) (lo + l) (hi + h) (tok + k)) []
  (List.range N).flatMap (fun s => go s s [s] 0 0 0)

def fmtRatio (num den : Nat) : String :=
  if den == 0 then "inf" else s!"{num / den}.{(num * 10 / den) % 10}"

def runEvents (args : List String) : IO UInt32 := do
  let some netf := args.head? | IO.eprintln "usage: xevents NETLIST.json [--top T] [--bands B.json]"; return 2
  let j ← readJson netf
  let B ← match getArg args "--bands" with
    | some p => pure (parseBands (← readJson p))
    | none => pure ({} : Bands)
  let (tname, top) ← IO.ofExcept (pickTop j (getArg args "--top"))
  let bt ← IO.ofExcept (buildDesign B top)
  let d := bt.d
  let u := bt.unit
  if !d.wfB then IO.eprintln "xevents: design not well formed"; return 1
  let gs := d.gates
  let luts := gs.filter (fun g => g.k == 6 && (g.init == c2n || g.init == c2nSet) &&
    g.ins.length == 6 && g.ins.getD 4 99 == 0 && g.ins.getD 5 99 == 0)
  let N := luts.length
  IO.println s!"xevents: {netf} top {tname}: {d.n} wires, {gs.length} gates; {N} C-element stages (bd_c2n / bd_c2n_set INIT on [a, b, q, rst, 0, 0])"
  IO.println s!"bands: 1 step = {u} ps"
  if hN : N = 0 then IO.println "no C-element stage: nothing to check"; return 0
  else
  have hN' : 0 < N := Nat.pos_of_ne_zero hN
  let idxOf (w : Nat) : Option Nat := luts.findIdx? (fun g => g.out == w)
  let fin (i : Nat) : Fin N := ⟨i % N, Nat.mod_lt _ hN'⟩
  -- recognise every stage's four pin buffers
  let mut srcs : Array (Nat × Nat) := #[]
  let mut pinGs : Array (GSpec × GSpec × GSpec × GSpec) := #[]
  let mut rstW : Option Nat := none
  let mut errs : List String := []
  for g in luts do
    let w := fun i => g.ins.getD i 0
    match bufOf gs (w 0), bufOf gs (w 1), bufOf gs (w 2), bufOf gs (w 3) with
    | some ga, some gb, some gq, some gr =>
        let ia := ga.ins.getD 0 0
        let ib := gb.ins.getD 0 0
        match idxOf ia, idxOf ib with
        | some ka, some kb =>
            if gq.ins.getD 0 0 != g.out then errs := s!"{g.name}: I2 is not routed from its own output" :: errs
            let r := gr.ins.getD 0 0
            if rstW.isSome && rstW != some r then errs := s!"{g.name}: I3 reads a different reset wire" :: errs
            rstW := some r
            srcs := srcs.push (ka, kb)
            pinGs := pinGs.push (ga, gb, gq, gr)
        | _, _ => errs := s!"{g.name}: I0/I1 reads wire {bt.wname[ia]?.getD "?"} / {bt.wname[ib]?.getD "?"}, not a C-element node (environment port?): not a closed Muller network" :: errs
    | _, _, _, _ => errs := s!"{g.name}: a pin is not a routed arc" :: errs
  if !errs.isEmpty then
    for e in errs.reverse do IO.println s!"  NOT RECOGNISED {e}"
    IO.println "VERDICT: not a closed Muller network of bd_c2n stages; the counter domain (Events.design_safe) does not apply as is (an open pipe needs an environment model: see formal/notes/A-events.md)"
    return 3
  let some rw := rstW | return 3
  let lutsA := luts.toArray
  let net : Events.MNet N := { v := fun j => (lutsA[j.val]!).init == c2nSet,
                               src := fun j p => fin (if p then (srcs[j.val]!).2 else (srcs[j.val]!).1) }
  let sm : Events.SMap N := {
    lut := fun j => lutsA[j.val]!
    pinG := fun j p => if p then (pinGs[j.val]!).2.1 else (pinGs[j.val]!).1
    fbG := fun j => (pinGs[j.val]!).2.2.1
    rG := fun j => (pinGs[j.val]!).2.2.2
    rst := rw }
  let recog := decide (Events.Recog d net sm)
  let pair := decide net.Pairing
  let race := decide (Events.Race net sm.bands)
  let bd := sm.bands
  for jj in List.range N do
    let j := fin jj
    let g := lutsA[jj]!
    IO.println s!"  stage {jj} {g.name} (wire {g.out} '{bt.wname[g.out]?.getD "?"}', reset {if net.v j then 1 else 0}): a <- stage {(net.src j false).val}, b <- stage {(net.src j true).val}; LUT [{bd.loF j * u},{bd.hiF j * u}] ps, own feedback [{bd.loQ j * u},{bd.hiQ j * u}] ps"
    for p in [false, true] do
      let k := net.src j p
      for p' in [false, true] do
        if net.src k p' == j then
          let rt := bd.loG j p + bd.loF k + bd.loG k p'
          IO.println s!"    race via {if p then "b" else "a"} -> stage {k.val} -> back: fastest round trip {rt * u} ps vs own feedback max {bd.hiQ j * u} ps: margin {(Int.ofNat rt - Int.ofNat (bd.hiQ j)) * u} ps"
  IO.println s!"Recog (proved-decidable, re-checks the recogniser): {recog}"
  IO.println s!"Pairing (handshake structure): {pair}"
  IO.println s!"Race (feedback <= fastest neighbour round trip, every pin): {race}"
  -- counter graph cycles (untrusted arithmetic, report only)
  let edges := (List.range N).flatMap (fun jj => [false, true].map (fun p =>
    let j := fin jj
    ((net.src j p).val, jj, bd.loF j + bd.loG j p, bd.hiF j + bd.hiG j p, net.off j p)))
  let cs := cycles N edges
  let zero := cs.filter (fun c => c.2.2 == 0)
  let best := cs.foldl (fun (acc : Nat × Nat × Nat × Nat) (lo, hi, tok) =>
    if tok == 0 then acc else
    let (alo, atok, ahi, ahtok) := acc
    let acc1 := if lo * atok > alo * tok then (lo, tok) else (alo, atok)
    let acc2 := if hi * ahtok > ahi * tok then (hi, tok) else (ahi, ahtok)
    (acc1.1, acc1.2, acc2.1, acc2.2)) (0, 1, 0, 1)
  IO.println s!"counter graph: {cs.length} simple cycles, {zero.length} with no token"
  if !zero.isEmpty then IO.println "  a token-free cycle: that loop can never fire (dead)"
  IO.println s!"event spacing per node (max cycle ratio, COMPUTED not proved except ring3): [{fmtRatio (best.1 * u) best.2.1}, {fmtRatio (best.2.2.1 * u) best.2.2.2}] ps; period (two events) twice that"
  if recog && pair && race then
    IO.println "VERDICT: CLEAN FOREVER. Events.design_safe: every behaviour (every delay in the bands, any power-up, reset released once) has every C-element node = reset value flipped M t j times at every time, M the counter recursion: no X, no glitch, no stored X, for all time."
    return 0
  else
    IO.println "VERDICT: NOT PROVED (a hypothesis of Events.design_safe fails; see above). This is not a hazard report: run xaudit for the X-window audit."
    return 1

end Formal.Core.XAudit.EventsMain

def main (args : List String) : IO UInt32 := Formal.Core.XAudit.EventsMain.runEvents args
