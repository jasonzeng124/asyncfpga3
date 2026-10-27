import Lean.Data.Json
import Formal.Core.XAudit.Parse
import Formal.Core.XAudit.Design
import Formal.Core.XAudit.Untimed
import Formal.Core.XAudit.Fast

/-!
# `xaudit` — whole-design X/hazard audit (executable main)

    xaudit NETLIST.json [--top T] [--bands BANDS.json] [--stim STIM.json]
           [--all] [--emit-lean]

TRUSTED (not proved): everything in this file and in `Parse.lean` (the
shared yosys-JSON parser). It parses the yosys JSON, the
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
open Formal.Core.XAudit.Parse

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
