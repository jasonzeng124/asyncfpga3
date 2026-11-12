import Lean.Data.Json
import Formal.Core.XAudit.Parse
import Formal.Core.XAudit.Events4

/-!
# `xevents4` — recognise the control skeleton of a ROUTED netlist from the real INITs (executable main)

    xevents4 NETLIST.json [--top T] [--bands BANDS.json]

Probe A-events4, W-E5c (netlist recognition). Input: a routed2x-style netlist
(every cell a LUTk over its USED PHYSICAL pins, INIT re-encoded to that pin
order), normally the control skeleton cut by `tools-A/xaudit/events4/skel.py`
(free inputs: `rig_rst` and the cut select nets `sel_*`).

What it does (TRUSTED code, no theorem): parses with `Parse.buildDesign`; for
every LUT gate finds, through its routed pin arcs, the net each physical pin
reads; then classifies, FROM THE INIT over all `2^k` addresses and with no
table of cell names:

* `cel`  — a LUT that reads its own output and `rig_rst`, and is
  `rst ? v : C(lit_1 .. lit_n, q)` for some pin polarities, where one literal
  may be `pin ∧ [select pins = pattern]` (bd_mux's folded steer). Any number
  of inputs, any physical pin order.
* `arb`  — a LUT that reads its own output and `rig_rst` but is not a
  C-element (the `bd_arbiter` state LUT): OUTSIDE the domain; the analysis
  replaces the arbiter core by the virtual mux core of hypothesis H_ARB.
* stateless: `buf`/`inv` (one live control pin), `steer` (one control pin AND a
  pattern of select pins: `bd_steer`'s LUT3/LUT6_2 halves, the 3-input mux
  decode), `and`/`or` (monotone, all control: FASTFALL/FASTRISE delay lines,
  acknowledge ORs, the mux request OR), `arbout` (reads an arbiter state:
  grant / merged request), anything else `OTHER` (unrecognised, exit 3).

The recognition is the part of W-E5c that the analysis (`ana.py`) also does;
this executable re-derives it in Lean so the two can be compared line by line
(`tools-A/xaudit/events4/recog_*.txt`). It does NOT check certificates; that,
and the theorem linking a recognised netlist to `Events4`'s lemmas
(`design_beh4`), is open (`Wip/Events4.lean`).
-/

namespace Formal.Core.XAudit.Events4Main

open Lean (Json)
open Formal.Core
open Formal.Core.XAudit
open Formal.Core.XAudit.Parse

/-- C-element spec on a pin-value assignment (physical pins). -/
def celSpec (rst q : Nat) (reqs : List (Nat × Bool)) (filt : Option (Nat × List (Nat × Bool)))
    (v : Bool) (val : Nat → Bool) : Bool :=
  if val rst then v else
    let lits := reqs.map fun (i, pol) =>
      let x := val i ^^ pol
      match filt with
      | some (fi, pat) => if fi == i then x && pat.all (fun (s, b) => val s == b) else x
      | none => x
    if lits.all id then true else if lits.all (! ·) then false else val q

/-- All assignments of `k` pins, as address numbers. -/
def addrs (k : Nat) : List Nat := List.range (2 ^ k)

def bitsOfList : List Bool → List (List Bool)
  | [] => [[]]
  | _ :: l => (bitsOfList l).flatMap fun r => [false :: r, true :: r]

/-- Does `init` (over `k` pins) equal the spec, on every address whose constant pins hold their constant? -/
def initMatches (k init : Nat) (consts : List (Nat × Bool)) (spec : (Nat → Bool) → Bool) : Bool :=
  (addrs k).all fun a =>
    let val : Nat → Bool := fun i => a.testBit i
    !(consts.all fun (i, b) => val i == b) || (init.testBit a == spec val)

structure Info where
  name : String
  k : Nat
  init : Nat
  out : Nat
  /-- per physical pin: the net wire it reads (`none` = constant `0`/`1`). -/
  nets : List (Option Nat)
  consts : List (Nat × Bool)

def pinsOf (b : Built) : List Info := Id.run do
  let gates := b.d.gates.toArray
  -- route gate output wire -> its net wire
  let mut pin2net : Std.HashMap Nat Nat := {}
  for i in [0:gates.size] do
    if b.info[i]!.kind == "route" then
      pin2net := pin2net.insert gates[i]!.out (gates[i]!.ins.headD 0)
  let mut out := []
  for i in [0:gates.size] do
    if b.info[i]!.kind == "lut" then
      let g := gates[i]!
      let nets := g.ins.map fun w => if w == 0 || w == 1 then none else pin2net.get? w
      let consts := (List.range g.k).filterMap fun p =>
        let w := g.ins.getD p 0
        if w == 0 then some (p, false) else if w == 1 then some (p, true) else none
      out := { name := b.info[i]!.cell, k := g.k, init := g.init, out := g.out, nets, consts } :: out
  return out.reverse

/-- Subsets as polarity / pattern vectors. -/
def allBools : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allBools n).flatMap fun r => [false :: r, true :: r]

def classifyCel (g : Info) (rstW : Nat) (isSel : Nat → Bool) : Option String := Id.run do
  let live := (List.range g.k).filter fun p => (g.nets.getD p none).isSome
  let net := fun p => (g.nets.getD p none).getD 0
  let rs := live.filter fun p => net p == rstW
  let qs := live.filter fun p => net p == g.out
  match rs, qs with
  | [r], [q] =>
    let others := live.filter fun p => p != r && p != q
    let sels := others.filter fun p => isSel (net p)
    let reqs := others.filter fun p => !isSel (net p)
    if reqs.isEmpty then return none
    for v in [false, true] do
      for pols in allBools reqs.length do
        let rq := reqs.zip pols
        let filts : List (Option (Nat × List (Nat × Bool))) :=
          if sels.isEmpty then [none] else
            reqs.flatMap fun fi => (allBools sels.length).map fun pat => some (fi, sels.zip pat)
        for f in filts do
          if initMatches g.k g.init g.consts (celSpec r q rq f v) then
            let fs := match f with
              | some (fi, pat) => s!" filtered-pin I{fi} by {pat.map (fun (sb : Nat × Bool) => s!"I{sb.1}={sb.2}")}"
              | none => ""
            let ps := rq.map (fun (ip : Nat × Bool) => (if ip.2 then "~" else "") ++ s!"I{ip.1}")
            return some s!"cel n={reqs.length} v={v} rst=I{r} q=I{q} pins={ps}{fs}"
    return none
  | _, _ => return none

def classifyGate (g : Info) (isCtl isSel isArbQ : Nat → Bool) : String := Id.run do
  let live := (List.range g.k).filter fun p => (g.nets.getD p none).isSome
  let net := fun p => (g.nets.getD p none).getD 0
  if live.any (fun p => isArbQ (net p)) then return "arbout"
  let ctl := live.filter fun p => isCtl (net p)
  let sel := live.filter fun p => isSel (net p)
  if ctl.length + sel.length != live.length then return "OTHER (reads a net that is neither control nor select)"
  match ctl, sel with
  | [c], [] =>
    if initMatches g.k g.init g.consts (fun val => val c) then return "buf"
    if initMatches g.k g.init g.consts (fun val => !val c) then return "inv"
    return "OTHER (1-input constant)"
  | [c], _ :: _ =>
    for pat in allBools sel.length do
      if initMatches g.k g.init g.consts (fun val => val c && (sel.zip pat).all fun (s, b) => val s == b) then
        return s!"steer pattern {pat}"
    return "OTHER (control x select, not a steer)"
  | _ :: _ :: _, [] =>
    if initMatches g.k g.init g.consts (fun val => ctl.all val) then return s!"and{ctl.length}"
    if initMatches g.k g.init g.consts (fun val => ctl.any val) then return s!"or{ctl.length}"
    return "OTHER (several control inputs, not AND/OR)"
  | _, _ => return "OTHER"

def run (args : List String) : IO UInt32 := do
  let path :: rest := args | do IO.eprintln "usage: xevents4 NETLIST.json [--top T] [--bands B.json]"; return 2
  let j ← readJson path
  let B : Bands ← match getArg rest "--bands" with
    | some p => pure (parseBands (← readJson p))
    | none => pure {}
  let (_, top) ← IO.ofExcept (pickTop j (getArg rest "--top"))
  let b ← IO.ofExcept (buildDesign B top)
  let infos := pinsOf b
  let rstW := (b.inputs.lookup "rig_rst").getD 0
  let selWs : Std.HashSet Nat := b.inputs.foldl (fun s (n, w) => if n.startsWith "sel_" then s.insert w else s) {}
  let isSel := fun w => selWs.contains w
  let lutOut : Std.HashSet Nat := infos.foldl (fun s g => s.insert g.out) {}
  -- stages
  let mut nCel := 0
  let mut nArb := 0
  let mut arbQ : Std.HashSet Nat := {}
  let mut lines : Array String := #[]
  for g in infos do
    let fb := g.nets.any (· == some g.out)
    let rd := g.nets.any (· == some rstW)
    if fb && rd then
      match classifyCel g rstW isSel with
      | some s => nCel := nCel + 1; lines := lines.push s!"STAGE {g.name}: {s}"
      | none => nArb := nArb + 1; arbQ := arbQ.insert g.out
                lines := lines.push s!"STAGE {g.name}: arb (not a C-element: outside the domain, H_ARB)"
  let isCtl := fun w => lutOut.contains w
  let mut cnt : List (String × Nat) := []
  let mut other : Array String := #[]
  for g in infos do
    let fb := g.nets.any (· == some g.out)
    if fb then continue
    let c := classifyGate g isCtl isSel (fun w => arbQ.contains w)
    let key := (c.splitOn " ").headD c
    cnt := match cnt.lookup key with
      | some n => (key, n + 1) :: cnt.filter (·.1 != key)
      | none => (key, 1) :: cnt
    if c.startsWith "OTHER" then other := other.push s!"{g.name}: {c}"
  for l in lines do IO.println l
  IO.println s!"SUMMARY {infos.length} LUT outputs; stages: cel {nCel}, arb {nArb}; stateless: {cnt.reverse}"
  for o in other do IO.println s!"UNRECOGNISED {o}"
  if other.isEmpty then
    IO.println "RECOGNISED: every LUT of the skeleton is a C-element stage, an arbiter state (H_ARB), or a buf/inv/steer/and/or/arbiter-output gate"
    return 0
  else
    return 3

end Formal.Core.XAudit.Events4Main

def main (args : List String) : IO UInt32 := Formal.Core.XAudit.Events4Main.run args
