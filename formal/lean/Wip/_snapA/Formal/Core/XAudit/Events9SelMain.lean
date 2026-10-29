import Lean.Data.Json
import Formal.Core.XAudit.Parse
import Formal.Core.XAudit.Events9SelSplit

/-!
# `xselhold` — check the select map and the hold rows of a ROUTED netlist (executable main)

    xselhold SKEL.json BANDS.json CERT.json MAP.json [--top T]

Probe E8SelC (shard A). Reads the same three inputs as `xevents9` (the control skeleton, its
band file, the certificate whose nodes give `Net4` / `Bands4` / `RNode`) with the SAME
parsers (copied below from `Events9Main`), plus the select map of `selhold/mkmap.py`.
Per REAL filtered pin `(j, p)` and select literal `i` it
* builds the `SelEnt` of the map entry (request / acknowledge wires from gate names, bus wires
  from input ports; the route gate `rg` and bus wire `dw` are found in the parsed netlist:
  the gate driving input `i` of `selGate`, and its input);
* evaluates **`entOK`** (Events9SelC);
* finds the shortest-low-end path `π` from the acknowledge wire down to the source node's
  output wire (Bellman-Ford over the parsed design; minimality NOT proved), evaluates
  **`chainOK`** and **`holdBand`** (Events9SelHold) and prints the hold margin of every copy
  (`holdMargin`): `plo π + selLo + lo(rg) - hiC - 1` ps.
* per copy, the junction-anchored row of `Events9SelSplit`: among the cuts `n` whose bottom
  part is a chain of 1-input buffers and whose junction wire `junW` the acknowledge reaches,
  the one with the best margin; the path from the acknowledge to `junW`, **`chainOK`** and
  **`holdBandS`** (margin `plo π + selLo + lo(rg) - (phi top - 1) - 1` ps). SELHOLD(split)
  CLEAN = every literal has `entOK` and passing split rows on every copy (the checked premises
  of `design_verdict9_selS`); SELHOLD(src) is the source-anchored `design_verdict9_selH` row.
Every map row is printed with its wire names, so the trusted name correspondence (C channel
name ↔ request / acknowledge / bus wires) can be read off.

What a row means: `design_verdict9_selH`'s checked premises `entOK ∧ chainOK ∧ holdBand`
hold for that literal. TRUSTED: the parsers, the map's channel names, the printed numbers,
and the Lean compiler. NOT checked here: `xevents9`'s own checks (run it on the same inputs).
-/

namespace Formal.Core.XAudit.Events9SelMain

open Lean (Json)
open Formal.Core
open Formal.Core.XAudit
open Formal.Core.XAudit.Parse
open Formal.Core.XAudit.Events5
open Formal.Core.XAudit.Events6
open Formal.Core.XAudit.Events7
open Formal.Core.XAudit.Events8
open Formal.Core.XAudit.Events9
open Formal.Core.XAudit.Events8Bridge
open Formal.Core.XAudit.Events9SelC
open Formal.Core.XAudit.Events9SelHold
open Formal.Core.XAudit.Events9SelSplit

/-! ## Certificate reader (copied verbatim from `Events9Main`) -/

structure PinD where
  src : Nat := 0
  inv : Bool := false
  neg : Bool := false
  pk : PK := PK.plain
  op : Bool := true
  grp : Nat := 0
  br : Bool := false
  gp : Nat := 0
  nc : Nat := 1
  rp : RPin := default
  lo : Array Nat := #[]
  hi : Array Nat := #[]
  deriving Inhabited

instance : Inhabited PK := ⟨PK.plain⟩

structure NodeD where
  name : String := ""
  v : Bool := false
  mg : Bool := false
  virt : Bool := false
  pins : Array PinD := #[]
  rn : RNode := { virt := false, ow := 0 }
  F : Nat × Nat := (1, 1)
  Q : Nat × Nat := (1, 1)
  deriving Inhabited

def gStr (j : Json) (k : String) : String := ((jget j k).bind (·.getStr?.toOption)).getD ""
def gNat (j : Json) (k : String) : Nat := ((jget j k).bind jnat).getD 0
def gBool (j : Json) (k : String) : Bool := ((jget j k).bind (·.getBool?.toOption)).getD false
def gArr (j : Json) (k : String) : Array Json := ((jget j k).bind (·.getArr?.toOption)).getD #[]

def parsePath (gix : Std.HashMap String Nat) (j : Json) : Except String Path := do
  let a ← j.getArr?
  a.toList.mapM fun e => do
    let ea ← e.getArr?
    let nm ← ea[0]!.getStr?
    let i ← ea[1]!.getNat?
    match gix.get? nm with
    | some gi => pure (gi, i)
    | none => throw s!"cert names gate {nm}, which the parsed netlist does not have"

def parseSel (j : Json) : List (Nat × Bool) :=
  match j.getArr? with
  | .ok a => a.toList.filterMap fun e => match e.getArr? with
      | .ok ea => match ea[0]!.getNat?, ea[1]!.getBool? with
        | .ok s, .ok b => some (s, b)
        | _, _ => none
      | .error _ => none
  | .error _ => []

def pkOf (s : String) : PK :=
  match s with
  | "multi" => PK.multi | "filt" => PK.filt | "guard" => PK.guard | _ => PK.plain

def parseNode (gix : Std.HashMap String Nat) (d : Design) (j : Json) : Except String NodeD := do
  let virt := gBool j "virt"
  let mut pins : Array PinD := #[]
  for pj in gArr j "pins" do
    let st := gBool pj "st"
    let rp : RPin ← if virt then pure default else do
      let paths ← (gArr pj "paths").toList.mapM (parsePath gix)
      let top ← parsePath gix ((jget pj "top").getD (Json.arr #[]))
      let bot ← parsePath gix ((jget pj "bot").getD (Json.arr #[]))
      let sg := (gix.get? (gStr pj "sg")).getD 0
      pure { ip := gNat pj "ip", fold := parseSel ((jget pj "fold").getD (Json.arr #[])), st, paths, top, sg,
             sci := gNat pj "sci", ssel := parseSel ((jget pj "ssel").getD (Json.arr #[])), bot }
    pins := pins.push
      { src := gNat pj "src", inv := gBool pj "inv", neg := gBool pj "neg", pk := pkOf (gStr pj "pk"),
        op := gBool pj "op", grp := gNat pj "grp", br := gBool pj "br", gp := gNat pj "gp",
        nc := gNat pj "ncopies", rp,
        lo := (gArr pj "lo").map (fun e => e.getNat?.toOption.getD 0),
        hi := (gArr pj "hi").map (fun e => e.getNat?.toOption.getD 0) }
  let pr (k : String) : Nat × Nat := match (jget j k).bind pairOf with
    | some p => p
    | none => (1, 1)
  let rn : RNode ← if virt then do
      let ow := match gix.get? (gStr j "owname") with
        | some gi => (gt d gi).out
        | none => 0
      pure { virt := true, ow, hasW := (gix.get? (gStr j "owname")).isSome }
    else do
      let lut ← match gix.get? (gStr j "lut") with
        | some gi => pure gi
        | none => throw s!"node {gStr j "name"}: no LUT gate {gStr j "lut"}"
      let qp ← parsePath gix ((jget j "qp").getD (Json.arr #[]))
      let rp ← parsePath gix ((jget j "rp").getD (Json.arr #[]))
      pure { virt := false, ow := (gt d lut).out, lut, qi := gNat j "qi", ri := gNat j "ri", qp, rp,
             pins := (pins.map (·.rp)).toList }
  pure { name := gStr j "name", v := gBool j "v", mg := gBool j "mg", virt, pins, rn, F := pr "F", Q := pr "Q" }

section
variable (N : Nat) (hN : 0 < N) (A : Array NodeD)

def nd (j : Fin N) : NodeD := A[j.val]!
def pd (j : Fin N) (p : Nat) : PinD := (nd N A j).pins[p]!

def mkNet : Net4 N where
  v := fun j => (nd N A j).v
  mg := fun j => (nd N A j).mg
  ar := fun j => max 1 (nd N A j).pins.size
  ar_pos := fun _ => Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)
  src := fun j p => let s := (pd N A j p.val).src; if h : s < N then ⟨s, h⟩ else ⟨0, hN⟩
  inv := fun j p => (pd N A j p.val).inv
  neg := fun j p => (pd N A j p.val).neg
  pk := fun j p => (pd N A j p.val).pk
  nc := fun j p => max 1 (pd N A j p.val).nc
  nc_pos := fun _ _ => Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)
  op := fun j p => (pd N A j p.val).op
  grp := fun j p => (pd N A j p.val).grp
  br := fun j p => (pd N A j p.val).br
  gp := fun j p => ⟨(pd N A j p.val).gp % max 1 (nd N A j).pins.size,
    Nat.mod_lt _ (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _))⟩

def mkRn (j : Fin N) : RNode := (nd N A j).rn

def mkBands (d : Design) : Bands4 (mkNet N hN A) :=
  let net := mkNet N hN A
  let rn := mkRn N A
  { loF := fun j => if (nd N A j).virt then (nd N A j).F.1 else 1
    hiF := fun j => if (nd N A j).virt then (nd N A j).F.2 else 1
    loC := fun j p i => if (nd N A j).virt then (pd N A j p.val).lo[i.val]! else plo d (full net rn j p i.val) - 1
    hiC := fun j p i => if (nd N A j).virt then (pd N A j p.val).hi[i.val]! else phi d (full net rn j p i.val) - 1
    loQ := fun j => if (nd N A j).virt then (nd N A j).Q.1 else if (nd N A j).mg then 1 else
      plo d (((rn j).lut, (rn j).qi) :: (rn j).qp) - 1
    hiQ := fun j => if (nd N A j).virt then (nd N A j).Q.2 else if (nd N A j).mg then 1 else
      phi d (((rn j).lut, (rn j).qi) :: (rn j).qp) - 1
    dw := fun j p i => if (nd N A j).virt then
        -- whole-band window of the copies (sound for any warps in these bands)
        ((pd N A j p.val).hi.foldl max 0) - ((pd N A j p.val).lo.foldl min 1000000000)
      else pairW d (full net rn j p i) (full net rn j p (i + 1)) }

end

def allFin (n : Nat) : List (Fin n) := List.finRange n

/-! ## Shortest low-end path (Bellman-Ford / SPFA over the parsed design; untrusted search) -/

/-- Distances (sum of gate `lo`) from wire `top` DOWN through gate inputs, and the
predecessor `(gate, input)` of each reached wire. -/
def spfa (d : Design) (drvG : Array (Option Nat)) (top : Nat) : Array Nat × Array (Option (Nat × Nat)) := Id.run do
  let inf := 1000000000000
  let mut dist : Array Nat := Array.replicate d.n inf
  let mut prev : Array (Option (Nat × Nat)) := Array.replicate d.n none
  dist := dist.set! top 0
  let mut q : Array Nat := #[top]
  let mut qi := 0
  let mut guard := 0
  while qi < q.size && guard < 5000000 do
    let w := q[qi]!
    qi := qi + 1
    guard := guard + 1
    match drvG[w]?.join with
    | none => pure ()
    | some g =>
      let gs := gt d g
      for i in [0:gs.k] do
        let v := gs.ins.getD i 0
        if v < d.n then
          let nd := dist[w]! + gs.lo
          if nd < dist[v]! then
            dist := dist.set! v nd
            prev := prev.set! v (some (g, i))
            q := q.push v
  return (dist, prev)

/-- The path from `top` down to `bot` recorded in `prev` (head at `top`). -/
def pathTo (d : Design) (prev : Array (Option (Nat × Nat))) (top bot : Nat) : Path := Id.run do
  let mut acc : List (Nat × Nat) := []
  let mut w := bot
  let mut n := 0
  while w != top && n < d.n do
    n := n + 1
    match prev[w]?.join with
    | none => n := d.n
    | some (g, i) =>
      acc := (g, i) :: acc
      w := (gt d g).out
  return acc

def run (args : List String) : IO UInt32 := do
  let netp :: bandp :: certp :: mapp :: rest := args
    | do IO.eprintln "usage: xselhold SKEL.json BANDS.json CERT.json MAP.json [--top T]"; return 2
  let j ← readJson netp
  let B0 := parseBands (← readJson bandp)
  let B : Bands := { B0 with unit := 1 }
  let (_, top) ← IO.ofExcept (pickTop j (getArg rest "--top"))
  let bt ← IO.ofExcept (buildDesign B top)
  let d := bt.d
  let gix : Std.HashMap String Nat := (d.gates.zipIdx).foldl (fun m (g, i) => m.insert g.name i) {}
  let cj ← readJson certp
  let mut A : Array NodeD := #[]
  for nj in gArr cj "nodes" do
    A := A.push (← IO.ofExcept (parseNode gix d nj))
  let N := A.size
  let mj ← readJson mapp
  let ents := gArr mj "entries"
  let nUnres := (gArr mj "unresolved").size
  if hN : 0 < N then
    let net := mkNet N hN A
    let b := mkBands N hN A d
    let rn := mkRn N A
    -- the driving gate of every wire
    let mut drvG : Array (Option Nat) := Array.replicate d.n none
    for (g, gi) in d.gates.zipIdx do
      if g.out < d.n then drvG := drvG.set! g.out (some gi)
    let wname (w : Nat) : String := bt.wname[w]?.getD s!"w{w}"
    IO.println s!"[xselhold] {d.gates.length} gates, {d.n} wires, {N} nodes; map: {ents.size} entries, {nUnres} unresolved"
    -- the literals the theorem quantifies over
    let mut lits : Array (Fin N × Nat × Nat) := #[]
    for jj in allFin N do
      if !(rn jj).virt then
        for p in allFin (net.ar jj) do
          if net.pk jj p == PK.filt then
            for sb in selLits net rn jj p do
              lits := lits.push (jj, p.val, sb.1)
    let mut nOK := 0
    let mut nEnt := 0
    let mut nChain := 0
    let mut nHold := 0
    let mut minM : Int := 1000000000
    let mut minAt := ""
    let mut fails : Array String := #[]
    let mut nS := 0
    let mut minS : Int := 1000000000
    let mut minSAt := ""
    let mut failsS : Array String := #[]
    let mut cache : Std.HashMap Nat (Array Nat × Array (Option (Nat × Nat))) := {}
    for (jj, pv, i) in lits do
      if hp : pv < net.ar jj then
        let p : Fin (net.ar jj) := ⟨pv, hp⟩
        let lab := s!"{(nd N A jj).name} pin{pv} lit{i}"
        let row := ents.find? (fun e => gNat e "node" == jj.val && gNat e "pin" == pv && gNat e "lit" == i)
        match row with
        | none => fails := fails.push s!"{lab}: NO MAP ENTRY (premise of design_verdict9_sel stays)"
        | some e =>
          let sgw := (gt d (selGate net rn jj p)).ins.getD i 0
          let rg := (drvG[sgw]?.join).getD d.gates.length
          let gw (k : String) : Nat := match gix.get? (gStr e k) with
            | some g => (gt d g).out
            | none => d.n
          let ws : List Nat := (gArr e "ws").toList.map fun w =>
            (bt.inputs.lookup ((w.getStr?.toOption).getD "")).getD d.n
          let se : SelEnt := SelEnt.mk (gStr e "name") (gw "rq") (gw "ak") ws ((gt d rg).ins.getD 0 0) rg
          let eok := entOK d net rn jj p i se
          if eok then nEnt := nEnt + 1
          let srcW := (gt d (rn (net.src jj p)).lut).out
          let srcVirt := (rn (net.src jj p)).virt
          let (dist, prev) ← match cache.get? se.ak with
            | some r => pure r
            | none => do
              let r := spfa d drvG se.ak
              cache := cache.insert se.ak r
              pure r
          let reach := decide (srcW < d.n) && dist[srcW]! < 1000000000000
          let π := if reach then pathTo d prev se.ak srcW else []
          let cok := chainOK d se.ak srcW π
          if cok then nChain := nChain + 1
          let D := plo d π
          let hok := holdBand d net b rn jj p se D
          if hok && cok then nHold := nHold + 1
          let ms := (allFin (net.nc jj p)).map (holdMargin d net b rn jj p se D)
          let mmin := ms.foldl min 1000000000
          let hiCmax := (allFin (net.nc jj p)).foldl (fun a c => max a (b.hiC jj p c)) 0
          let ok := eok && cok && hok && !srcVirt
          if ok then nOK := nOK + 1
          if cok && mmin < minM then
            minM := mmin
            minAt := lab
          -- split (junction-anchored) rows: per copy, the best cut whose bottom is a buffer chain
          let isBufB (g : Nat) : Bool := (gt d g).k == 1 && decide (InitSpec (gt d g) (fun v => v 0))
          let mut sok := eok && !srcVirt
          let mut smin : Int := 1000000000
          let mut sdesc := ""
          for c in allFin (net.nc jj p) do
            let fp := full net rn jj p c.val
            let mut best : Option (Int × Nat × Nat) := none
            for n in [0:fp.length] do
              if (fp.drop (n + 1)).all (fun e => isBufB e.1) then
                let w := junW d net rn jj p c.val n
                if w < d.n && dist[w]! < 1000000000000 then
                  let mg : Int := (dist[w]! : Int) + selLo d net rn jj p + (gt d rg).lo -
                    ((phi d (topP d net rn jj p c.val n) : Int) - 1) - 1
                  if best.all (fun bb => bb.1 < mg) then best := some (mg, n, w)
            match best with
            | none => sok := false; sdesc := sdesc ++ s!" c{c.val}:nocut"
            | some (_, n, w) =>
              let πs := pathTo d prev se.ak w
              let cs := chainOK d se.ak w πs
              let hs := holdBandS d net rn jj p se c.val n (plo d πs)
              let mg : Int := (plo d πs : Int) + selLo d net rn jj p + (gt d rg).lo -
                    ((phi d (topP d net rn jj p c.val n) : Int) - 1) - 1
              if !(cs && hs) then sok := false
              if mg < smin then smin := mg
              sdesc := sdesc ++ s!" c{c.val}:cut{n + 1}/{fp.length} w={wname w} Dw {plo d πs} topHi {phi d (topP d net rn jj p c.val n) - 1} m {mg}{if cs && hs then "" else " FAIL"}"
          if sok then nS := nS + 1
          if smin < minS then
            minS := smin
            minSAt := lab
          IO.println s!"  {if ok then "OK  " else "FAIL"} {lab} chan {se.name} req {wname se.rq} ack {wname se.ak} bus {se.ws.map wname} sel-arc {(gt d rg).name} [{(gt d rg).lo},{(gt d rg).hi}] entOK {eok} | SRC D {D} ({π.length} hops) selLo {selLo d net rn jj p} hiC {hiCmax} chain {cok} hold {hok} margin {mmin} | SPLIT {if sok then "OK" else "FAIL"} min {smin}{sdesc}"
          if !ok then fails := fails.push s!"{lab}: entOK {eok} chainOK {cok} holdBand {hok} srcVirt {srcVirt} margin {mmin}"
          if !sok then failsS := failsS.push s!"{lab}: split min {smin}{sdesc}"
    IO.println s!"[xselhold] literals {lits.size}: entOK {nEnt}, chainOK {nChain}, holdBand {nHold}, all three {nOK}; min hold margin {minM} ps at {minAt}"
    IO.println s!"[xselhold] split rows: {nS} of {lits.size} literals pass (entOK, chainOK, holdBandS on every copy); min split margin {minS} ps at {minSAt}"
    for f in fails do IO.println s!"  RESIDUAL(src) {f}"
    for f in failsS do IO.println s!"  RESIDUAL(split) {f}"
    IO.println (if nOK == lits.size then "SELHOLD(src) CLEAN" else s!"SELHOLD(src) RESIDUAL {lits.size - nOK}")
    IO.println (if nS == lits.size then "SELHOLD(split) CLEAN: every real select literal has a checked map entry and passing split hold rows"
      else s!"SELHOLD(split) RESIDUAL {lits.size - nS}")
    return (if nS == lits.size then 0 else 1)
  else
    IO.eprintln "no nodes"; return 2

end Formal.Core.XAudit.Events9SelMain

def main (args : List String) : IO UInt32 := Formal.Core.XAudit.Events9SelMain.run args
