import Lean.Data.Json
import Formal.Core.XAudit.Parse
import Formal.Core.XAudit.Events7Beh

/-!
# `xevents7` — check the A-events7 certificate of a ROUTED netlist (executable main)

    xevents7 NETLIST.json BANDS.json CERT.json [--top T] [--fuel F]

Probe A-events7 (rebuilt in E7r). Input: a routed2x-style control skeleton, its
band file (ps; read with 1 ps steps), and the certificate `CERT.json` emitted by
the UNTRUSTED `tools-A/xaudit/events7/cert7.py` (the `Net4` with guarded
delay-line pins, the per-node recognition data, the select partitions, the
derivation LOG and the per-item references into it).

What it checks (the hypotheses of `Events7.design_verdict7`, by evaluation):

* `Recog6 d net b rn rank rw fuel` (unchanged from A-events6) and `Net4.OK7`;
* `runLog net b parts log = some J`: every log line is accepted by `concl`;
* per stage pin `backOK7`, per merge `exclOK7`, per line pin `lineOK7` against `J`
  (STRICT margins).

Items without a valid certificate are listed as RESIDUAL (`design_verdict7`
carries them as explicit count-level hypotheses). CLEAN = recognition, OK7, an
accepted log and no residual item: then every per-pin behaviour of the netlist
(no H_ATOMIC_LUT), under H_ARB, SelOK, SelPart and GuardOK, has every real
node's wire equal to its reset value flipped `M t j` times at every time.

If the log is NOT accepted nothing is certified. The margins then printed are
diagnostics only, computed from a lenient run of the log in which every rejected
line gets the default judgement (all fields 0).

TRUSTED: the JSON / netlist parsers (`Parse`), the certificate reader below, the
mapping of certificate data to `Net4`/`Bands4`/`RNode`/`Ln`, the printed numbers,
and the Lean compiler running the instances.
-/

namespace Formal.Core.XAudit.Events7Main

open Lean (Json)
open Formal.Core
open Formal.Core.XAudit
open Formal.Core.XAudit.Parse
open Formal.Core.XAudit.Events5
open Formal.Core.XAudit.Events6
open Formal.Core.XAudit.Events7

set_option synthInstance.maxSize 2048 in
instance instOK7 {N : Nat} (net : Net4 N) : Decidable net.OK7 := by unfold Net4.OK7; exact inferInstance

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

/-! ## The log -/

def parseArm (j : Json) : Arm :=
  { g := gNat j "g", b := gBool j "b", dir := gBool j "dir", ref := gNat j "ref" }

def parseArms (j : Json) (k : String) : List Arm := (gArr j k).toList.map parseArm

/-- One log line (cert7.py's `log` entries). An unknown kind becomes a line that
`concl` rejects (`refl` of a node index out of range). -/
def parseLn (j : Json) : Ln :=
  match gStr j "k" with
  | "refl" => .refl (gNat j "a")
  | "r1" => .r1 (gNat j "n") (gNat j "p") (gNat j "r")
  | "fpin" => .fpin (gNat j "n") (gNat j "p") (gNat j "r")
  | "r3" => .r3 (gNat j "x") (gNat j "S") (parseArms j "arms") (gNat j "r")
  | "lift" => .lift (gNat j "g") (gBool j "b") (gNat j "r")
  | "sub" => .sub (gNat j "x") (gNat j "S") (gNat j "ab") (parseArms j "arms") (gNat j "w1") (gNat j "w2")
  | "uT" => .uT (gNat j "T") (gNat j "q")
  | "uW" => .uW (gNat j "w") (gNat j "u")
  | _ => .refl 1000000000

def parseParts (j : Json) : List (List Nat) :=
  (gArr j "parts").toList.map fun p => match p.getArr? with
    | .ok a => a.toList.map (fun e => e.getNat?.toOption.getD 0)
    | .error _ => []

/-- Diagnostic run of the log: a rejected line gets the default judgement; returns
the judgements and the first rejected line. (Not used for any certification:
an item is certified only from `runLog`'s result.) -/
def runLogD {N : Nat} (net : Net4 N) (b : Bands4 net) (parts : List (List Nat)) (log : Array Ln) :
    Array Jd × Option Nat := Id.run do
  let mut J : Array Jd := #[]
  let mut bad : Option Nat := none
  for ln in log do
    match concl net b parts J ln with
    | some j => J := J.push j
    | none =>
      if bad.isNone then bad := some J.size
      J := J.push default
  return (J, bad)

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

def run (args : List String) : IO UInt32 := do
  let netp :: bandp :: certp :: rest := args
    | do IO.eprintln "usage: xevents7 NETLIST.json BANDS.json CERT.json [--top T] [--fuel F]"; return 2
  let j ← readJson netp
  let B0 := parseBands (← readJson bandp)
  let B : Bands := { B0 with unit := 1 }
  let (_, top) ← IO.ofExcept (pickTop j (getArg rest "--top"))
  let bt ← IO.ofExcept (buildDesign B top)
  let d := bt.d
  let fuel := ((getArg rest "--fuel").bind String.toNat?).getD 64
  let gix : Std.HashMap String Nat := (d.gates.zipIdx).foldl (fun m (g, i) => m.insert g.name i) {}
  let cj ← readJson certp
  let nodesJ := gArr cj "nodes"
  let mut A : Array NodeD := #[]
  for nj in nodesJ do
    A := A.push (← IO.ofExcept (parseNode gix d nj))
  let N := A.size
  if hN : 0 < N then
    let net := mkNet N hN A
    let b := mkBands N hN A d
    let rn := mkRn N A
    let rankA := (gArr cj "rank").map (fun e => e.getNat?.toOption.getD 0)
    let rank : Fin N → Nat := fun j => rankA[j.val]!
    let rw := (bt.inputs.lookup "rig_rst").getD 0
    IO.println s!"[xevents7] {d.gates.length} gates, {N} nodes ({(A.filter (·.virt)).size} virtual, H_ARB), fuel {fuel}, 1 ps steps"
    if !bt.raised.isEmpty then
      IO.println s!"[xevents7] {bt.raised.length} bands with lo = 0 ps raised to 1 ps (Parse.toSteps)"
    -- recognition
    let wf := decide d.WF
    let mut recogBad : Array String := #[]
    for jj in allFin N do
      if !(rn jj).virt then
        if !(decide (NodeR d net b rn rank rw fuel jj)) then
          recogBad := recogBad.push (nd N A jj).name
    let ok := decide net.OK7
    let mut nG := 0
    for jj in allFin N do
      for p in allFin (net.ar jj) do
        if net.pk jj p == PK.guard && decide (1 < net.nc jj p) then nG := nG + 1
    IO.println s!"[xevents7] Design.WF {wf}; Recog6 node failures {recogBad.size}; Net4.OK7 {ok}; guarded delay-line pins {nG}"
    for s in recogBad.toList.take 20 do IO.println s!"  RECOG-FAIL {s}"
    -- the log
    let parts := parseParts cj
    IO.println s!"[xevents7] select partitions (SelPart): {parts}"
    let logA : Array Ln := (gArr cj "log").map parseLn
    let acc := runLog net b parts logA.toList
    let (JD, bad) := runLogD net b parts logA
    let accepted := acc.isSome
    let J : Array Jd := acc.getD JD
    IO.println s!"[xevents7] derivation log: {logA.size} lines, accepted by runLog: {accepted}{match bad with | some i => s!" (first rejected line {i})" | none => ""}"
    -- certificates
    let backJ := (jget cj "back").getD Json.null
    let lineJ := (jget cj "lines").getD Json.null
    let exclJ := (jget cj "excl").getD Json.null
    let mut nB := 0
    let mut nBok := 0
    let mut minB : Int := 1000000000
    let mut resid : Array String := #[]
    let mut margins : Array (Int × String) := #[]
    for jj in allFin N do
      if net.mg jj then continue
      for p in allFin (net.ar jj) do
        if net.pk jj p == PK.guard then continue
        nB := nB + 1
        let lab := s!"{(nd N A jj).name} pin{p.val}{if (nd N A jj).virt then " (virtual)" else ""}"
        match (jget backJ s!"{jj.val}/{p.val}").bind jnat with
        | some i =>
          if hi : i < J.size then
            let k := J[i]
            let m : Int := (b.loP jj p : Int) + (k.d : Int) - (b.hiQ jj : Int)
            let cons := !k.u && k.a == (net.src jj p).val && k.bb == jj.val &&
              k.c == (if net.pk jj p = PK.filt then some (net.grp jj p, net.br jj p) else none) &&
              decide (k.t + net.off jj p ≤ 1)
            if cons then
              margins := margins.push (m, lab)
              if m < minB then minB := m
            if accepted && backOK7 net b J jj p i then nBok := nBok + 1
            else resid := resid.push s!"Back {lab}: margin {m}{if accepted && !cons then " (judgement does not match the pin)" else ""}"
          else resid := resid.push s!"Back {lab}: log line {i} out of range"
        | none => resid := resid.push s!"Back {lab}: no certificate"
    -- lines
    let mut nL := 0
    let mut nLok := 0
    let mut minL : Int := 1000000000
    for jj in allFin N do
      for p in allFin (net.ar jj) do
        if net.pk jj p != PK.multi then continue
        nL := nL + 1
        let lab := s!"{(nd N A jj).name} pin{p.val}"
        match (jget lineJ s!"{jj.val}/{p.val}").bind jnat with
        | some i =>
          if hi : i < J.size then
            let k := J[i]
            let wmax := (List.range (net.nc jj p - 1)).foldl (fun a i => max a (b.dw jj p i)) 0
            let m : Int := (k.d : Int) - (wmax : Int)
            if m < minL then minL := m
            if accepted && lineOK7 net b J jj p i then nLok := nLok + 1
            else resid := resid.push s!"Line {lab}: margin {m} (W {k.d}, window {wmax})"
          else resid := resid.push s!"Line {lab}: log line {i} out of range"
        | none => resid := resid.push s!"Line {lab}: no certificate"
    -- merges
    let mut nX := 0
    let mut nXok := 0
    let mut nX3 := 0
    for jj in allFin N do
      if !net.mg jj then continue
      nX := nX + 1
      if decide (2 < net.ar jj) then nX3 := nX3 + 1
      let lab := (nd N A jj).name
      match jget exclJ s!"{jj.val}" with
      | some ej =>
        if accepted && exclOK7 net b parts J jj (gNat ej "S") (parseArms ej "arms") (gNat ej "w") then
          nXok := nXok + 1
        else resid := resid.push s!"Excl {lab} ({net.ar jj} arms): certificate does not check"
      | none =>
        if accepted && decide (net.ar jj ≤ 1) then nXok := nXok + 1
        else resid := resid.push s!"Excl {lab} ({net.ar jj} arms): no certificate"
    IO.println s!"[xevents7] Back pins {nBok}/{nB} certified (strict), min margin {minB} ps"
    IO.println s!"[xevents7] line pins {nLok}/{nL} certified (strict), min margin {minL} ps"
    IO.println s!"[xevents7] merges {nXok}/{nX} certified ({nX3} with more than 2 arms)"
    let sorted := margins.qsort (fun a c => a.1 < c.1)
    for (m, l) in sorted.toList.take 5 do IO.println s!"  lowest Back {m} {l}"
    IO.println s!"[xevents7] RESIDUAL items (hypotheses of design_verdict7): {resid.size}"
    for r in resid do IO.println s!"  RESIDUAL {r}"
    let errs := gArr cj "errors"
    IO.println s!"[xevents7] (cert7.py reported {errs.size} items it could not certify)"
    let recog := wf && recogBad.isEmpty && ok && accepted
    let clean := recog && resid.isEmpty
    IO.println s!"VERDICT {if clean then "CLEAN" else if recog then "RECOGNISED, RESIDUAL " ++ toString resid.size else "NOT RECOGNISED"} (Events7.design_verdict7; hypotheses: per-pin SatPin, H_ARB, SelOK, SelPart, GuardOK{if resid.isEmpty then "" else ", the residual items"})"
    return (if clean then 0 else if recog then 1 else 3)
  else
    IO.eprintln "empty certificate"; return 2

end Formal.Core.XAudit.Events7Main

def main (args : List String) : IO UInt32 := Formal.Core.XAudit.Events7Main.run args
