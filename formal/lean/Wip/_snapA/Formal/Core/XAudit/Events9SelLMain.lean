import Lean.Data.Json
import Formal.Core.XAudit.Parse
import Formal.Core.XAudit.Events9SelJ

/-!
# `xselL` — evaluate the checked select rows of `design_verdict9_selL` / `selT` / `selJ` (executable main)

    xselL SKEL.json BANDS.json CERT.json MAP.json [--top T]

Probe E9SelRun (shard A). CERT is `tools-A/xaudit/selrun/certsel.py`'s output: the cert9
certificate (nodes, log, ...) with the select rows' walk lines appended to its log and a `sel`
section (per map entry: gate trees, leaves, log lines, junction rows; junction logs). MAP is
E8SelC's `selhold/mkmap.py` map (channel name, request / acknowledge / bus wires). The
parsers are copied from `Events9SelMain` / `Events9Main`.

Per REAL filtered pin `(j, p)` and select literal it evaluates, with the Lean functions the
theorems quantify over:
* `entOK` (Events9SelC), on the map entry (as `xselhold`);
* **selL** (E8Causal's `Events9PrefixSel.design_verdict9_selL`): `ackOK` with the first
  request leaf as `nq` and its path as `κ`, `ReqLine`, and per copy `holdBandS` + `AckLine` at
  the source cut (`bot = []`) with `Dl = dW + 1`;
* **selT** (`Events9SelL.design_verdict9_selT`): `treeOK`, `reqOK`, and per copy `holdBandS` +
  `AckLineT` at the source cut with `Dl = dW + plo κa + 1`;
* **selJ** (`Events9SelJ.design_verdict9_selJ`): `treeOK`, `reqOK`, and per copy the junction
  row `jrowOK` at the certificate's cut with `Dl = dj + plo κa + 1` and `holdBandS` at that cut.
It also evaluates the recognition (`Recog6`, `Net4.OK7`) and `runLog` (the log must be
accepted). The other items of `design_verdict9` (Back, lines, merges, guards) are `xevents9`'s:
run it on the same certificate.

What a CLEAN row means: the checked select-side premises of the named theorem hold for every
real select literal. TRUSTED: the parsers, the map's channel names (which wire is the
channel's ack / req / bus), the printed margins, and the Lean compiler.
-/

namespace Formal.Core.XAudit.Events9SelLMain

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
open Formal.Core.XAudit.Events9PrefixSel
open Formal.Core.XAudit.Events9SelL
open Formal.Core.XAudit.Events9SelJ

instance instOK7 {N : Nat} (net : Net4 N) : Decidable net.OK7 := by unfold Net4.OK7; exact inferInstance

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

/-- One hypothesis line (cert9.py's `hyp` entries); a `dsub` line without `wS` gets an
out-of-range `wS` (so it has no judgement). -/
def parseHLn9 (j : Json) : HLn9 :=
  match gStr j "k" with
  | "dsub" => .dsub (gNat j "a") (gNat j "x") (gNat j "S") (gNat j "ab") (parseArms j "arms") (gNat j "w1") (gNat j "w2")
      (((jget j "wS").bind jnat).getD 1000000000)
  | _ => .copy (gNat j "i")

def parseParts (j : Json) : List (List Nat) :=
  (gArr j "parts").toList.map fun p => match p.getArr? with
    | .ok a => a.toList.map (fun e => e.getNat?.toOption.getD 0)
    | .error _ => []

/-! ## The select section -/

partial def parseAT (gix : Std.HashMap String Nat) (j : Json) : AT :=
  match jget j "leaf" with
  | some l => AT.leaf ((jnat l).getD 1000000000)
  | none =>
    let g := (gix.get? (gStr j "g")).getD 1000000000
    let ch := (gArr j "ch").toList.map fun c => match c.getArr? with
      | .ok a => ((a[0]!.getNat?.toOption.getD 1000000000), parseAT gix a[1]!)
      | .error _ => (1000000000, AT.leaf 1000000000)
    AT.gate g (ch.foldr (fun c r => ATL.cons c.1 c.2 r) ATL.nil)

def parseJArm (j : Json) : JArm :=
  { g := gNat j "g", b := gBool j "b", dir := gBool j "dir", e := gNat j "e", ref := gNat j "ref" }

def parseJLn (j : Json) : JLn :=
  match gStr j "k" with
  | "jrefl" => .jrefl
  | "jpin" => .jpin (gNat j "n") (gNat j "p") (gNat j "e")
  | "juT" => .juT (gNat j "n") (gNat j "p") (gNat j "e")
  | "jwalk" => .jwalk (gNat j "w") (gNat j "r")
  | "juW" => .juW (gNat j "w") (gNat j "r")
  | "jr3" => .jr3 (gNat j "xm") ((gArr j "arms").toList.map parseJArm)
  | _ => .jpin 1000000000 0 0

def natList (j : Json) (k : String) : List Nat := (gArr j k).toList.map (fun e => e.getNat?.toOption.getD 1000000000)

def run (args : List String) : IO UInt32 := do
  let netp :: bandp :: certp :: mapp :: rest := args
    | do IO.eprintln "usage: xselL SKEL.json BANDS.json CERT.json MAP.json [--top T] [--fuel F]"; return 2
  let j ← readJson netp
  let B0 := parseBands (← readJson bandp)
  let B : Bands := { B0 with unit := 1 }
  let (_, top) ← IO.ofExcept (pickTop j (getArg rest "--top"))
  let bt ← IO.ofExcept (buildDesign B top)
  let d := bt.d
  let fuel := ((getArg rest "--fuel").bind String.toNat?).getD 64
  let gix : Std.HashMap String Nat := (d.gates.zipIdx).foldl (fun m (g, i) => m.insert g.name i) {}
  let cj ← readJson certp
  let mut A : Array NodeD := #[]
  for nj in gArr cj "nodes" do
    A := A.push (← IO.ofExcept (parseNode gix d nj))
  let N := A.size
  let mj ← readJson mapp
  let ents := gArr mj "entries"
  let selJ := (jget cj "sel").getD Json.null
  let sents := gArr selJ "entries"
  let blocksJ := gArr selJ "blocks"
  if hN : 0 < N then
    let net := mkNet N hN A
    let b := mkBands N hN A d
    let rn := mkRn N A
    let rankA := (gArr cj "rank").map (fun e => e.getNat?.toOption.getD 0)
    let rank : Fin N → Nat := fun j => rankA[j.val]!
    let rw := (bt.inputs.lookup "rig_rst").getD 0
    let mut drvG : Array (Option Nat) := Array.replicate d.n none
    for (g, gi) in d.gates.zipIdx do
      if g.out < d.n then drvG := drvG.set! g.out (some gi)
    let wname (w : Nat) : String := bt.wname[w]?.getD s!"w{w}"
    IO.println s!"[xselL] {d.gates.length} gates, {d.n} wires, {N} nodes; map {ents.size} entries; sel {sents.size} entries, {blocksJ.size} junction logs"
    -- recognition and the log
    let recog := decide (Recog6 d net b rn rank rw fuel)
    let ok7 := decide net.OK7
    let parts := parseParts cj
    let logA : Array Ln := (gArr cj "log").map parseLn
    let acc := runLog net b parts logA.toList
    let accepted := acc.isSome
    let J : Array Jd := acc.getD #[]
    IO.println s!"[xselL] Recog6 {recog}; Net4.OK7 {ok7}; derivation log {logA.size} lines, accepted by runLog: {accepted}"
    let blocks : Array (List JLn) := blocksJ.map (fun bj => (gArr bj "lines").toList.map parseJLn)
    -- the literals the theorems quantify over
    let mut lits : Array (Fin N × Nat × Nat) := #[]
    for jj in allFin N do
      if !(rn jj).virt then
        for p in allFin (net.ar jj) do
          if net.pk jj p == PK.filt then
            for sb in selLits net rn jj p do
              lits := lits.push (jj, p.val, sb.1)
    let mut nEnt := 0
    let mut nTree := 0
    let mut nReq := 0
    let mut nL := 0
    let mut nT := 0
    let mut nJ := 0
    let mut minL : Int := 1000000000
    let mut minT : Int := 1000000000
    let mut minJ : Int := 1000000000
    let mut resL : Array String := #[]
    let mut resT : Array String := #[]
    let mut resJ : Array String := #[]
    for (jj, pv, i) in lits do
      if hp : pv < net.ar jj then
        let p : Fin (net.ar jj) := ⟨pv, hp⟩
        let lab := s!"{(nd N A jj).name} pin{pv} lit{i}"
        let row := ents.find? (fun e => gNat e "node" == jj.val && gNat e "pin" == pv && gNat e "lit" == i)
        let srow := sents.find? (fun e => gNat e "node" == jj.val && gNat e "pin" == pv && gNat e "lit" == i)
        match row, srow with
        | some e, some se0 =>
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
          let src := net.src jj p
          let ta := parseAT gix ((jget se0 "ta").getD Json.null)
          let tq := parseAT gix ((jget se0 "tq").getD Json.null)
          let naN := gNat se0 "na"
          let nqN := gNat se0 "nq"
          let ka : Path := (parsePath gix ((jget se0 "ka").getD (Json.arr #[]))).toOption.getD [(1000000000, 0)]
          let kq : Path := (parsePath gix ((jget se0 "kq").getD (Json.arr #[]))).toOption.getD [(1000000000, 0)]
          let wq := natList se0 "wq"
          let wa := gNat se0 "wa"
          let jcs := gArr se0 "jc"
          let selLo' : Int := (selLo d net rn jj p : Int) + (gt d rg).lo
          if hna : naN < N then
            let na : Fin N := ⟨naN, hna⟩
            let tok := treeOK (d := d) (net := net) (rn := rn) se ta tq na ka
            let rok := accepted && reqOK d J naN ka (AT.leaves tq) wq
            if tok then nTree := nTree + 1
            if rok then nReq := nReq + 1
            let dW : Nat := if h : wa < J.size then J[wa].d else 0
            -- selL (E8Causal): ackOK + ReqLine + AckLine at the source cut, Dl = dW + 1
            let lok0 := accepted && eok && (if hq : nqN < N then
              ackOK d net rn se na ⟨nqN, hq⟩ kq && decide (ReqLine J nqN naN (wq.headD 1000000000)) else false)
            let mut lok := lok0
            let mut tokR := eok && tok && rok
            let mut jokR := eok && tok && rok
            let mut mL : Int := 1000000000
            let mut mT : Int := 1000000000
            let mut mJ : Int := 1000000000
            let mut desc := ""
            for c in allFin (net.nc jj p) do
              let fp := full net rn jj p c.val
              let cutS := fp.length - 1
              let topHi : Int := phi d (topP d net rn jj p c.val cutS)
              -- selL row
              let DlL := dW + 1
              let hL := holdBandS d net rn jj p se c.val cutS DlL &&
                decide (AckLine J naN src.val wa DlL (phi d (botP d net rn jj p c.val cutS)))
              let marL : Int := (DlL : Int) + selLo' - topHi
              mL := min mL marL
              if !hL then lok := false
              -- selT row
              let DlT := dW + plo d ka + 1
              let hT := accepted && holdBandS d net rn jj p se c.val cutS DlT &&
                decide (AckLineT J naN src.val wa DlT (phi d (botP d net rn jj p c.val cutS)) (plo d ka))
              let marT : Int := (DlT : Int) + selLo' - topHi
              mT := min mT marT
              if !hT then tokR := false
              -- selJ row
              match jcs[c.val]? with
              | some jc =>
                if jc.isNull then
                  jokR := false; desc := desc ++ s!" c{c.val}:nojunction"
                else
                  let cut := gNat jc "cut"
                  let blk := gNat jc "blk"
                  let jw := gNat jc "jw"
                  let bot := botP d net rn jj p c.val cut
                  let lines := blocks[blk]?.getD []
                  let JJ := (runJ net b parts J src.val (facOK d net rn bot) (decide (bot = [])) lines).getD #[]
                  let dj : Nat := if h : jw < JJ.size then JJ[jw].d else 0
                  let DlJ := dj + plo d ka + 1
                  let hJ := accepted && jrowOK d net b rn parts J src.val bot lines jw naN (plo d ka) DlJ &&
                    holdBandS d net rn jj p se c.val cut DlJ
                  let tH : Int := phi d (topP d net rn jj p c.val cut)
                  let marJ : Int := (DlJ : Int) + selLo' - tH
                  mJ := min mJ marJ
                  if !hJ then jokR := false
                  desc := desc ++ s!" c{c.val}:cut{cut + 1}/{fp.length} w={wname (junW d net rn jj p c.val cut)} dj {dj} topHi {tH} m {marJ}{if hJ then "" else " FAIL"}"
              | none => jokR := false; desc := desc ++ s!" c{c.val}:missing"
            if lok then nL := nL + 1
            if tokR then nT := nT + 1
            if jokR then nJ := nJ + 1
            minL := min minL mL; minT := min minT mT; minJ := min minJ mJ
            let nleaf := (AT.leaves tq).length
            IO.println s!"  {lab} chan {se.name} ack {wname se.ak} (leaf {(nd N A na).name}, {ka.length} hops) req {wname se.rq} ({nleaf} leaves) entOK {eok} treeOK {tok} reqOK {rok} | selL {if lok then "OK" else "FAIL"} ackOK {lok0} m {mL} | selT {if tokR then "OK" else "FAIL"} dW {dW} m {mT} | selJ {if jokR then "OK" else "FAIL"}{desc}"
            if !lok then resL := resL.push s!"{lab}: ackOK/ReqLine {lok0} margin {mL}"
            if !tokR then resT := resT.push s!"{lab}: entOK {eok} treeOK {tok} reqOK {rok} margin {mT}"
            if !jokR then resJ := resJ.push s!"{lab}: entOK {eok} treeOK {tok} reqOK {rok}{desc}"
          else
            resL := resL.push s!"{lab}: ack leaf out of range"; resT := resT.push s!"{lab}: ack leaf out of range"
            resJ := resJ.push s!"{lab}: ack leaf out of range"
        | _, _ =>
          resL := resL.push s!"{lab}: no map / sel entry"; resT := resT.push s!"{lab}: no map / sel entry"
          resJ := resJ.push s!"{lab}: no map / sel entry"
    let base := recog && ok7 && accepted
    IO.println s!"[xselL] literals {lits.size}: entOK {nEnt}, treeOK {nTree}, reqOK {nReq}"
    IO.println s!"[xselL] selL rows {nL}/{lits.size} (min margin {minL} ps); selT rows {nT}/{lits.size} (min margin {minT} ps); selJ rows {nJ}/{lits.size} (min margin {minJ} ps)"
    for r in resL do IO.println s!"  RESIDUAL(selL) {r}"
    for r in resT do IO.println s!"  RESIDUAL(selT) {r}"
    for r in resJ do IO.println s!"  RESIDUAL(selJ) {r}"
    let v (n : Nat) : String := if base && n == lits.size then "CLEAN" else s!"RESIDUAL {lits.size - n}{if base then "" else " (recognition/log not accepted)"}"
    IO.println s!"SELL {v nL}"
    IO.println s!"SELT {v nT}"
    IO.println s!"SELJ {v nJ}"
    return (if base && nJ == lits.size then 0 else 1)
  else
    IO.eprintln "no nodes"; return 2

end Formal.Core.XAudit.Events9SelLMain

def main (args : List String) : IO UInt32 := Formal.Core.XAudit.Events9SelLMain.run args
