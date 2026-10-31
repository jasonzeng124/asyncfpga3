import Lean.Data.Json
import Formal.Core.XAudit.Parse
import Formal.Core.XAudit.Events9ArbNetRows
import Formal.Core.XAudit.Events9ArbNetEdge
import Formal.Core.XAudit.Events9ArbB1

/-!
# `xarbnet` — check the arbiter link of a ROUTED netlist (executable main)

    lean --run Formal/Core/XAudit/Events9ArbNetMain.lean NETLIST.json BANDS.json CERT.json ARB.json [--top T] [--fuel F]

Probe E9ArbNet (shard A). Reads the netlist and bands (as `xevents9par`), the certificate
`CERT.json` (cert9p.py: nodes, reset classes) and the arbiter data `ARB.json` (arbnet/gen.py), and
evaluates the CHECKED premises of `Events9ArbNet.design_verdict9arbnet` that replace `HARB7'` and
`HRst`: per arbiter `ArbOK` (bd_arbiter's four LUT functions on the INITs, every read path, the
request nets, the corrected-core shape and bands of its six virtual nodes, the band side
conditions), `OwnOK` (every virtual node owned by exactly one arbiter), `RsOK` (the reset classes
are readers), `FixShape`. Then it prints, per arbiter and reader, the edge-time ROWS of probe
E9ArbNet part 2 (`Events9ArbNet.Rows`; untrusted reading, see the notes: no theorem says that the
rows imply `ArbCond`).

TRUSTED: the parsers, the certificate / arbiter readers below (the reader of `CERT.json` is
`xevents9par`'s, copied), the printed numbers, the Lean compiler.
-/

namespace Formal.Core.XAudit.Events9ArbNetMain

open Lean (Json)
open Formal.Core
open Formal.Core.XAudit
open Formal.Core.XAudit.Parse
open Formal.Core.XAudit.Events5
open Formal.Core.XAudit.Events6
open Formal.Core.XAudit.Events9Arb
open Formal.Core.XAudit.Events9ArbNet

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
  rc : Nat := 0
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
  pure { name := gStr j "name", v := gBool j "v", mg := gBool j "mg", virt, pins, rn, F := pr "F", Q := pr "Q",
         rc := gNat j "rc" }

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

instance instFix {N : Nat} (net : Net4 N) (b : Bands4 net) (rn : Fin N → RNode) :
    Decidable (FixShape net b rn) := by unfold FixShape; exact inferInstance

def parseReq (gix : Std.HashMap String Nat) (d : Design) (j : Json) : Except String ReqD := do
  let wb ← match gix.get? (gStr j "wbuf") with
    | some gi => pure gi
    | none => throw s!"arb data names gate {gStr j "wbuf"}, which the netlist does not have"
  let w := (gt d wb).ins.getD 0 0
  let paths ← (gArr j "paths").toList.mapM (parsePath gix)
  let top ← parsePath gix ((jget j "top").getD (Json.arr #[]))
  let bot ← parsePath gix ((jget j "bot").getD (Json.arr #[]))
  let st := gBool j "st"
  let sg := if st then (gix.get? (gStr j "sg")).getD 0 else 0
  pure { w, rp := { ip := 0, fold := [], st, paths, top, sg, sci := gNat j "sci",
                    ssel := parseSel ((jget j "ssel").getD (Json.arr #[])), bot } }

/-- The environment lower bound of a request (gen.py `w_env`: least lower delay of any LUT path from
the A0 net to the request net; UNTRUSTED). -/
def wEnv (j : Json) : Option Nat := (jget j "w_env").bind jnat

def parseArb (N : Nat) (gix : Std.HashMap String Nat) (d : Design) (j : Json) : Except String (ArbD N) := do
  let fin (k : String) : Except String (Fin N) :=
    let v := gNat j k
    if h : v < N then pure ⟨v, h⟩ else throw s!"arb {gStr j "name"}: node index {k} = {v} out of range"
  let gate (k : String) : Except String Nat := match gix.get? (gStr j k) with
    | some gi => pure gi
    | none => throw s!"arb {gStr j "name"}: no gate {gStr j k}"
  let pp (k : String) : Except String Path := parsePath gix ((jget j k).getD (Json.arr #[]))
  pure { jc := ← fin "jc", jg1 := ← fin "jg1", jg2 := ← fin "jg2", js1 := ← fin "js1", js2 := ← fin "js2",
         jR := ← fin "jR", jA := ← fin "jA",
         gG1 := ← gate "gG1", gG2 := ← gate "gG2", gR := ← gate "gR", gQ := ← gate "gQ",
         i1g1 := gNat j "i1g1", iqg1 := gNat j "iqg1", i2g2 := gNat j "i2g2", iqg2 := gNat j "iqg2",
         i1R := gNat j "i1R", i2R := gNat j "i2R", iqR := gNat j "iqR",
         p1g1 := ← pp "p1g1", pqg1 := ← pp "pqg1", p2g2 := ← pp "p2g2", pqg2 := ← pp "pqg2",
         p1R := ← pp "p1R", p2R := ← pp "p2R", pqR := ← pp "pqR",
         i1Q := gNat j "i1Q", i2Q := gNat j "i2Q", iqQ := gNat j "iqQ", irQ := gNat j "irQ", iA := gNat j "iA",
         p1Q := ← pp "p1Q", p2Q := ← pp "p2Q", pqQ := ← pp "pqQ", prQ := ← pp "prQ", pA := ← pp "pA",
         rq1 := ← parseReq gix d ((jget j "rq1").getD Json.null),
         rq2 := ← parseReq gix d ((jget j "rq2").getD Json.null) }

/-- The least quiet-start time `T0` that the start-bound conjuncts of `ArbRowsOK` allow for a
design reset released at `T` (the B1 rows do not depend on `T0`). -/
def t0Min {N : Nat} (d : Design) (a : ArbD N) (T : Nat) : Nat :=
  let B := bandsOf d a
  max (max ((B.g1 0).2 + (B.g1 2).2 + 2) ((B.g2 1).2 + (B.g2 2).2 + 2))
    (max (max ((B.r0 0).2 + (B.r0 2).2 + 2) ((B.r0 1).2 + (B.r0 2).2 + 2))
      (max (T + phi d (PrQ a) + (B.g2 2).2 + 2) (T + phi d (PrQ a) + (B.r0 2).2)))

/-- DIAGNOSTIC ONLY: the largest κ (×10^6, floor) such that `(1+κ) Pr + 2 ≤ (1-κ) (PQ + Pq)` at both
band ends, where `P` are the path delays with every arc at the same band end: the B1 inequality for
any delays within a factor `1 ± κ` of a shared-position nominal (B1 is linear in the position).
`κ = (PQ + Pq - Pr - 2) / (PQ + Pq + Pr)`; negative if B1 fails already at κ = 0. -/
def b1Kappa {N : Nat} (d : Design) (a : ArbD N) : List (String × Int) :=
  let B := bandsOf d a
  let z (n : Nat) : Int := n
  let k1 (q r : Int) : Int := ((q - r - 2) * 1000000) / (q + r)
  let m (P : Path) (dr dq : Nat × Nat) : Int :=
    min (k1 (z (plo d P) + z dq.1) (z dr.1)) (k1 (z (phi d P) + z dq.2) (z dr.2))
  [("g1", m (P1Q a) (B.g1 0) (B.g1 2)), ("g2", m (P2Q a) (B.g2 1) (B.g2 2)),
   ("s1", m (P1Q a) ((B.r0 0).1 - 2, (B.r0 0).2 - 2) ((B.r0 2).1 - 2, (B.r0 2).2 - 2)),
   ("s2", m (P2Q a) ((B.r0 1).1 - 2, (B.r0 1).2 - 2) ((B.r0 2).1 - 2, (B.r0 2).2 - 2))]

/-- DIAGNOSTIC ONLY (no theorem): the B1 margins when every arc sits at the SAME end of its band
(all at lo, all at hi): `lo DrQ + lo Dq - lo Dr - 2` and `hi DrQ + hi Dq - hi Dr - 2`. B1 is linear in a
shared position, so both >= 0 means B1 holds for every shared position (H_SPREAD_CORRELATED reading). -/
def b1Corr {N : Nat} (d : Design) (a : ArbD N) : List (String × Int × Int) :=
  let B := bandsOf d a
  let z (n : Nat) : Int := n
  let m (P : Path) (dr dq : Nat × Nat) : Int × Int :=
    (z (plo d P) + z dq.1 - z dr.1 - 2, z (phi d P) + z dq.2 - z dr.2 - 2)
  [("g1", m (P1Q a) (B.g1 0) (B.g1 2)), ("g2", m (P2Q a) (B.g2 1) (B.g2 2)),
   ("s1", m (P1Q a) ((B.r0 0).1 - 2, (B.r0 0).2 - 2) ((B.r0 2).1 - 2, (B.r0 2).2 - 2)),
   ("s2", m (P2Q a) ((B.r0 1).1 - 2, (B.r0 1).2 - 2) ((B.r0 2).1 - 2, (B.r0 2).2 - 2))]

/-- Margins (rhs - lhs, >= 0 holds) of the conjuncts of `ArbRowsOK d a T T0`, in its order
(diagnostics only; the verdict uses `decide (ArbRowsOK …)`). -/
def rowsDiag {N : Nat} (d : Design) (a : ArbD N) (T T0 : Nat) : List (String × Int) :=
  let B := bandsOf d a
  let z (n : Nat) : Int := n
  [("B1 g1", z (plo d (P1Q a) + (B.g1 2).1) - z ((B.g1 0).2 + 2)),
   ("B1 g2", z (plo d (P2Q a) + (B.g2 2).1) - z ((B.g2 1).2 + 2)),
   ("B1 s1", z (plo d (P1Q a) + ((B.r0 2).1 - 2)) - z ((B.r0 0).2 - 2 + 2)),
   ("B1 s2", z (plo d (P2Q a) + ((B.r0 2).1 - 2)) - z ((B.r0 1).2 - 2 + 2)),
   ("start g1", z T0 - z ((B.g1 0).2 + (B.g1 2).2 + 2)),
   ("start g2", z T0 - z ((B.g2 1).2 + (B.g2 2).2 + 2)),
   ("start s1", z T0 - z ((B.r0 0).2 + (B.r0 2).2 + 2)),
   ("start s2", z T0 - z ((B.r0 1).2 + (B.r0 2).2 + 2)),
   ("rst g2", z T0 - z (T + phi d (PrQ a) + (B.g2 2).2 + 2)),
   ("rst R0", z T0 - z (T + phi d (PrQ a) + (B.r0 2).2)),
   ("lo r0.1", z (B.r0 0).1 - 2), ("lo r0.2", z (B.r0 1).1 - 2), ("lo r0.q", z (B.r0 2).1 - 2)]

/-- The conjuncts of `ArbOK`, separately (diagnostics only; the verdict uses `decide (ArbOK …)`). -/
def diag {N : Nat} (d : Design) (net : Net4 N) (b : Bands4 net) (rn : Fin N → RNode) (fuel rw : Nat)
    (a : ArbD N) : List (String × Bool) :=
  let B := bandsOf d a
  let K := kOf B
  [("read g1.r1", decide (RdP d fuel a.gG1 a.i1g1 a.p1g1 a.rq1.w)),
   ("read g1.q", decide (RdP d fuel a.gG1 a.iqg1 a.pqg1 (qW d a))),
   ("INIT g1 = r1 q", decide (InitSpec (gt d a.gG1) (fun v => v a.i1g1 && v a.iqg1))),
   ("read g2.r2", decide (RdP d fuel a.gG2 a.i2g2 a.p2g2 a.rq2.w)),
   ("read g2.q", decide (RdP d fuel a.gG2 a.iqg2 a.pqg2 (qW d a))),
   ("INIT g2 = r2 !q", decide (InitSpec (gt d a.gG2) (fun v => v a.i2g2 && !v a.iqg2))),
   ("read R0.r1", decide (RdP d fuel a.gR a.i1R a.p1R a.rq1.w)),
   ("read R0.r2", decide (RdP d fuel a.gR a.i2R a.p2R a.rq2.w)),
   ("read R0.q", decide (RdP d fuel a.gR a.iqR a.pqR (qW d a))),
   ("INIT R0 = r1 q + r2 !q", decide (InitSpec (gt d a.gR) (fun v => (v a.i1R && v a.iqR) || (v a.i2R && !v a.iqR)))),
   ("read q.r1", decide (RdP d fuel a.gQ a.i1Q a.p1Q a.rq1.w)),
   ("read q.r2", decide (RdP d fuel a.gQ a.i2Q a.p2Q a.rq2.w)),
   ("read q.q", decide (RdP d fuel a.gQ a.iqQ a.pqQ (qW d a))),
   ("read q.rst", decide (RdP d fuel a.gQ a.irQ a.prQ rw)),
   ("read q.A0", decide (RdP d fuel a.gQ a.iA a.pA (rn a.jA).ow)),
   ("INIT q = rst + (A0 ? q : C(r1,!r2))", decide (InitSpec (gt d a.gQ) (fun v => v a.irQ || (if v a.iA then v a.iqQ else
      ((v a.i1Q && !v a.i2Q) || (v a.iqQ && !(!v a.i1Q && v a.i2Q))))))),
   ("six nodes distinct", decide ([a.jc, a.jg1, a.jg2, a.js1, a.js2, a.jR].Nodup)),
   ("ctl node", decide (CtlOK net b rn a.jc a.jA (loCtl B))),
   ("grant 1 node", decide (RdNodeOK d net b rn fuel a.jg1 a.jc (net.src a.jg1 (pin0 net a.jg1)) false
      (rdG (B.g1 0) (B.g1 2) K).loR (rdG (B.g1 0) (B.g1 2) K).hiR (rdG (B.g1 0) (B.g1 2) K).loC
      (rdG (B.g1 0) (B.g1 2) K).hiC a.rq1)),
   ("grant 2 node", decide (RdNodeOK d net b rn fuel a.jg2 a.jc (net.src a.jg2 (pin0 net a.jg2)) true
      (rdG (B.g2 1) (B.g2 2) K).loR (rdG (B.g2 1) (B.g2 2) K).hiR (rdG (B.g2 1) (B.g2 2) K).loC
      (rdG (B.g2 1) (B.g2 2) K).hiC a.rq2)),
   ("shadow 1 node", decide (RdNodeOK d net b rn fuel a.js1 a.jc (net.src a.jg1 (pin0 net a.jg1)) false
      (rdS (B.r0 0) (B.r0 2) K).loR (rdS (B.r0 0) (B.r0 2) K).hiR (rdS (B.r0 0) (B.r0 2) K).loC
      (rdS (B.r0 0) (B.r0 2) K).hiC a.rq1)),
   ("shadow 2 node", decide (RdNodeOK d net b rn fuel a.js2 a.jc (net.src a.jg2 (pin0 net a.jg2)) true
      (rdS (B.r0 1) (B.r0 2) K).loR (rdS (B.r0 1) (B.r0 2) K).hiR (rdS (B.r0 1) (B.r0 2) K).loC
      (rdS (B.r0 1) (B.r0 2) K).hiC a.rq2)),
   ("grant / shadow wires", decide ((rn a.jg1).hasW = true ∧ (rn a.jg1).ow = (gt d a.gG1).out ∧
      (rn a.jg2).hasW = true ∧ (rn a.jg2).ow = (gt d a.gG2).out ∧ (rn a.js1).hasW = false ∧ (rn a.js2).hasW = false)),
   ("R0 node", decide (MgOK net b rn a.jR a.js1 a.js2 (gt d a.gR).out)),
   ("band side conditions", decide (1 ≤ (B.g1 0).1 ∧ 1 ≤ (B.g2 1).1 ∧ 3 ≤ (B.r0 0).1 ∧ 3 ≤ (B.r0 1).1 ∧ 2 ≤ K ∧
      K + 2 ≤ (B.g1 2).1 ∧ K + 2 ≤ (B.g2 2).1 ∧ K + 4 ≤ (B.r0 2).1))]

def run (args : List String) : IO UInt32 := do
  let netp :: bandp :: certp :: arbp :: rest := args
    | do IO.eprintln "usage: xarbnet NETLIST.json BANDS.json CERT.json ARB.json [--top T] [--fuel F]"; return 2
  let j ← readJson netp
  let B0 := parseBands (← readJson bandp)
  let Bd : Bands := { B0 with unit := 1 }
  let (_, top) ← IO.ofExcept (pickTop j (getArg rest "--top"))
  let bt ← IO.ofExcept (buildDesign Bd top)
  let d := bt.d
  let fuel := ((getArg rest "--fuel").bind String.toNat?).getD 64
  let gix : Std.HashMap String Nat := (d.gates.zipIdx).foldl (fun m (g, i) => m.insert g.name i) {}
  let cj ← readJson certp
  let mut A : Array NodeD := #[]
  for nj in gArr cj "nodes" do
    A := A.push (← IO.ofExcept (parseNode gix d nj))
  let N := A.size
  if hN : 0 < N then
    let net := mkNet N hN A
    let b := mkBands N hN A d
    let rn := mkRn N A
    let rw := (bt.inputs.lookup "rig_rst").getD 0
    let aj ← readJson arbp
    let mut AS : Array (ArbD N) := #[]
    let mut anames : Array String := #[]
    let mut wenv : Array (Option Nat × Option Nat) := #[]
    let mut w30 : Array (Option Nat) := #[]
    for x in gArr aj "arbs" do
      AS := AS.push (← IO.ofExcept (parseArb N gix d x))
      anames := anames.push (gStr x "name")
      wenv := wenv.push (wEnv ((jget x "rq1").getD Json.null), wEnv ((jget x "rq2").getD Json.null))
      w30 := w30.push ((jget x "w_r0a0").bind jnat)
    let K := AS.size
    IO.println s!"[xarbnet] {d.gates.length} gates, {N} nodes ({(A.filter (·.virt)).size} virtual), {K} arbiters, fuel {fuel}, 1 ps steps"
    let Trst := ((getArg rest "--T").bind String.toNat?).getD 20000
    let mut nOK := 0
    let mut nRows := 0
    let mut nRowsS := 0
    for h : k in [0:AS.size] do
      let a := AS[k]'h.upper
      let ok := decide (ArbOK d net b rn fuel rw a)
      if ok then nOK := nOK + 1
      let B := bandsOf d a
      let T0 := t0Min d a Trst
      let okR := decide (ArbRowsOK d a Trst T0)
      if ok && okR then nRows := nRows + 1
      let okS := decide (ArbRowsOKS d a Trst T0)
      if ok && okS then nRowsS := nRowsS + 1
      IO.println s!"[xarbnet] arbiter {anames[k]!}: ArbRowsOK {okR} (T {Trst}, T0 {T0}) [Events9ArbNetEdge.arbCond_of_edge / Events9FullArb]"
      if !okR then
        IO.println s!"  ArbRowsOK margins (ps): {(rowsDiag d a Trst T0).filter (fun p => decide (p.2 < 0))}"
        IO.println s!"  B1 with every arc at the same band end (lo-end, hi-end; diagnostic only): {b1Corr d a}"
        IO.println s!"  B1 kappa threshold per reader, x1e6 (corner model: shared band position, path scatter kappa; diagnostic only): {b1Kappa d a}"
      IO.println s!"[xarbnet] arbiter {anames[k]!}: ustate own-q read band ({plo d (PqQ a)}, {phi d (PqQ a)}) [QQuiet window = hi; qclean_of_arb needs lo >= 1]"
      IO.println s!"[xarbnet] arbiter {anames[k]!}: ArbOK {ok}; K {kOf B}, ctl lo {loCtl B}; Dq g1/g2/R0 {B.g1 2}/{B.g2 2}/{B.r0 2}, Dr1 g1/R0 {B.g1 0}/{B.r0 0}, Dr2 g2/R0 {B.g2 1}/{B.r0 1}, DA0 {B.st 4}"
      if !ok then
        for (nm, v) in diag d net b rn fuel rw a do
          if !v then IO.println s!"  FAIL {nm}"
      -- part 2: the rows
      let DA := B.st 4
      let DqR := B.r0 2
      let wcert := r0Read net b a.jA a.jR
      let w34 := match wcert with | some v => some v | none => w30[k]!
      let (we1, we2) := wenv[k]!
      let mut line := s!"  rows (ps; >= 0 holds): hMax {hMax d a}; R0 -> A0 lower delay {match w34 with | some v => toString v | none => "-"} ({if wcert.isSome then "certificate pin band" else "gen.py path, untrusted"})"
      IO.println line
      for (nm, r) in readers d a do
        let we := if nm == "g1" || nm == "s1" then we1 else we2
        let w3 := w34.getD 0
        let b2a := match we with | some w => toString (rowB2a DA w r) | none => "-"
        let clo := match we with | some w => toString (rowClo DA w r) | none => "-"
        let nn := match we with | some w => toString (rowN DA w r) | none => "-"
        let b2b := if w34.isSome then toString (rowB2b DqR DA w3 r) else "-"
        let b2c := if w34.isSome then toString (rowB2c DA w3 r) else "-"
        let chi := if w34.isSome then toString (rowChi DA w3 r) else "-"
        line := s!"  ROW {anames[k]!} {nm}: B1 {rowB1 r} B2a {b2a} B2b {b2b} B2c {b2c} Clo {clo} Chi {chi} | N {nn} | need w {needW DA r}, w_env {match we with | some w => toString w | none => "-"}"
        IO.println line
    -- the owner map, reset classes, shape
    let asF : Fin AS.size → ArbD N := fun k => AS[k.val]'k.isLt
    let own : Fin N → Option (Fin AS.size) := fun jj => (allFin AS.size).find? (fun k => decide (jj ∈ (asF k).nodes))
    let rs : Nat → Nat := fun k => if k < N then (if A[k]!.virt && !A[k]!.mg then A[k]!.rc else 0) else 0
    let okOwn := decide (OwnOK rn asF own)
    let okRs := decide (RsOK asF rs)
    let okFix := decide (FixShape net b rn)
    IO.println s!"[xarbnet] ArbOK {nOK}/{K}; OwnOK {okOwn}; RsOK {okRs}; FixShape {okFix}"
    IO.println s!"[xarbnet] ArbOK and ArbRowsOK {nRows}/{K} (the checked premises of Events9FullArb.design_verdict9_full_arb besides design_verdict9_full's own)"
    IO.println s!"[xarbnet] ArbOK and ArbRowsOKS {nRowsS}/{K} (start rows only; with ArbOrd assumed: Events9FullArb.design_verdict9arbnet_ord)"
    let allOK := nOK == K && okOwn && okRs && okFix
    IO.println s!"VERDICT {if allOK then "ARB-LINK OK" else "ARB-LINK FAILS"} (Events9ArbNet.design_verdict9arbnet: HARB7' and HRst follow from SatPin and the per-arbiter trace conditions ArbCond)"
    return (if allOK then 0 else 1)
  else
    IO.eprintln "empty certificate"; return 2

end Formal.Core.XAudit.Events9ArbNetMain

def main (args : List String) : IO UInt32 := Formal.Core.XAudit.Events9ArbNetMain.run args
