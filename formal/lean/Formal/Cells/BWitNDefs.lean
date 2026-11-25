import Formal.Cells.BWitLib
import Formal.Cells.BWitNData
import Formal.Cells.FiniteNetBound
import Formal.Cells.FiniteNetWit2

/-!
# Probe Bwit (shard B): the driver-bound gate-level network on the gate-timed run `chB`

Definitions and Boolean checks (kernel-checked in `BWitNChk`, used in `BWitNet`).

* Cells (`FiniteNetWit2.Cl`): links `lk o`, fork acknowledge C-elements `fa o`, join request
  C-elements `jr o`, steer branches `sb o b`, steer acknowledge ORs `ao o`, and one CONTRACT
  cell per channel signal (`rq c`, `ak c`).
* Every tied cell's node is the channel signal it drives, one tick earlier (`lstN`: a link's
  output request, a fork's input acknowledge, a join's output request, a steer branch's
  request, a steer's input acknowledge).
* Every pin reading channel `c` is driven by the cell the NETLIST names (`dR`/`dA`, from
  `FiniteNetBound.reqSrc`/`ackSrc`); only where the netlist names no B cell (mux, muxn,
  amerge, source, sink, wide join, fork tree) is the driver the channel's contract cell.
  Its wire delay is `wRT`/`wAT` (generated), checked: the pin's event list is the driver's
  node list shifted by `w - 1` (`wireChk`).
* Every cell's edge function is its node's event list (`τ c j = (lstN c).getD j 1`).
Core Lean only.
-/

namespace Formal.Cells.BWit
open Formal.Cells
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapNet.Wit (CD nv bv)
open Formal.Cells.FiniteRunsWit (sortedB cL rst2 bndD linkB)
open Formal.Cells.AssumeGuaranteeEnds (GPin gE GC2 GC3 GC4)
open Formal.Cells.AssumeGuaranteeEndsNet (GD)
open Formal.Cells.AssumeGuaranteeEndsCap (forkOuts joinIns steerIn d0)
open Formal.Cells.FiniteNet
open Formal.Cells.FiniteNetBound (DK reqSrc ackSrc FU stJ brC)
open Formal.Cells.FiniteNetWit2 (Cl lkIO faOK jrOK Gf2 Gf3 Gf4 celB celT stB orB orE σT κT)

/-! ## 1. Drivers, nodes, pins -/

def toCl : DK → Cl
  | .lk o => .lk o
  | .fa o => .fa o
  | .jr o => .jr o
  | .sb o b => .sb o b
  | .ao o => .ao o

/-- The cell driving channel `c`'s request: the netlist's B cell, else `c`'s contract cell. -/
def dR (c : Fin NC) : Cl := match reqSrc FU c with
  | some d => toCl d
  | none => .rq c

/-- The cell driving channel `c`'s acknowledge. -/
def dA (c : Fin NC) : Cl := match ackSrc FU c with
  | some d => toCl d
  | none => .ak c

def fkIn : K NC → Option (Fin NC)
  | .forkG i _ => some i
  | .forkH i _ _ _ _ _ => some i
  | _ => none

def jnOut : K NC → Option (Fin NC)
  | .join _ o _ _ _ => some o
  | .bjoin _ o _ _ => some o
  | _ => none

/-- Every cell's node, as an event list (`cL` form): the signal it drives at wire 1. -/
def lstN : Cl → List Nat
  | .lk o => match lkIO (opAt o) with
    | some (_, o') => (cdB o').rq
    | none => []
  | .fa o => if faOK o then (match fkIn (opAt o) with
      | some i => (cdB i).ak
      | none => []) else []
  | .jr o => if jrOK o then (match jnOut (opAt o) with
      | some z => (cdB z).rq
      | none => []) else []
  | .sb o b => match stJ (opAt o) with
    | some (_, t, f) => (cdB (brC t f b)).rq
    | none => []
  | .ao o => match stJ (opAt o) with
    | some (j, _, _) => (cdB j).ak
    | none => []
  | .rq c => (cdB c).rq
  | .ak c => (cdB c).ak

def wR (c : Fin NC) : Nat := wRT.getD c.val 1
def wA (c : Fin NC) : Nat := wAT.getD c.val 1

def pRB (c : Fin NC) : GPin Cl := ⟨dR c, bv (cdB c).rq, wR c, wR c, fun _ => 0⟩
def pAB (c : Fin NC) : GPin Cl := ⟨dA c, bv (cdB c).ak, wA c, wA c, fun _ => 0⟩
def apB (t f : Fin NC) (b : Bool) : GPin Cl := pAB (brC t f b)

def faPinsB (o : Fin NO) : List (GPin Cl) :=
  match forkOuts (opAt o) with
  | some os => os.map pAB
  | none => []

def jrPinsB (o : Fin NO) : List (GPin Cl) :=
  match joinIns (opAt o) with
  | some ins => ins.map pRB
  | none => []

def pinsB : Cl → List (GPin Cl)
  | .lk o => match lkIO (opAt o) with
    | some (i, o') => [pRB i, pAB o']
    | none => []
  | .fa o => faPinsB o
  | .jr o => jrPinsB o
  | .sb o _ => match stJ (opAt o) with
    | some (j, _, _) => [pRB j]
    | none => []
  | .ao o => match stJ (opAt o) with
    | some (_, t, f) => [apB t f false, apB t f true]
    | none => []
  | .rq _ => []
  | .ak _ => []

def DB : GD Cl where
  O c := cL (lstN c)
  τ c j := (lstN c).getD j 1
  lo _ := 1
  hi _ := 1
  fl _ := 1
  fh _ := 1
  qp c := bv (lstN c)
  rst := rst2
  R := 2
  pins := pinsB

/-- The driver-bound elaboration of gcd_hw on `chB`. -/
def NBn : FGcdNet where
  ι := Cl
  D := DB
  lk := .lk
  fa := .fa
  jr := .jr
  sb := .sb
  ao := .ao

def nB (c : Cl) : Nat := (lstN c).length

def LB (c : Cl) (j : Nat) : Prop := j < nB c

/-! ## 2. Checks -/

/-- Channel `c`: both pins are wires (delay `≥ 1`) of their drivers' nodes; lists sorted. -/
def wireChk (n : Nat) : Bool :=
  if h : n < NC then
    let c : Fin NC := ⟨n, h⟩
    decide (1 ≤ wR c) && decide (1 ≤ wA c) &&
    ((cdB c).rq == shL (wR c - 1) (lstN (dR c))) && ((cdB c).ak == shL (wA c - 1) (lstN (dA c))) &&
    sortedB (cdB c).rq && sortedB (cdB c).ak
  else true

/-- A link: Bfin's checker, its node edges, its request driver's first edge, edge count. -/
def lkChk (o : Fin NO) : Bool :=
  match lkIO (opAt o) with
  | some (i, o') =>
    linkB (cdB i) (cdB o') &&
    (List.range (min (cdB i).rq.length ((cdB o').ak.length + 1))).all
      (fun j => (cdB o').rq.getD j 1 == FiniteNetWit.τ1 (cdB i) (cdB o') j) &&
    (min (cdB i).rq.length ((cdB o').ak.length + 1) == (cdB o').rq.length) &&
    decide (1 ≤ (lstN (dR i)).getD 0 1) && sortedB (lstN (dR i))
  | none => true

def celTm {k : Nat} (pl : Fin k → List Nat) (Ln : List Nat) : Bool :=
  (List.range Ln.length).all (fun j => Ln.getD j 1 == celT pl Ln j)

def celChkB (sel : CD → List Nat) (cs : List (Fin NC)) (Ln : List Nat) : Bool :=
  if cs.length = 2 then
    celB Gf2 (fun i : Fin 2 => sel (cdB (cs.getD i.val d0))) Ln &&
    celTm (fun i : Fin 2 => sel (cdB (cs.getD i.val d0))) Ln
  else if cs.length = 3 then
    celB Gf3 (fun i : Fin 3 => sel (cdB (cs.getD i.val d0))) Ln &&
    celTm (fun i : Fin 3 => sel (cdB (cs.getD i.val d0))) Ln
  else if cs.length = 4 then
    celB Gf4 (fun i : Fin 4 => sel (cdB (cs.getD i.val d0))) Ln &&
    celTm (fun i : Fin 4 => sel (cdB (cs.getD i.val d0))) Ln
  else true

def faChkB (o : Fin NO) : Bool :=
  match forkOuts (opAt o) with
  | some os => celChkB CD.ak os (lstN (.fa o))
  | none => true

def jrChkB (o : Fin NO) : Bool :=
  match joinIns (opAt o) with
  | some ins => if ins.length = 2 then celChkB CD.rq ins (lstN (.jr o)) else true
  | none => true

/-- The select of a steer on channel `j`: bit 0 of its bus. -/
def selB (j : Fin NC) (t : Nat) : Bool := nv (cdB j).d0 (cdB j).dt t % 2 == 1

def tabOf (o : Fin NO) : List Bool := tabB.getD o.val []

def stTm (b : Bool) (r : List Nat) (tab : List Bool) (Ln : List Nat) : Bool :=
  (List.range Ln.length).all (fun j => Ln.getD j 1 ==
    (if cL Ln (r.getD (AssumeGuaranteeEnds.sN (κT tab b) j) 1 + 1 + 1) = PipeTimed.Vph j then
      r.getD (AssumeGuaranteeEnds.sN (κT tab b) j) 1 + 1 + 1
     else r.getD (AssumeGuaranteeEnds.sN (κT tab b) j) 1 + 1 + 2))

def orTm (tab : List Bool) (a0 a1 Ln : List Nat) : Bool :=
  (List.range Ln.length).all (fun k => Ln.getD k 1 ==
    (if cL Ln (orE tab a0 a1 k + 1) = PipeTimed.Vph k then orE tab a0 a1 k + 1
     else orE tab a0 a1 k + 2))

def stChkB (o : Fin NO) : Bool :=
  match stJ (opAt o) with
  | some (j, t, f) =>
    stB true (cdB j).rq (selB j) (tabOf o) (lstN (.sb o true)) &&
    stTm true (cdB j).rq (tabOf o) (lstN (.sb o true)) &&
    stB false (cdB j).rq (selB j) (tabOf o) (lstN (.sb o false)) &&
    stTm false (cdB j).rq (tabOf o) (lstN (.sb o false)) &&
    orB (tabOf o) (cdB f).ak (cdB t).ak (lstN (.ao o)) &&
    orTm (tabOf o) (cdB f).ak (cdB t).ak (lstN (.ao o)) && bndD (cdB j).dt
  | none => true

def opChkB (n : Nat) : Bool :=
  if h : n < NO then lkChk ⟨n, h⟩ && faChkB ⟨n, h⟩ && jrChkB ⟨n, h⟩ && stChkB ⟨n, h⟩ else true

end Formal.Cells.BWit
