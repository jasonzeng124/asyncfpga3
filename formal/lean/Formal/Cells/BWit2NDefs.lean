import Formal.Cells.BWit2Lib
import Formal.Cells.BWit2NData
import Formal.Cells.BWitNDefs
import Formal.Cells.FiniteNetBoundM

/-!
# Probe Bwit2 (shard B): the mux-extended driver-bound network on the run `chB` of `BWit2Data`

As `BWitNDefs`, with every `bd_mux` gate-modelled: cells `mj o b` (joins), `ma o b`
(acknowledges), `md o i` (the two `udly` buffers), `mo o` (`uor`); the drivers are
`FiniteNetBoundM.reqSrcM`/`ackSrcM`; the internal mux nodes are generated lists (`mj0L`,
`mj1L`, `moL`, `md0L`), every other node is the channel signal it drives one tick early.
Definitions and Boolean checks; kernel checks in `BWit2NChk`. Core Lean only.
-/

namespace Formal.Cells.BWit2
open Formal.Cells
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapNet.Wit (CD nv bv)
open Formal.Cells.FiniteRunsWit (sortedB cL rst2 bndD linkB)
open Formal.Cells.AssumeGuaranteeEnds (GPin gE GC2 GC3 GC4)
open Formal.Cells.AssumeGuaranteeEndsNet (GD)
open Formal.Cells.AssumeGuaranteeEndsCap (forkOuts joinIns steerIn d0)
open Formal.Cells.FiniteNet
open Formal.Cells.FiniteNetBound (DK FU stJ brC)
open Formal.Cells.FiniteNetBoundM (DKM reqSrcM ackSrcM FGcdNetM muxC)
open Formal.Cells.FiniteNetWit2 (lkIO faOK jrOK Gf2 Gf3 Gf4 celB celT stB orB orE σT κT)
open Formal.Cells.BWit (shL celTm stTm orTm fkIn jnOut)

/-! ## 1. Cells, drivers, nodes, pins -/

inductive Cm
  | lk (o : Fin NO)
  | fa (o : Fin NO)
  | jr (o : Fin NO)
  | sb (o : Fin NO) (b : Bool)
  | ao (o : Fin NO)
  | mj (o : Fin NO) (b : Bool)
  | ma (o : Fin NO) (b : Bool)
  | md (o : Fin NO) (i : Fin 2)
  | mo (o : Fin NO)
  | rq (c : Fin NC)
  | ak (c : Fin NC)

def toCm : DKM → Cm
  | .base (.lk o) => .lk o
  | .base (.fa o) => .fa o
  | .base (.jr o) => .jr o
  | .base (.sb o b) => .sb o b
  | .base (.ao o) => .ao o
  | .md o i => .md o i
  | .ma o b => .ma o b

def dR (c : Fin NC) : Cm := match reqSrcM FU c with
  | some d => toCm d
  | none => .rq c

def dA (c : Fin NC) : Cm := match ackSrcM FU c with
  | some d => toCm d
  | none => .ak c

def isMux (o : Fin NO) : Bool := (muxC (opAt o)).isSome

def mjN (o : Fin NO) (b : Bool) : List Nat := (if b then mj1L else mj0L).getD o.val []

/-- Every cell's node, as an event list (`cL` form). -/
def lstN : Cm → List Nat
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
  | .mj o b => mjN o b
  | .ma o b => match muxC (opAt o) with
    | some (_, x, y, _) => (cdB (if b then y else x)).ak
    | none => []
  | .md o i => if i.val = 0 then md0L.getD o.val [] else
      (match muxC (opAt o) with
        | some (_, _, _, z) => (cdB z).rq
        | none => [])
  | .mo o => moL.getD o.val []
  | .rq c => (cdB c).rq
  | .ak c => (cdB c).ak

def wR (c : Fin NC) : Nat := wRT.getD c.val 1
def wA (c : Fin NC) : Nat := wAT.getD c.val 1

def pRB (c : Fin NC) : GPin Cm := ⟨dR c, bv (cdB c).rq, wR c, wR c, fun _ => 0⟩
def pAB (c : Fin NC) : GPin Cm := ⟨dA c, bv (cdB c).ak, wA c, wA c, fun _ => 0⟩
def apB (t f : Fin NC) (b : Bool) : GPin Cm := pAB (brC t f b)
/-- An internal mux pin: a unit wire from cell `d`'s node. -/
def pIn (d : Cm) : GPin Cm := ⟨d, bv (lstN d), 1, 1, fun _ => 0⟩

def faPinsB (o : Fin NO) : List (GPin Cm) :=
  match forkOuts (opAt o) with
  | some os => os.map pAB
  | none => []

def jrPinsB (o : Fin NO) : List (GPin Cm) :=
  match joinIns (opAt o) with
  | some ins => ins.map pRB
  | none => []

def pinsB : Cm → List (GPin Cm)
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
  | .mj o b => match muxC (opAt o) with
    | some (cc, x, y, _) => [pRB (if b then y else x), pRB cc]
    | none => []
  | .ma o b => match muxC (opAt o) with
    | some (_, _, _, z) => [pIn (.mj o b), pAB z]
    | none => []
  | .md o i => if isMux o then [pIn (if i.val = 0 then .mo o else .md o 0)] else []
  | .mo o => if isMux o then [pIn (.mj o false), pIn (.mj o true)] else []
  | .rq _ => []
  | .ak _ => []

def DB : GD Cm where
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

/-- The mux-extended driver-bound elaboration of gcd_hw on `chB`. -/
def NBm : FGcdNetM where
  ι := Cm
  D := DB
  lk := .lk
  fa := .fa
  jr := .jr
  sb := .sb
  ao := .ao
  mj := .mj
  ma := .ma
  md := .md
  mo := .mo

def nB (c : Cm) : Nat := (lstN c).length
def LB (c : Cm) (j : Nat) : Prop := j < nB c

/-! ## 2. Checks -/

def wireChk (n : Nat) : Bool :=
  if h : n < NC then
    let c : Fin NC := ⟨n, h⟩
    decide (1 ≤ wR c) && decide (1 ≤ wA c) &&
    ((cdB c).rq == shL (wR c - 1) (lstN (dR c))) && ((cdB c).ak == shL (wA c - 1) (lstN (dA c))) &&
    sortedB (cdB c).rq && sortedB (cdB c).ak
  else true

def lkChk (o : Fin NO) : Bool :=
  match lkIO (opAt o) with
  | some (i, o') =>
    linkB (cdB i) (cdB o') &&
    (List.range (min (cdB i).rq.length ((cdB o').ak.length + 1))).all
      (fun j => (cdB o').rq.getD j 1 == FiniteNetWit.τ1 (cdB i) (cdB o') j) &&
    (min (cdB i).rq.length ((cdB o').ak.length + 1) == (cdB o').rq.length) &&
    decide (1 ≤ (lstN (dR i)).getD 0 1) && sortedB (lstN (dR i))
  | none => true

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

def selB (j : Fin NC) (t : Nat) : Bool := nv (cdB j).d0 (cdB j).dt t % 2 == 1

def tabOf (o : Fin NO) : List Bool := tabB.getD o.val []

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

/-- A mux: both joins, both acknowledges, the OR and the two buffers. -/
def muxChk (o : Fin NO) : Bool :=
  match muxC (opAt o) with
  | some (cc, x, y, z) =>
    mjB false (cdB x).rq (cdB cc).rq (selB cc) (tabOf o) (mjN o false) &&
    mjB true (cdB y).rq (cdB cc).rq (selB cc) (tabOf o) (mjN o true) &&
    maB false (mjN o false) (cdB z).ak (tabOf o) (lstN (.ma o false)) &&
    maB true (mjN o true) (cdB z).ak (tabOf o) (lstN (.ma o true)) &&
    orB (tabOf o) (mjN o false) (mjN o true) (lstN (.mo o)) &&
    orTm (tabOf o) (mjN o false) (mjN o true) (lstN (.mo o)) &&
    bufB (lstN (.mo o)) (lstN (.md o 0)) && bufB (lstN (.md o 0)) (lstN (.md o 1)) &&
    bndD (cdB cc).dt &&
    sortedB (mjN o false) && sortedB (mjN o true) && sortedB (lstN (.mo o)) &&
    sortedB (lstN (.md o 0))
  | none => true

/-- The internal node lists are sorted (for every operator). -/
def srtChk (o : Fin NO) : Bool :=
  sortedB (mjN o false) && sortedB (mjN o true) && sortedB (moL.getD o.val []) &&
  sortedB (md0L.getD o.val [])

def opChkB (n : Nat) : Bool :=
  if h : n < NO then
    lkChk ⟨n, h⟩ && faChkB ⟨n, h⟩ && jrChkB ⟨n, h⟩ && stChkB ⟨n, h⟩ && muxChk ⟨n, h⟩ &&
    srtChk ⟨n, h⟩
  else true

end Formal.Cells.BWit2
