import Formal.Cells.BWitNet

/-! Auditor P14bc, claim B (Bwit). Not part of the formal tree.
1. Axioms of the witness theorems and of the self-audit rejection.
2. Census of the witness network: which pins are driven by tied (gate-model) cells and which by
   pinless contract cells; wire-delay histogram; amount of activity (edge counts).
3. Negative controls: (a) the journal's wire-delay mutant (channel 20 request wire 2 -> 1),
   restated without editing their data; (b) a gate-function mutant: a 2-way fork acknowledge
   C-element checked against OR instead of the C-element must fail. -/

open Formal.Cells Formal.Cells.BWit Formal.Net Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Cells.FiniteNetBound (reqSrc ackSrc FU)
open Formal.Cells.FiniteNetWit2 (Cl celB Gf2)
open Formal.Cells.AssumeGuaranteeEndsCap (forkOuts d0)
open Formal.Cells.AssumeGuaranteeEnds (GPin)

#print axioms gcd_hw_fin_netB_witness
#print axioms gcd_hw_fin_netB_consistent
#print axioms bwit_ok
#print axioms Rej.chW_net_not_bound
#print axioms Formal.Cells.FiniteNetBound.gcd_hw_safe_fin_netB
#check @gcd_hw_fin_netB_witness

def isContract : Cl → Bool
  | .rq _ => true
  | .ak _ => true
  | _ => false

def allCells : List Cl :=
  ((List.finRange NO).flatMap fun o => [Cl.lk o, .fa o, .jr o, .sb o true, .sb o false, .ao o])

/-- (#tied cells with pins, #pins, #pins driven by a contract cell, #pins driven by a tied cell) -/
def pinCensus : Nat × Nat × Nat × Nat :=
  let cs := allCells.filter fun c => !(pinsB c).isEmpty
  let ps := cs.flatMap pinsB
  (cs.length, ps.length, (ps.filter fun p => isContract p.drv).length,
    (ps.filter fun p => !isContract p.drv).length)

#eval pinCensus

-- channels whose request / acknowledge driver the netlist leaves to a contract cell
#eval ((List.finRange NC).filter fun c => (reqSrc FU c).isNone).length
#eval ((List.finRange NC).filter fun c => (ackSrc FU c).isNone).length
#eval NC

-- wire delay histogram over all channels (request, acknowledge)
#eval ((List.finRange NC).map fun c => wR c).foldl (fun (a : Nat × Nat × Nat) w =>
  if w = 1 then (a.1 + 1, a.2) else if w = 2 then (a.1, a.2.1 + 1, a.2.2) else (a.1, a.2.1, a.2.2 + 1)) (0, 0, 0)
#eval ((List.finRange NC).map fun c => wA c).foldl (fun (a : Nat × Nat × Nat) w =>
  if w = 1 then (a.1 + 1, a.2) else if w = 2 then (a.1, a.2.1 + 1, a.2.2) else (a.1, a.2.1, a.2.2 + 1)) (0, 0, 0)

-- activity: total request edges, number of channels with at least one edge, max edge time
#eval (((List.finRange NC).map fun c => (cdB c).rq.length).foldl (· + ·) 0,
  ((List.finRange NC).filter fun c => (cdB c).rq.length > 0).length,
  ((List.finRange NC).map fun c => (cdB c).rq.getLastD 0).foldl max 0)
#eval out0CloseB
#eval ((cdB out0).rq, (cdB out0).ak)

/-! ### Negative control (a): wire delay of channel 20's request 2 -> 1 -/
def wR' (c : Fin NC) : Nat := if c.val = 20 then 1 else wR c

def wireChk' (n : Nat) : Bool :=
  if h : n < NC then
    let c : Fin NC := ⟨n, h⟩
    decide (1 ≤ wR' c) && decide (1 ≤ wA c) &&
    ((cdB c).rq == shL (wR' c - 1) (lstN (dR c))) && ((cdB c).ak == shL (wA c - 1) (lstN (dA c))) &&
    sortedB (cdB c).rq && sortedB (cdB c).ak
  else true
where sortedB := Formal.Cells.FiniteRunsWit.sortedB

theorem orig_20 : wireChk 20 = true := by decide +kernel
theorem mut_20 : wireChk' 20 = false := by decide +kernel

/-! ### Negative control (b): a 2-way fork's acknowledge cell checked as OR instead of C-element -/
def fork2 : List Nat :=
  ((List.finRange NO).filter fun o => match forkOuts (opAt o) with
    | some os => os.length == 2 && (lstN (.fa o)).length > 0
    | none => false).map (·.val)
#eval fork2.take 5

def GfOr (p : Fin 2 → Bool) (_q : Bool) : Bool := p 0 || p 1

def o0 : Fin NO := ⟨0, by decide⟩
def outs0 : List (Fin NC) := (forkOuts (opAt o0)).getD []
#eval outs0
theorem fork0_orig : celB Gf2 (fun i : Fin 2 => (cdB (outs0.getD i.val d0)).ak) (lstN (.fa o0)) = true := by
  decide +kernel
theorem fork0_mut_or : celB GfOr (fun i : Fin 2 => (cdB (outs0.getD i.val d0)).ak) (lstN (.fa o0)) = false := by
  decide +kernel
#print axioms mut_20
#print axioms fork0_mut_or
