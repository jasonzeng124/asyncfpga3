import Formal.Cells.BWit2Net
import Formal.Cells.FiniteNetBoundMCensus
/-! Auditor P15bc, item 3: Bwit2 statement, axioms, activity census, and negative controls
reproduced WITHOUT editing formal's tree:
(1) formal's control: first entry of mux op 37's `uj0` node list +1 -> the mux checker rejects;
(2) auditor's gate mutation: mux 37's `uj0` checked with the select polarity inverted -> rejects;
(3) auditor's binding mutation: a channel whose request driver is reached through a 1-input join
    (channel 109, out of join op 41 = ushrsi0) re-bound to the join's input contract node instead. -/
open Formal.Cells
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapNet.Wit (CD nv bv)
open Formal.Cells.FiniteRunsWit (sortedB cL rst2 bndD linkB)
open Formal.Cells.AssumeGuaranteeEndsCap (forkOuts joinIns steerIn d0)
open Formal.Cells.FiniteNet
open Formal.Cells.FiniteNetBound (DK FU stJ brC)
open Formal.Cells.FiniteNetBoundM (DKM reqSrcM ackSrcM FGcdNetM muxC bound_censusM gcd_hw_safe_fin_netBM)
open Formal.Cells.FiniteNetWit2 (lkIO faOK jrOK Gf2 Gf3 Gf4 celB celT stB orB orE σT κT)
open Formal.Cells.BWit (shL celTm stTm orTm fkIn jnOut)
open Formal.Cells.BWit2

#check @gcd_hw_fin_netBM_witness
#check @gcd_hw_safe_fin_netBM
#print axioms gcd_hw_fin_netBM_witness
#print axioms gcd_hw_fin_netBM_consistent
#print axioms bwitM_link_env
#print axioms bound_censusM
#print axioms Formal.Cells.FiniteNetBoundMCensus.unbound_req_classes
#print axioms Formal.Cells.FiniteNetBoundMCensus.unbound_ack_classes

-- activity: channels with request edges, total request edges, last edge, out0's edges 
#eval ((List.finRange NC).filter fun c => (cdB c).rq.length > 0).length
#eval ((List.finRange NC).map fun c => (cdB c).rq.length).sum
#eval ((List.finRange NC).map fun c => (cdB c).rq.foldl max 0).foldl max 0
#eval ((cdB out0).rq, (cdB out0).ak)
-- muxes whose two internal joins toggle at least once in the run -/
#eval ((List.finRange NO).filter fun o => isMux o && ((mjN o false).length + (mjN o true).length > 0)).length
#eval ((List.finRange NO).filter fun o => isMux o).length
-- the drivers the witness uses for channels 109 and 113 (outputs of 1-input joins 41, 43) -/
#eval (reqSrcM FU ⟨109, by decide⟩, reqSrcM FU ⟨113, by decide⟩)
#eval (opAt (prodOf ⟨109, by decide⟩) |> fun k => match k with | .join ins o _ _ _ => (ins, o) | _ => ([], ⟨0, by decide⟩))
#eval (mjN ⟨37, by decide⟩ false).take 4

/-! (1) formal's control, reproduced -/
def mjNm (o : Fin NO) (b : Bool) : List Nat :=
  if o.val = 37 ∧ b = false then (match mjN o b with | [] => [] | x :: xs => (x + 1) :: xs)
  else mjN o b

def muxChkM (o : Fin NO) : Bool :=
  match muxC (opAt o) with
  | some (cc, x, y, z) =>
    mjB false (cdB x).rq (cdB cc).rq (selB cc) (tabOf o) (mjNm o false) &&
    mjB true (cdB y).rq (cdB cc).rq (selB cc) (tabOf o) (mjNm o true) &&
    maB false (mjNm o false) (cdB z).ak (tabOf o) (lstN (.ma o false)) &&
    maB true (mjNm o true) (cdB z).ak (tabOf o) (lstN (.ma o true)) &&
    orB (tabOf o) (mjNm o false) (mjNm o true) (lstN (.mo o)) &&
    orTm (tabOf o) (mjNm o false) (mjNm o true) (lstN (.mo o)) &&
    bufB (lstN (.mo o)) (lstN (.md o 0)) && bufB (lstN (.md o 0)) (lstN (.md o 1)) &&
    bndD (cdB cc).dt &&
    sortedB (mjNm o false) && sortedB (mjNm o true) && sortedB (lstN (.mo o)) &&
    sortedB (lstN (.md o 0))
  | none => true

set_option maxRecDepth 100000 in
theorem aud_mux37_orig : muxChk ⟨37, by decide⟩ = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem aud_mux37_mjEdge_rejected : muxChkM ⟨37, by decide⟩ = false := by decide +kernel

/-! (2) select polarity inverted -/
def mjSelInv (o : Fin NO) : Bool :=
  match muxC (opAt o) with
  | some (cc, x, _, _) => mjB false (cdB x).rq (cdB cc).rq (fun t => !selB cc t) (tabOf o) (mjN o false)
  | none => true

set_option maxRecDepth 100000 in
theorem aud_mux37_selinv_rejected : mjSelInv ⟨37, by decide⟩ = false := by decide +kernel

/-! (3) not a mutation: on the witness, channel 109 (the request into link 233, downstream of the
1-input join op 41 = ushrsi0 through a fork) is channel 85's request (ushrsi0's e0 side, out of
link 220) shifted by wR 109 - 1 ticks: the compute unit is a wire of a few ticks in this run. -/
#eval (wR ⟨109, by decide⟩, (cdB ⟨85, by decide⟩).rq, (cdB ⟨109, by decide⟩).rq, wR ⟨113, by decide⟩, (cdB ⟨113, by decide⟩).rq)
