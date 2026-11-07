import Formal.Cells.FiniteNetBoundM
import Formal.Cells.AssumeGuaranteeCap

/-!
# Probe Belab2 (shard B): where the remaining unbound link sides end

`FiniteNetBoundM.bound_censusM` counts 136 of 175 links bound on both sides. This file names,
by kernel, the operator class at which each of the 39 unbound sides ends (following the same
wires `reqSrcM`/`ackSrcM` follow: tied forks on the request side; 1- and 2-input joins and a
mux's control acknowledge on the acknowledge side).

**Proved:** `unbound_req_classes`: the 24 unbound request sides end at an `amerge` (23) or a
source (1); `unbound_ack_classes`: the 15 unbound acknowledge sides end at a `muxn` (4), an
`amerge` (5) or a fork tree (`forkH5` 4, `forkH6` 2). So with the arbiter (`amerge`) gate-
modelled the request side would be complete but for the source. Core Lean only.
-/

namespace Formal.Cells.FiniteNetBoundMCensus
open Formal.Net Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Cells.FiniteNetBound (FU)
open Formal.Cells.FiniteNetBoundM (reqSrcM ackSrcM)
open Formal.Cells.AssumeGuaranteeCap (kname census)
open Formal.Cells.AssumeGuaranteeEndsCap (d0)

/-- The operator at which a request side ends (through tied forks and 1-input joins). -/
def reqEnd : Nat → Fin NC → String
  | 0, _ => "?"
  | F + 1, c =>
    match opAt (prodOf c) with
    | .forkG i os => if 2 ≤ os.length ∧ os.length ≤ 4 then reqEnd F i else kname (opAt (prodOf c))
    | .forkH i os _ _ _ _ =>
        if 2 ≤ os.length ∧ os.length ≤ 4 then reqEnd F i else kname (opAt (prodOf c))
    | .join ins _ _ _ _ => if ins.length = 1 then reqEnd F (ins.getD 0 d0) else kname (opAt (prodOf c))
    | .bjoin ins _ _ _ => if ins.length = 1 then reqEnd F (ins.getD 0 d0) else kname (opAt (prodOf c))
    | k => kname k

/-- The operator at which an acknowledge side ends (through 1- and 2-input joins and a mux's
control acknowledge). -/
def ackEnd : Nat → Fin NC → String
  | 0, _ => "?"
  | F + 1, c =>
    match opAt (consOf c) with
    | .join ins z _ _ _ => if ins.length = 2 ∨ ins.length = 1 then ackEnd F z else kname (opAt (consOf c))
    | .bjoin ins z _ _ => if ins.length = 2 ∨ ins.length = 1 then ackEnd F z else kname (opAt (consOf c))
    | .mux cc _ _ z _ => if c = cc then ackEnd F z else "mux"
    | k => kname k

def unboundReq : List String :=
  (List.finRange NO).filterMap fun o => match opAt o with
    | .link i _ => if (reqSrcM FU i).isNone then some (reqEnd FU i) else none
    | _ => none

def unboundAck : List String :=
  (List.finRange NO).filterMap fun o => match opAt o with
    | .link _ o' => if (ackSrcM FU o').isNone then some (ackEnd FU o') else none
    | _ => none

set_option maxRecDepth 100000

theorem unbound_req_classes : census unboundReq = [("src", 1), ("amerge", 23)] := by decide +kernel
theorem unbound_ack_classes : census unboundAck = [("muxn", 4), ("amerge", 5), ("forkH5", 4), ("forkH6", 2)] := by decide +kernel

end Formal.Cells.FiniteNetBoundMCensus
