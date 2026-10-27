import Formal.Cells.ArbAnalog
import Formal.Cells.ArbCorners
import Formal.Cells.ArbResolve
import Formal.Cells.CElemCore
import Formal.Cells.MergeMuxSI
import Formal.Cells.PipeTimed
import Formal.Cells.PipeTimedN
import Formal.Core.Delay.CornerDiff
import Formal.Core.Env
import Formal.Core.Substrate
import Formal.Core.Substrate.Chan
import Formal.Core.Substrate.CornerNat
import Formal.Core.Substrate.Legacy
import Formal.Core.Substrate.Real
import Formal.Net.Bridge
import Formal.Net.BridgeRing
import Formal.Net.BridgeTransport
import Formal.Net.BridgeWire
import Formal.Net.EndToEnd
import Formal.Net.EndToEndRace
import Formal.Net.EndToEndToy
import Formal.Net.FasmLink.Basic
import Formal.Net.FasmLink.LinkArb
import Formal.Net.FasmLink.Proofs
import Formal.Net.FasmLink.S1
import Formal.Net.FasmLink.S2
import Formal.Net.FasmLink.S3
import Formal.Net.FasmLink.S4
import Formal.Net.Kahn
import Formal.Net.KahnBounded
import Formal.Net.KahnGcd
import Formal.Net.KahnGcdCM
import Formal.Net.KahnGcdNested
import Formal.Net.KahnLTS
import Formal.Net.Muller
import Formal.Net.MullerRun
import Formal.Net.MullerSI
open Lean Elab Command

def auditMods : List Name := [`Formal.Cells.ArbAnalog, `Formal.Cells.ArbCorners, `Formal.Cells.ArbResolve, `Formal.Cells.CElemCore, `Formal.Cells.MergeMuxSI, `Formal.Cells.PipeTimed, `Formal.Cells.PipeTimedN, `Formal.Core.Delay.CornerDiff, `Formal.Core.Env, `Formal.Core.Substrate, `Formal.Core.Substrate.Chan, `Formal.Core.Substrate.CornerNat, `Formal.Core.Substrate.Legacy, `Formal.Core.Substrate.Real, `Formal.Net.Bridge, `Formal.Net.BridgeRing, `Formal.Net.BridgeTransport, `Formal.Net.BridgeWire, `Formal.Net.EndToEnd, `Formal.Net.EndToEndRace, `Formal.Net.EndToEndToy, `Formal.Net.FasmLink.Basic, `Formal.Net.FasmLink.LinkArb, `Formal.Net.FasmLink.Proofs, `Formal.Net.FasmLink.S1, `Formal.Net.FasmLink.S2, `Formal.Net.FasmLink.S3, `Formal.Net.FasmLink.S4, `Formal.Net.Kahn, `Formal.Net.KahnBounded, `Formal.Net.KahnGcd, `Formal.Net.KahnGcdCM, `Formal.Net.KahnGcdNested, `Formal.Net.KahnLTS, `Formal.Net.Muller, `Formal.Net.MullerRun, `Formal.Net.MullerSI]

elab "#audit_axioms" : command => do
  let env ← getEnv
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut nThm : Nat := 0
  let mut bad : Array (Name × List Name) := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mn := env.header.moduleNames[idx.toNat]!
    if !(auditMods.contains mn) then continue
    match ci with
    | .thmInfo _ =>
      nThm := nThm + 1
      let axs ← liftCoreM <| Lean.collectAxioms n
      let extra := axs.toList.filter (fun a => !(ok.contains a))
      if !extra.isEmpty then bad := bad.push (n, extra)
    | _ => pure ()
  logInfo m!"theorems checked: {nThm}; non-standard axioms: {bad.size}"
  for (n, e) in bad do logInfo m!"{n}: {e}"

#audit_axioms
