import Formal.Core.Env

/-!
# Formal.Core.EnvFast.Steer — bd_steer (bd_ctl.v) under its bundling contract

Shard A. Notes: `formal/notes/A-envfast-2.md`. Small enough (34 states) for
`Env.certify` with the in-kernel `reachTree`, so no tables or certificate.

`bd_steer`: `req0 = req·¬s` (O5), `req1 = req·s` (O6) of one LUT6_2
(`bd_steer_u`, bd_ctl.v:79, free pins root first `[s, req]` for both outputs),
`ack = ack0 + ack1` (`bd_steer_uack`, bd_ctl.v:82, `[ack1, ack0]`).
Signals: `req 0, s 1, rdy 2, r0 3, r1 4, a0 5, a1 6, ack 7` (`rdy`: the
sender's private "s is out" event). Sender: `s` moves only while `req` and
`ack` are low and before `rdy`; `req` rises after `rdy` (H_BUNDLE, encoded
causally, as in `Env.linkModel`), falls after `ack↑`. Receivers: any
four-phase partners on `r0/a0` and `r1/a1`. Every fork isochronic.

* `steer_sound`: speed-independent, every MIC at both LUTs hazard-free, live,
  and a receiver acknowledges only when `s` named it. No timing assumption
  beyond the bundling contract — the header's argument ("within a transaction
  s is a constant … return to zero is immediate and unconditional"), derived.
* `steer_needs_setup`: if `s` may move whenever `req` is low (no setup
  discipline), `s↑ ∥ req↑` meet at the LUT: a static-0 hazard on `req0`
  (the wrong branch can see a request pulse).
-/

namespace Formal.Core.EnvFast

open Formal.Core.LutCells Formal.Core.Env

def steerModel : Model where
  n := 8
  gates := [.lut 3 bd_steer_u .O5 [1, 0], .lut 4 bd_steer_u .O6 [1, 0], .lut 7 bd_steer_uack .O [6, 5]]
  env := [(1, fun s => !bit s 2 && !bit s 0 && !bit s 7),
          (2, fun s => (!bit s 2 && !bit s 0 && !bit s 7) || (bit s 2 && bit s 0)),
          (0, fun s => (!bit s 0 && bit s 2 && !bit s 7) || (bit s 0 && bit s 7)),
          (5, fun s => bit s 5 != bit s 3),
          (6, fun s => bit s 6 != bit s 4)]
  prio := []
  inits := [0]

/-- Liveness, and a receiver's acknowledge rises only for the branch `s` names. -/
def steerQ (M : Model) (s : Nat) : Bool :=
  live M s && !(bit (excMask M s) 5 && !bit s 5 && bit s 1) &&
    !(bit (excMask M s) 6 && !bit s 6 && !bit s 1)

/-- Negative control: `s` may move whenever `req` is low (no `rdy` discipline). -/
def steerFree : Model :=
  { steerModel with env := [(1, fun s => !bit s 0),
      (0, fun s => (!bit s 0 && !bit s 7) || (bit s 0 && bit s 7)),
      (5, fun s => bit s 5 != bit s 3),
      (6, fun s => bit s 6 != bit s 4)] }

theorem steer_cert : certify steerModel (steerQ steerModel) (reachTree steerModel 1000) = true ∧
    (reachTree steerModel 1000).size = 34 := by
  decide +kernel

/-- **bd_steer is speed-independent and hazard-free under its bundling
contract alone**, against arbitrary four-phase receivers: both LUT outputs and
the acknowledge OR see only hazard-free MICs, every excitation persists, no
deadlock, and only the branch named by `s` is acknowledged. 34 states. -/
theorem steer_sound : Sound steerModel (steerQ steerModel) := certify_sound steer_cert.1

/-- **The setup half of the bundling contract is necessary**: `s↑` and `req↑`
together at the steer LUT (`[s, req]: 00 → 11`) is a static-0 function hazard
on `req0 = req·¬s` (the cube crosses `s = 0, req = 1`). -/
theorem steer_needs_setup :
    ∃ s, Reach steerFree s ∧ (0, post steerFree s 0) ∈ succs steerFree s ∧
      (!lutOK steerFree s 0 (.lut 3 bd_steer_u .O5 [1, 0]) 0) = true :=
  witness_sound (M := steerFree) (s0 := 0) (ts := [1]) (t := 0)
    (bad := fun s t => !lutOK steerFree s t (.lut 3 bd_steer_u .O5 [1, 0]) 0) (by decide) (by decide +kernel)

end Formal.Core.EnvFast
