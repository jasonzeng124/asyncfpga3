import Formal.Core.EnvFast.Steer
import Formal.Cells.PipeTimed

/-!
# Formal.Core.EnvFast.SteerEnv — does bd_steer need a select hold? (contradiction X6)

Shard A, contradiction X6 of `formal/out/gcd_hw_hypotheses.md`. Notes:
`formal/notes/A-contradictions.md` §X6.

The three shards stated the steer's select obligation differently:

* A (`EnvFast.steer_sound`): "no hold assumption is needed";
* B (`OpsTimed2.SteerStatic.S_S_HOLD`, id `bd_steer.bundled_s_hold`):
  `Wq.hi ≤ Hs + Ws.lo`, i.e. `ρ(2k+1) + Wq.hi ≤ sE + Ws.lo`;
* C (`Net.Ops.Held`): the bus is stable while the channel is mid-transaction,
  i.e. until the step after `ack↓`.

They differ in the ENVIRONMENT, not in the cell. Two sender contracts:

* **H_S_AFTER_ACK** (environment E_A): the sender moves `s` only while
  `req = ack = 0` at its own port, i.e. causally after it has seen `ack↓`.
  This is the library contract (bd_ctl.v: "holds it still from req-rise until
  ack-fall"), A's `steerModel` (guard `!rdy ∧ !req ∧ !ack` on `s`), and C's
  `Held` (the bus may change only across steps that start or end idle).
* **H_S_AFTER_REQ** (environment E_B, weaker): the sender may move `s` once it
  has lowered `req` (guard `!rdy ∧ !req`), without waiting for `ack↓`. This
  is B's `SteerCausal.H_S_HOLD` with a free `Hs` (any hold after the
  sender's `req↓`, including 0).

Results, at two levels.

**Env (state graph, LUT-MIC level, real INITs).** The `req` and `s` forks
into `bd_steer_u` are now separate WIRE elements of unbounded delay (A's
`steerModel` had them isochronic: the LUT read the sender's ports directly).
Two timing assumptions are kept for every model and named: the setup
`sSetup` (prio `(sq, req)`: the select reaches `u.I1` before the sender's
next `req` move, B's `S_S_SETUP`), and `sSettle` (prio `(sq, s)`: the `s`
wire settles before `s` moves again; this only removes runts of the `s` wire
while `req` is low at the pin, where `req·s` masks them, but Env's
persistence check reports every runt).

* `steerA_wire_sound` (E_A): sound with NO hold assumption, for any delay of
  the `req` and `s` wires. The hold is a consequence of causality: `ack↓`
  needs the routed receiver's `ack_k↓`, which needs `req_k↓`, which needs the
  `req` pin's fall at the LUT, so the pin is low before `s` can move.
* `steerB_needs_hold` (E_B, no hold): a reachable transition withdraws an
  excitation of `req1` (a request pulse on the branch NOT named by the token):
  `s` reaches `u.I1` while `req`'s fall is still on its wire.
* `steerB_hold_sound` (E_B + `sHold`, prio `(rq, sq)`: `req`'s fall reaches
  `u.I0` before `s`'s change reaches `u.I1`): sound. That prio is B's
  `S_S_HOLD` in event form.

**Timed (FIFO read-time maps, B's `PipeTimed.Ret`).**

* `hold_free_of_ackfall`: under H_S_AFTER_ACK the pin-level hold (B's
  `H_S_PIN`, hold half) holds for EVERY wire delay: no inequality. The chain
  `req pin↓ ≤ req_k↓ ≤ ack_k↓ ≤ ack↓ at the sender ≤ s moves` uses only
  `fst_ge` (each FIFO channel delivers an edge no earlier than it was
  launched) and the receiver's causality.
* `hold_of_static`: under H_S_AFTER_REQ, B's static `S_S_HOLD` inequality
  gives the pin-level hold.
* `hold_needed_after_req`: under H_S_AFTER_REQ with `Hs = 0` and a `req` wire
  slower than the `s` wire, the pin shows the next token's select while `req`
  is still high at the pin (a concrete pair of fixed-delay wires).

So: A and C assume the same environment (E_A) and need no hold; B's
`bundled_s_hold` is the obligation for E_B, and under E_A B's band form
(`steer_hold_of_ackfall` + `S_S_HOLD`) is a sufficient but lossy check
(it measures from the sender's `req↓` with `Wq.lo` on the way out and
`Wq.hi` on the way in, so it can fail where the event chain holds).
-/

namespace Formal.Core.EnvFast.SteerEnv

open Formal.Core.LutCells Formal.Core.Env

/-! ## 1. Env models with the `req` and `s` forks as wires

Signals: `req 0, s 1, rdy 2, r0 3, r1 4, a0 5, a1 6, ack 7` as in
`EnvFast.steerModel`, plus `rq 8` (`req` at `u.I0`) and `sq 9` (`s` at
`u.I1`). Both LUT outputs read `[sq, rq]` (root first, as `steerModel`'s
`[1, 0]`). -/

def gatesW : List Env.Gate :=
  [.wire 8 0, .wire 9 1, .lut 3 bd_steer_u .O5 [9, 8], .lut 4 bd_steer_u .O6 [9, 8],
   .lut 7 bd_steer_uack .O [6, 5]]

/-- The sender's `rdy`/`req` discipline and four-phase receivers, common to
both environments. -/
def senderRcv : List (Nat × (Nat → Bool)) :=
  [(2, fun s => (!bit s 2 && !bit s 0 && !bit s 7) || (bit s 2 && bit s 0)),
   (0, fun s => (!bit s 0 && bit s 2 && !bit s 7) || (bit s 0 && bit s 7)),
   (5, fun s => bit s 5 != bit s 3),
   (6, fun s => bit s 6 != bit s 4)]

/-- **H_S_AFTER_ACK** (E_A): `s` moves only while `req = ack = 0` at the
sender and before `rdy` (`EnvFast.steerModel`'s guard). -/
def sAfterAck : Nat × (Nat → Bool) := (1, fun s => !bit s 2 && !bit s 0 && !bit s 7)

/-- **H_S_AFTER_REQ** (E_B): `s` may move as soon as the sender has lowered
`req` (and before `rdy`), without waiting for `ack↓`. -/
def sAfterReq : Nat × (Nat → Bool) := (1, fun s => !bit s 2 && !bit s 0)

/-- Named relative-timing assumptions of the wire models. -/
structure SteerAsm where
  /-- `sHold` (B's `S_S_HOLD`, event form): while `req`'s change is on its
  wire, `s`'s change does not reach `u.I1`. -/
  sHold : Bool

/-- `sSetup` (prio `(9, 0)`, B's `S_S_SETUP`) and `sSettle` (prio `(9, 1)`)
are in every model; `sHold` (prio `(8, 9)`) on request. -/
def wModel (sRule : Nat × (Nat → Bool)) (A : SteerAsm) : Model where
  n := 10
  gates := gatesW
  env := sRule :: senderRcv
  prio := [(9, 0), (9, 1)] ++ (if A.sHold then [(8, 9)] else [])
  inits := [0]

/-- `EnvFast.steerQ` (liveness; a receiver acknowledges only the branch `s`
names) and the two branch requests are never high together. -/
def wQ (M : Model) (s : Nat) : Bool := EnvFast.steerQ M s && !(bit s 3 && bit s 4)

def mA : Model := wModel sAfterAck ⟨false⟩
def mB : Model := wModel sAfterReq ⟨false⟩
def mBH : Model := wModel sAfterReq ⟨true⟩

theorem steerA_cert : certify mA (wQ mA) (reachTree mA 1000) = true ∧
    (reachTree mA 1000).size = 46 := by
  decide +kernel

/-- **E_A: no hold assumption, for any `req`/`s` wire delays.** With the
sender bound by H_S_AFTER_ACK, `bd_steer` with separate unbounded `req` and
`s` wires into its LUT6_2 is speed-independent and MIC-hazard-free, live,
never raises both branch requests, and acknowledges only the named branch.
Assumptions: `sSetup`, `sSettle`; NOT `sHold`. 46 states. -/
theorem steerA_wire_sound : Sound mA (wQ mA) := certify_sound steerA_cert.1

theorem steerBH_cert : certify mBH (wQ mBH) (reachTree mBH 1000) = true ∧
    (reachTree mBH 1000).size = 76 := by
  decide +kernel

/-- **E_B with the hold: sound.** H_S_AFTER_REQ plus `sHold` (B's
`S_S_HOLD` in event form). 76 states. -/
theorem steerB_hold_sound : Sound mBH (wQ mBH) := certify_sound steerBH_cert.1

/-- **E_B without the hold: unsound.** Trace: `rdy↑ req↑ rdy↓ rq↑ r0↑ a0↑
ack↑ req↓` (token 0, `s = 0`), then the sender moves `s↑` (allowed by
H_S_AFTER_REQ while `ack` is still high) and `s` reaches `u.I1` (`sq↑`)
before `req↓` does: `req1 = rq·sq` is excited (a request on the branch the
token did not name). Firing `rq↓` then withdraws that excitation: a runt on
`req1`, i.e. `persistOK` fails. -/
theorem steerB_needs_hold :
    ∃ s, Reach mB s ∧ (8, post mB s 8) ∈ succs mB s ∧ (!stepOK mB s 8) = true :=
  witness_sound (M := mB) (s0 := 0) (ts := [2, 0, 2, 8, 3, 5, 7, 0, 1, 9]) (t := 8)
    (bad := fun s t => !stepOK mB s t) (by decide) (by decide +kernel)

/-- …and so E_B without the hold is not `Sound` for any `Q`. -/
theorem steerB_not_sound (Q : Nat → Bool) : ¬ Sound mB Q := by
  intro hS
  obtain ⟨s, hs, hm, hb⟩ := steerB_needs_hold
  have := (hS s hs).2 _ hm
  simp only at this
  simp [this] at hb

/-! ## 2. Timed form: B's FIFO read-time maps

`Ret` (`Cells.PipeTimed.Ret`) is B's FIFO channel: output at `t` shows the
input at `σ t ∈ [t - hi, t - lo]`, `σ` monotone; `fst c` is the first output
instant that shows an input edge launched at `c`. The arcs, as in B's
`SteerRun`: `Wq` (req → `u.I0`), `Ws` (s → `u.I1`), `L` (the routed LUT
output arc), `W` (to the routed receiver), `Wa` (its ack → `uack`), `La`
(`uack`), `Wk` (to the sender). -/

open Formal.Cells.PipeTimed (Ret)

/-- **Hold for free under H_S_AFTER_ACK.** Token `k`: the sender's `req`
rises at `ρr ≥ 1` and falls at `ρf`; `s` holds `v` at its driver on
`[sS, sE)`; setup at the pin (`sS + Ws.hi ≤ qr`, B's `H_S_LEAD`+`S_S_SETUP`
in pin form). The routed receiver lowers its acknowledge at `Af`, after its
request pin has fallen (`hrcv`, H_RCV_CAUSAL); the sender moves `s` only
after it has seen `ack↓` (`hctr`, H_S_AFTER_ACK). Then `u.I1` shows `v` for
the whole interval in which `req` is high at `u.I0` (B's `H_S_PIN`), for
EVERY delay of every channel: no inequality between `Wq` and `Ws`. -/
theorem hold_free_of_ackfall (Wq Ws L W Wa La Wk : Ret) (ρr ρf sS sE Af : Nat) (v : Bool)
    (s su : Nat → Bool)
    (hw : ∀ t, Ws.hi ≤ t → su t = s (Ws.σ t))
    (hs : ∀ t, sS ≤ t → t < sE → s t = v)
    (hρ : 1 ≤ ρr)
    (hsetup : sS + Ws.hi ≤ Wq.fst ρr)
    (hrcv : W.fst (L.fst (Wq.fst ρf)) ≤ Af)
    (hctr : Wk.fst (La.fst (Wa.fst Af)) ≤ sE) :
    ∀ t, Wq.fst ρr ≤ t → t < Wq.fst ρf → su t = v := by
  intro t h1 h2
  have e1 := Ws.ge t; have e2 := Ws.le t
  have c1 := L.fst_ge (Wq.fst ρf); have c2 := W.fst_ge (L.fst (Wq.fst ρf))
  have c3 := Wa.fst_ge Af; have c4 := La.fst_ge (Wa.fst Af); have c5 := Wk.fst_ge (La.fst (Wa.fst Af))
  have hq := Wq.fst_lo hρ
  rw [hw t (by omega)]
  exact hs _ (by omega) (by omega)

/-- **H_S_AFTER_REQ with B's static hold.** If the sender holds `s` until
`sE` with `ρf + Wq.hi ≤ sE + Ws.lo` (B's `S_S_HOLD` with `Hs = sE - ρf`),
the pin-level hold holds. -/
theorem hold_of_static (Wq Ws : Ret) (ρr ρf sS sE : Nat) (v : Bool) (s su : Nat → Bool)
    (hw : ∀ t, Ws.hi ≤ t → su t = s (Ws.σ t))
    (hs : ∀ t, sS ≤ t → t < sE → s t = v)
    (hρ : 1 ≤ ρr) (hE : 1 ≤ sE)
    (hsetup : sS + Ws.hi ≤ Wq.fst ρr)
    (hhold : ρf + Wq.hi ≤ sE + Ws.lo) :
    ∀ t, Wq.fst ρr ≤ t → t < Wq.fst ρf → su t = v := by
  intro t h1 h2
  have e1 := Ws.ge t; have e2 := Ws.le t
  have hq := Wq.fst_le ρf
  have hq0 := Wq.fst_lo hρ
  rw [hw t (by omega)]
  exact hs _ (by omega) (by omega)

/-- The `s` of the counterexample: token `k`'s select `true` until the
sender's `req↓` at 20, then the next token's `false` at once (`Hs = 0`). -/
def cxS (t : Nat) : Bool := decide (t < 20)

/-- **Without H_S_AFTER_ACK the hold is a real obligation.** `req` wire a
fixed 5 steps, `s` wire a fixed 1 step, `req` rises at 1 and falls at 20 at
the sender, and the sender moves `s` at 20 (allowed by H_S_AFTER_REQ with
`Hs = 0`; violates B's `S_S_HOLD`: `20 + 5 > 20 + 1`). Setup holds
(`0 + 1 ≤ 6`). At step 22 `req` is still high at `u.I0` (it falls there at
25) while `u.I1` already shows the next token's select. -/
theorem hold_needed_after_req :
    let Wq := Ret.shift 5
    let Ws := Ret.shift 1
    (0 + Ws.hi ≤ Wq.fst 1) ∧ ¬ (20 + Wq.hi ≤ 20 + Ws.lo) ∧
      Wq.fst 1 ≤ 22 ∧ 22 < Wq.fst 20 ∧ cxS (Ws.σ 22) ≠ cxS 0 := by
  intro Wq Ws
  have a : Wq.fst 1 = 6 := Ret.fst_shift 5 1 (by omega)
  have b : Wq.fst 20 = 25 := Ret.fst_shift 5 20 (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [a]; decide
  · decide
  · rw [a]; decide
  · rw [b]; decide
  · decide

end Formal.Core.EnvFast.SteerEnv
