# B probe G5b: the link / pipe contract in C's interface

Shard B, Phase 3, gap G5 of `B-contracts.md` (link and pipe). 2026-10-27. Core Lean, no Mathlib.

File (CLAIMED, checks clean): `formal/lean/Formal/Cells/ContractsLink.lean` (766 lines).
Imports (read-only, through their oleans): `Formal.Cells.ContractsB` (and through it `Contracts`,
`ContractsOps`), `Formal.Cells.OpsHold` (and `LinkTimed`), `Formal.Cells.PipePerPin` (and
`PipeTimedN`, `PipeTimed`). No shared definition added or changed. Its own definitions (`ilv`,
`busVal`, `LinkLead`, `PipeIO`, `linkInitEq`, `LinkInitEv`, the witness traces) live in namespace
`Formal.Cells.ContractsLink`. The lead must add `Formal.Cells.ContractsLink` to `Formal.lean`
after `ContractsB`, `OpsHold` and `PipePerPin`.

## Check

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/ContractsLink.lean
    python3 ../scan.py Formal/Cells/ContractsLink.lean

- The check prints nothing (no error, no warning). It takes about 2.5 s.
- `scan.py` is clean.
- `#print axioms` was run on a scratch copy for `link_contract`, `link_opSpec`, `pipe_ports`,
  `pipe_contract`, `pipe_contract_pp`, `fifo_tok`, `linkInit_spec`, `Wit.pipe_witness` and
  `Wit.no_lead_breaks`. All of them use only `[propext, Classical.choice, Quot.sound]`.
  `link_x_lead` uses only `[propext, Quot.sound]`.
- No routed numbers are involved, and no nextpnr build was run.

## Observation points (G2 convention used)

Every channel is observed at its CONSUMER's pins:
- `req` and `dat` are observed at the receiver's request pin and D pins;
- `ack` is observed at the sender's acknowledge pin.

Each cell owns its OUTPUT wires. A link owns:
- `req_out` up to the receiver's request pin (wire + DELAY);
- `data_out` up to the receiver's D pins;
- `ack_in` up to the sender's acknowledge pin (wire + DACK).

With this convention, the pins that LinkTimed's controller reads (I0 = `req_in`, I1 = `ack_out`) are
exactly where the partners' wires are observed. So `CtlEnv`'s `H_REQ_*` and `H_ACK_*` traces ARE the
input port's `req` and the output port's `ack`, and no wire is counted twice. Interleaving on a
channel then splits cleanly:
- the "after its cause" inequalities are derived from the cell that drives the edge;
- the "before the partner's next move" inequalities are the partner's own pin-level causality
  (`H_SND_PIN`, `H_RCV_PIN`). On a composed channel these are the same `Port.ra`/`Port.ar` fields
  that the other end's theorem proves, so nothing is assumed twice.

## Theorems (all proved)

| theorem | statement | hypotheses beyond B's theorem |
|---|---|---|
| `link_in_port` | input channel of a `bd_link` is a `Port`: `req` edges `ilv ρ φ` (CtlEnv's pin trace), `ack` = link-owned `ack_in` at the sender's pin, value `busVal W (val k)` | `H_AIN`, `H_AIN_LATE`, `H_ALO_POS`; sender: `H_SND_PIN`, `H_IN_LEAD`, `H_SND_HOLDF` |
| `link_out_port` | (a) every output bit at the receiver's D pin = `val k i` on `[ρo(2k), β k)`; (b) the output channel is a `Port` (`req` = link-owned `req_out`, `ack` edges `ilv α β` = CtlEnv's I1 trace) | `H_ROUT`, `H_ROUT_LATE`, `H_RLO_POS`, `H_DWIRE`, **`H_LEAD` (H_X_LEAD)**; receiver: `H_RCV_PIN` |
| `link_ev` | C's `LinkEv`: `ρ_in(2k) < ρ_out(2k)` and `v_out k = v_in k` | channel-map identification |
| `link_contract` | the package: both Ports, the bit-level output, `LinkEv` | all of the above |
| `link_opSpec` | `LinkEv` + ports on all channels ⇒ C's `OpSpec … (linkEq ci co)` (`link_spec`) | (G1 caveat) |
| `link_x_lead` | under `LinkLead … M`, the latch bit is valid (`stage_token`'s start) at least `M` before a request edge that is no earlier than `cph(2m) + dlmin + rlo`. With `M = Lx` this is `OpsTimed2.MuxDataEnv.H_X_LEAD` for a link sender, the half `OpsHold.link_x_sender` left open | `LinkLead` |
| `fifo_tok` | a FIFO wire (`Ret`) from a clean node is a clean four-phase `Tok` from time 0 on edges `Wr.fst (τ j)` | quiet before `Q`; wire flushed by the first edge |
| `pipe_ports` | generic N-stage pipe: from `PipeIO` (end facts), FIFO end wires and partner facts: both Ports, bit-level delivery, causality | as listed in the docstring |
| `pipe_io_N`, `pipe_contract` | 6f (`PipeTimedN`, FIFO controllers) gives `PipeIO`; the packaged contract with C's `LinkEv` | `H_LUT_POS`, end wires, **`H_X_LEAD_N : Dl (N-1) b + xhi b ≤ Wr.lo`** (ℤ) |
| `pipe_io_P`, `pipe_contract_pp` | the same for 6g (`PipePerPin`, per-pin LUTs, no `H_LUT_FIFO`) | `H_PIN_POS`, **`H_X_LEAD_P`** on 6g's `Dl` |
| `Wit.pipe_witness` | non-vacuity: for every `N ≥ 1`, 6f's unit-delay witness plus `Wa = shift 1`, `Wr = shift 2` and a one-tick data wire meets EVERY hypothesis of `pipe_contract`, including `H_X_LEAD_N` (tight: `Dl = 1`, `xhi = 1`, `Wr.lo = 2`) and the partners' pin facts. Both Ports and `LinkEv` hold on the concrete run, and the token values are not constant | none |
| `Wit.no_lead_breaks` | **negative control**: in the same run with `Wr = shift 1` (no DELAY, so `H_X_LEAD_N` fails by one tick), the output channel is NOT a `Port` for ANY request/acknowledge traces. At token 0's request edge, the D pin still shows 0 while the token's value is 1 | none |
| `linkInitEq`, `LinkInitEv`, `linkInit_det`, `linkInit_spec` | **proposal for C** (below): the equation of a reset-token link, its event contract, the `EarlierDet` proof, and `OpSpec` on ports | none |

### Named hypotheses added (each a fact about the routed design)

- **`H_ROUT`, `H_AIN`** (single link only): the link-driven wires at the partners' pins are clean
  four-phase traces.
  - LinkTimed's controller is a non-FIFO window LUT, so the node may glitch inside its transition
    windows and this cannot be derived. It is LinkTimed's open row 4.
  - In the pipe models it is derived (`fifo_tok` from `nodes_clean`).
  - GLS test: one edge per phase at the receiver's request pin and the sender's ack pin.
- **`H_ROUT_LATE`, `H_AIN_LATE`**: each edge comes no earlier than `cph j + dlmin +` the wire's
  minimum.
  - `rlo` includes `DELAY`; `alo` includes DACK's fastest path.
  - SDF minima. In the pipe models this is derived (`Ret.fst_lo`).
- **`H_RLO_POS`, `H_ALO_POS`, `H_LUT_POS`, `H_PIN_POS`**: positive minimum delays (prjxray: no
  zero arc).
- **`H_DWIRE`**: each data wire `q i → receiver D pin` is a 5b window wire `[xlo i, xhi i]`
  (non-FIFO allowed; only stable stretches are used).
- **H_X_LEAD (`LinkLead`, `H_X_LEAD_N`, `H_X_LEAD_P`)**: the request path to the consumer's pin must
  be slower than the data path. For one link:
  - `H_X_LEAD_EN : dlmax + ehi i + xhi i ≤ dlmin + rlo` (enable path);
  - `H_X_LEAD_D : dhi i + Lag + xhi i ≤ Sdr + dlmin + rlo` (data-through path).

  For a pipe it is one inequality on the last stage's data lateness, `Dl (N-1) b + xhi b ≤ Wr.lo`.

  This is the obligation B-ops-hold asked for ("req_out leads data_out ... needs a DELAY /
  request-wire obligation"). It is STATED (not derivable from the cell: it is a property of the
  routed request wire and DELAY chain) and PROVED sufficient. `no_lead_breaks` shows it is not
  vacuous: violated by one tick, the port fails.

  In tool terms it is skew.py rule E / tighten.py rule I applied at a link OUTPUT. No current
  rule checks it there:
  - rule I checks the next stage's latch closing, which is a later event;
  - rule E is only applied at steer/mux.
- **`H_WIRE_FLUSH`, `H_QA`/`H_QR`, `H_QUIET_*`**: reset facts.
  - The end wires carry their reset value from power-up and have flushed it by the first node edge.
  - `ResetGcd` proves the control nets settle low; it is not yet tied to these traces (same as the
    steer's `H_QUIET_*`).
- **Partner facts**:
  - `H_SND_PIN`, `H_RCV_PIN`: the partner moves only after it saw the link's edge at its pin.
  - `H_IN_LEAD`: the sender's data at the link's D pins is valid by the request rise at I0. For a
    link sender, this is its own `H_X_LEAD`.
  - `H_SND_HOLDF`: the sender holds until its own ack pin has fallen. For a link sender, this is
    `link_hold_fall`.
  - On a composed link→link channel, all four are conclusions of the other end's `link_contract`.
    The bit-level conclusion `[ρo(2k), β k)` is exactly the downstream's `H_DATA_VALID` window
    with `dS = ρ`, `dE = αi ∘ (2·+1)`, `Sdr = Lag = 0`.

## What did not work / is not done

- **G1 (time truncation) is not addressed.** All statements are whole-run, as in `steer_contract`.
  Probes `ContractsTrunc*` work on that separately; I did not touch them.
- **A single `bd_link`'s output wires are not derived to be clean.** This is LinkTimed's non-FIFO
  controller (row 4). It can be closed by:
  - stating the link via the pipe models with `N = 1` (FIFO or per-pin controller, where
    `pipe_contract`/`pipe_contract_pp` already cover it); or
  - a FIFO single-transition proof for the window LUT (5b, not done).

  With `N = 1`, `pipe_contract_pp` IS a one-link contract with the per-pin LUT model. So for
  composition, the pipe theorems are the ones to use.
- **The rule-H margin is lost at a link→link boundary if only the `Port` is passed on.** The bit
  conclusion ends at `β k` (the `Port` window, C's `Held`). The downstream link's `H_DATA_REL` /
  `H_RULE_H` needs the longer window that `OpsHold.link_hold_fall` gives:
  `β k + dlmin + elo i − 1`, plus the data wire's `xlo`. This is the B-ops-hold finding again: C's
  `Held` is not sufficient for a link consumer. A link→link composition lemma (one `CtlEnv` +
  `DataPath` from the upstream's conclusions) is not written. It is about half a day, and is
  mostly bookkeeping of `Erel`.
- **No witness for the single-link `link_contract`.** LinkTimed itself has none, which is noted
  in B-link-timed. The pipe witness covers `N ≥ 1`, which includes one stage under the FIFO
  model.
- **No per-pin witness.** 6g's `Wit` could be instantiated like 6f's (estimated 1 h).

## Proposal to shard C: a link WITH an initial token (the rig's `uenv1`)

**The cell.**
- `bd_c2n_set` (INIT `64'hFFB2_FFB2_FFB2_FFB2`, `cells/rtl/bd_ce.v`) is `bd_c2n` whose reset half
  (I3 = 1) outputs 1.
- So it comes up with its node HIGH: a token is present at release.
- In the rig, `uenv0` (`bd_c2n`) and `uenv1` (`bd_c2n_set`) form a two-stage pipe whose output
  stage starts full ("the ring starts with one token in it and c0 empty", `gcd_rig.v`).
- C's `linkEq` (`σ co k = σ ci k`) cannot describe it. Output token 0 exists before any input
  token.

**Proposed equation** (`linkInitEq`, defined in the file):

    linkInitEq init ci co σ  :=  σ co 0 = init  ∧  ∀ k, σ co (k+1) = σ ci k

- `init` is the reset token's value.
- For the rig's `uenv1`, which has no data path, it is the unit token (any constant; C's `srcEq`
  convention).
- For a data reset-token buffer, it is the latches' `RESET_VALUE`.

**Proposed event contract** (`LinkInitEv`):
- `v co 0 = init`;
- `ρ ci (2k) < ρ co (2(k+1))`: input token `k` leaves as output token `k+1`, strictly after it
  arrived;
- `v co (k+1) = v ci k`.

`linkInit_det` proves `EarlierDet` for it, so `net_refines_ports` / `net_refines` accept it with
no change. Output token 0 reads no input. Output token `k+1` reads only input token `k`, which is
offered earlier. `linkInit_spec` gives C's `OpSpec`.

**What B still owes for it** (not done, ~1 day):
1. **A set variant of LinkTimed's reset lemma (`ctl_reset_done`).** Under reset the
   `FFB2` half drives the node to 1, so after release the controller sits in a FALL phase.
2. **Re-indexing.** The set stage is LinkTimed with a virtual input token `−1` (`ρ = φ = 0`).
   Its phases are LinkTimed's phases shifted by one:
   - the node's first fall waits for `req_in = 0 ∧ ack_out = 1`, the receiver taking token 0;
   - its `k+1`-th rise latches input token `k`.
3. **The ports.** Output port token 0 is offered at the first request edge after release. Output
   token `k+1` corresponds to LinkTimed's token `k` under the shift. Then
   `link_init_contract` = `link_contract` with `ρo(2(k+1))` in place of `ρo(2k)`.

**For C's ring theorems (C-9).** A ring through `uenv1` has exactly one `linkInitEq` operator.
Every other link uses `linkEq`. The "three storage stages per simple cycle" rule (CLAUDE.md)
counts the set stage as one storage stage holding the token.

## Verdict

**Works.** G5 is closed for the link and the pipe, in `steer_contract` style. B's timed theorems
give `Port` on both channels and C's `LinkEv`, hence `OpSpec … linkEq`:
- `LinkTimed.stage_forward` gives the single link;
- `PipeTimedN.pipe_forward` gives the FIFO-controller pipe;
- `PipePerPin.pipe_forward` gives the per-pin pipe.

The `cph` phase times map to port edges as follows:
- input `req` = `ilv ρ φ`;
- output `ack` = `ilv α β`;
- link-driven edges are bounded below by `cph j + dlmin + wire_lo`, and derived exactly
  (`Ret.fst ∘ τ`) in the pipe models.

**H_X_LEAD** is a named obligation over routed delays (`LinkLead`, `H_X_LEAD_N/P`):
- proved sufficient;
- shown necessary in the witness (`no_lead_breaks`);
- in the mux form, it also discharges `OpsTimed2`'s `H_X_LEAD` for a link sender (`link_x_lead`).

The pipe contract is non-vacuous for every `N ≥ 1` (`Wit.pipe_witness`).

**Remaining effort:**
- G1 time truncation (shared with all operators);
- the link→link `CtlEnv`/`DataPath` composition lemma with the rule-H window (~0.5 day);
- the set-link timed theorem for `uenv1` (~1 day);
- a 6g witness (~1 h).

**What it buys:**
- C can compose links and pipes from B's gate-level timed models with one per-channel interface.
- H_X_LEAD now has a precise inequality that tighten.py/skew.py could check at every link output:
  `Wr.lo ≥ Dl(N-1) + xhi`, i.e. request path minimum ≥ the data's lateness behind the last
  stage's rise plus the data wire maximum. No rule checks it today.

## Fidelity per primitive

- **`bd_link` controller (LinkTimed)**:
  - real `bd_c2n` INIT `0x00B2…` via `lutB`, binary pins;
  - lumped non-FIFO window delay `[dlmin, dlmax]`, so glitches are allowed in the transition
    windows;
  - feedback wire `[dwmin, dwmax]`.
- **Pipe controllers**: unchanged from the source theorems.
  - 6f: real INIT, FIFO LUT map (`H_LUT_FIFO`).
  - 6g: per-pin site-pin FIFO maps plus one FIFO tree map (`H_PIN_FIFO`/`H_TREE_FIFO`), no
    `H_LUT_FIFO`.
  - In both, the DACK line is the gate-level FASTRISE OR (`fastrise_or`).
- **Latch bits**: 6c's Kleene closure of the real INITs over per-pin windows (H_KLEENE_LUT). The
  witness uses the real `ODD` INIT as a transport LUT.
- **End wires (new here)**:
  - pipe: `ack_in` and `req_out` to the partners' pins are FIFO read-time maps (`Ret`), the same
    assumption as 6f's internal lines;
  - single link: abstract clean traces with a lower edge bound;
  - data wires: 5b window wires (non-FIFO allowed).
- **Bus value**: `busVal` (binary weighting). Only its congruence on the `W` bits is used. C sees
  the token as a `Nat`.
- **Partners**: abstract pin-level causality and data windows.
- **Delay lines**: DELAY is folded into `rlo`/`Wr`, DACK into `alo`/`Wa`. In the 6f/6g pipes,
  internal DACK is gate-level.
- **Time**: ℕ ticks; `Dl` in ℤ. The witness uses unit delays, which is a consistency check, not
  timing evidence.
