# B-contracts-trunc (probe G1): time-truncated cell contracts, causal composition

Shard B, Phase 3, for shard C's closed-graph composition. 2026-10-27.
Core Lean, no Mathlib. Gap G1 of `B-contracts.md`.

| file | lines | content |
|---|---|---|
| `formal/lean/Formal/Cells/ContractsTrunc.lean` | 475 | `TokN` (prefix of B's `Tok`) and its toolkit; port halves `ReqUpTo`/`DatUpTo`/`AckUpTo`, `PortUpTo`; limit lemma `port_iff`; base case `PortUpTo.quiet`; `causal_closure`, `causal_closure_cells`, `ports_of_causal`, `net_refines_causal` |
| `formal/lean/Formal/Cells/ContractsTruncSteer.lean` | 498 | `bd_steer` as a causal cell: `steer_fwdN`, `steer_backN`, `steer_pinN`, `steer_skewN`, `steer_step` (B form), `steer_step_ports` (port halves only), `steer_sorder_closed`, `steer_ev_closed` |
| `formal/lean/Formal/Cells/ContractsTruncWit.lean` | 189 | non-vacuity: a unit-delay steer run satisfying every hypothesis of `steer_step_ports` at every `N` |
| `formal/lean/Formal/Cells/ContractsTruncCel.lean` | 189 | the timed C-element in prefix form: `cel_runN`, `cel_nodeN`, `cel_run_of_N` |

All four are CLAIMED and check clean.

## Check

    cd /home/user/asyncfpga3/formal/lean
    for f in ContractsTrunc ContractsTruncSteer ContractsTruncWit ContractsTruncCel; do
      PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/$f.lean \
        -o .lake/build/lib/lean/Formal/Cells/$f.olean; done
    python3 ../scan.py Formal/Cells/ContractsTrunc*.lean

- No output from any of the four (no errors, no warnings), 1-4 s each. Order matters:
  `ContractsTrunc` (imports `ContractsB`) before `ContractsTruncSteer` (imports `ContractsTrunc`)
  before `ContractsTruncWit`; `ContractsTruncCel` imports `ContractsTrunc` only.
- `scan.py`: clean (no `sorry`/`admit`/`axiom`/`native_decide`).
- `#print axioms` (scratch files) on every theorem named below: `[propext, Classical.choice,
  Quot.sound]` or a subset (`port_iff`, `TokN.tok_iff`: none).
- Imports read-only: `ContractsB` (so `Contracts`, `ContractsOps`, `OpsTimed`, `OpsTimed2`,
  `OpsTimedMux`). Nothing shared was edited. The lead must add the four modules to `Formal.lean`.

## The prefix vocabulary (`ContractsTrunc.lean`)

`TokN T N x e g`: B's `Tok T x e g` restricted to instants `t ≤ N` (same three clauses with an
extra `t ≤ N`). `TokN.tok_iff : (∀ N, TokN T N x e g) ↔ Tok T x e g`.

Toolkit, each the prefix form of the whole-run lemma in `OpsTimed`/`OpsTimedMux`:

| lemma | statement |
|---|---|
| `TokN.fifo` | a FIFO arc (`Ret`) turns a prefix up to `N` into a prefix up to `N + lo` (edges moved by `fst`). This is the only source of causal slack: the arc's minimum delay. |
| `TokN.gate` | gated function of a token prefix and a bit bundled up to `N` |
| `TokN.or_tok` | OR of exclusive prefixes; the pin skew (H_OR_SKEW) needed only as "if the later edge happened by `N`, the earlier one precedes it" |
| `TokN.reindex` / `TokN.lift` | to / from a sub-sequence of tokens (`Enum`, `rx`); `lift` needs monotonicity only of edges `≤ N` |
| `TokN.from0` | start a prefix at time 0 from reset quiet; first-edge and monotonicity conditions only for edges `≤ N` |
| `TokN.low_slot/low_range/low_pre`, `TokN.at_phase` (Cel file) | values inside slots |

**Port halves up to `N`** (each is what ONE side drives, so each cell's theorem produces exactly
its own halves):

- `ReqUpTo c ρ α N` (producer): `TokN 0 N c.req ρ true`, `0 < ρ 0`, and
  `ρ (j+1) ≤ N → α j < ρ (j+1)` (next request only after the acknowledge);
- `DatUpTo c ρ α v N` (producer): `t ≤ N`, `ρ(2k) ≤ t < α(2k+1)` ⇒ `c.dat t = v k`;
- `AckUpTo c ρ α N` (consumer): `TokN 0 N c.ack α true` and `α j ≤ N → ρ j < α j`;
- `PortUpTo` = all three. Ordering facts are stated as "if the LATER edge happened by `N`".

| theorem | statement |
|---|---|
| `port_iff` | **limit lemma**: `Port c ρ α v ↔ ∀ N, PortUpTo c ρ α v N` |
| `PortUpTo.down` (and per half) | prefixes are downward closed |
| `PortUpTo.quiet` | base case: both wires low on `[0, N]` and no edge `≤ N` ⇒ `PortUpTo … N` |
| `rho_lt_upTo` | with both halves up to `N`, request edges `≤ N` strictly increase |
| `causal_closure` | generic: `Q` downward closed, true at `N0`, and (all `Q · N`, `N ≥ N0`) ⇒ (all `Q · (N+1)`) ⇒ `Q` everywhere |
| `causal_closure_cells` | the same with a driver map `drv : W → D` and per-driver minimum delay `d ≥ 1` (H_DMIN_POS): (all `Q · N`) ⇒ `Q w (N + d (drv w))` |
| `ports_of_causal` | instantiated on wire halves (`Half C`: `rq`/`dt`/`ak` of each channel): base `PortUpTo … N0` on every channel + per-half causal steps ⇒ every channel is a `Port` |
| `net_refines_causal` | + each operator's `EarlierDet` ⇒ C's `net_refines` conclusion (`ref c k = v c k`). **No port is assumed for the whole run.** |

The driver type `D` is free, so one cell can have different delays for different outputs (the
steer: `dF` forward, `dB` backward).

## The steer as a causal cell (`ContractsTruncSteer.lean`)

Same gate model as `OpsTimed.steer_ok_static` (`SteerGates`, real INITs, FIFO arcs), with every
partner fact up to `N` only:

| theorem | statement |
|---|---|
| `SteerCausalN` (structure) | partners' causality up to `N`: `A j ≤ N → Rsel j + Er ≤ A j`, `ρ(j+1) ≤ N → K j + Es ≤ ρ(j+1)`, `1 ≤ ρ 0` |
| `SteerCausalN.ρpos/Apos/ρ_step/ρ_mono/A_mono` | positivity and monotonicity of the edges `≤ N` |
| `steer_pinN` | H_S_PIN up to `N + dq`, DERIVED from the select held at the sender's driver on the port window `[ρ(2k), K(2k+1))` up to `N`, `S_SETUP0 : Ws.hi ≤ Wq.lo`, `S_HOLD_RT : Wq.hi ≤ Ws.lo + (Wq.lo + Lm + Er + Wm + La.lo + Wk.lo)` |
| `steer_skewN` | H_ACK_SKEW up to `N + Wm`, DERIVED from causality up to `N` and `S_ACK` |
| `steer_fwdN` | sender req prefix to `N`, pin to `N + dq` ⇒ both gated branch requests prefixes to `N + dq + Lm` |
| `steer_backN` | receivers' acks prefixes to `N`, skew to `N + Wm` ⇒ sender ack prefix to `N + Wm + La.lo + Wk.lo` |
| `steer_step` | B form: from the sender's `ReqUpTo`, select window, receivers' gated acks + causality up to `N` ⇒ `AckUpTo cin ρ K (N + dB)` and `ReqUpTo (cout b) (rx R_b κ_b) (rx A κ_b) (N + dF)` |
| `rcv_of_branches` | the branch channels' `AckUpTo` give B's receiver causality up to `N` (`Er = 1`) |
| **`steer_step_ports`** | **the steer's step on port halves only**: inputs `ReqUpTo cin`, `DatUpTo cin` (select = `sel` of the bus), `AckUpTo (cout b)` for both branches, all up to `N`; outputs `AckUpTo cin` up to `N + dB` and `ReqUpTo (cout b)` up to `N + dF` (`dF = dq + Lm`, `dB = Wm + La.lo + Wk.lo`). This is exactly the `step` hypothesis of `ports_of_causal` for the steer's three halves. |
| `steer_sorder_closed`, `steer_ev_closed` | after the closure (whole-run facts), B's `SOrder P Er 1` and C's `SteerEv` (via `ContractsB.steer_ev`) |
| `sel_of_dat` | `DatUpTo` + `H_SEL_WIRE` + `H_SEL_VAL` ⇒ the select window |

`ContractsTruncWit.step_witness`: on a unit-delay run (first request at 9; select held to ack-fall;
receivers one wire later; tokens alternate branches) every hypothesis of `steer_step_ports`
holds at every `N` (statics by `decide`), so the step is not vacuous. `witness_routes` (`decide`):
token 0 reaches only branch 0, token 1 only branch 1, both acknowledged. `OpsTimed.SteerWit` was
NOT reusable: its select changes at `16k+11`, before ack-fall `16k+16`, so it violates the port's
H_BUNDLE window (it only meets `steer_ok_static`'s weaker `H_S_HOLD`).

Named hypotheses of `steer_step_ports` (each a fact about the routed design):
- `hdq : dq ≤ Wq.lo ∧ dq ≤ Ws.lo`, `hLm`, `hWm`: lower bounds on the arcs' minimum delays (SDF).
  Positivity `1 ≤ dq + Lm`, `1 ≤ Wm + La.lo + Wk.lo` is needed only for `causal_closure_cells`
  (H_DMIN_POS), not by the step itself.
- `S_SETUP0 : Ws.hi ≤ Wq.lo`: `bd_steer.bundled_s_setup` with ZERO lead (the port only guarantees
  the bus from `ρ(2k)`). Stronger than `SteerStatic.S_S_SETUP` (which has the sender's lead `Ls`).
  On silicon this needs the `s` wire to be no slower than the req wire's fastest corner: a real
  constraint to check, or the port contract needs a lead (`ρ(2k) - Ls`).
- `S_HOLD_RT`: `bd_steer.bundled_s_hold` with the hold = the round trip to ack-fall.
- `S_ACK`: `bd_steer.ack_or_skew` (still missing from `cell_constraints.json`, see `B-contracts.md`).
- `H_QUIET_FWD`, `H_QUIET_ACK`: steer-driven wires low before `T1 0`, `T2 0` (reset; `ResetGcd`).
- `H_FIRST_REQ : T1 0 ≤ ρ 0 + Wq.lo + Lm`, `H_FIRST_ACK : T2 0 ≤ ρ 0 + Wq.lo + Lm + 1 + Wm + La.lo
  + Wk.lo`: the first request comes late enough after time 0 for the FIFO model to be valid
  (the `Ret` relations hold only from `hi`). GLS: first req edge vs. release.
- `H_SEL_WIRE`, `H_SEL_VAL`: the select at the sender's driver is `sel` of the bus.
- `hcr`, `hca`, `hor`, `hoa`: the channel wires are the steer's traces (see G2 below).

## The C-element (`ContractsTruncCel.lean`)

`cel_runN`: `OpsTimedMux.cel_run` on prefixes. Inputs `TokN T N`, reset low on `[R, N]`, input
latency H_ENV_LATENCY (`hdep`) only for input edges `≤ N`, first edges after `R` if `≤ N` ⇒
excitation `TokN 0 N` on `max (ea j) (eb j)` with gate `ga k && gb k`. `cel_nodeN`: the node up to
`N + L.lo`. `cel_run_of_N`: `cel_runN` at every `N` gives back `cel_run` (consistency). This is the
primitive under the mux, muxn3, merge acknowledge, joins and link controllers.

## Base case and `ResetGcd`

`PortUpTo.quiet` is the base case shape: wires low on `[0, N0]`, no edge `≤ N0`.
`ResetGcd.gcd_release_quiet` / `gcd_reset_release` prove every control net of gcd_hw at its reset
value on `[(maxRank+2)(D+W+1), T]` until a frontier link controller moves; every
request/acknowledge net resets to 0, so with `N0` before the first edge of the run each channel
is `PortUpTo … N0` and each steer's `H_QUIET_*` holds. NOT done: the map from `gNet` node numbers
to the channel wires and steer outputs (the same missing net-name map as in `B-contracts.md`), and
the two models differ (`ResetGcd` is the discrete `Run gNet` model; the timed cells use `Ret`
traces), so the citation is by shape, not a Lean link.

## What did not work / what is not done (precise)

1. **Mux and 3-way mux are NOT restated.** Not attempted beyond the C-element: `mux_ok` /
   `mux_ok_static` (`OpsTimedMux`, `OpsTimed2`) need the `MuxTiming` fields made conditional on
   `N` (`H_DEP_J*`, `H_CTL_SEQ`, `H_OR_SKEW`, `H_DEP_XA/YA`), `mux_E_mono` up to `N`, and the
   derivation of those from `MuxCausal`/`MuxStatic` in prefix form, then the port packaging (with
   G3, the data window). With `cel_runN`, `TokN.lift/reindex/or_tok/fifo` in place, estimate
   0.5-1 day for the mux, about the same for `muxn3_ok` (`MuxN3Timed`), mostly mechanical
   (every derivation already looks only backward). Link/pipe (`LinkTimed`, `PipeTimedN`):
   phase-time `CtlEnv` first needs the `cph → ρ/α` map (G5), then the same.
2. **G4 is not removed.** The edge sequences are fixed functions `Nat → Nat` given up front, and
   `Enum` presupposes infinitely many tokens per branch. A prefix theorem never uses an edge
   after `N`, so the sequences may be the run's actual edges; but their existence for every index
   is liveness, which the closure does not prove.
3. **G2 (observation points) is not resolved.** `steer_step_ports` uses `cin.req = req` (at the
   sender's port, before the steer's own `Wq` wire) and `(cout b).req = r_b` (at the receiver's
   pin, after the steer's `W0`/`W1`). If the receiver's theorem also contains its input wire, a
   wire is counted twice. A convention must be fixed before two cells are composed in Lean.
4. **No closed graph is instantiated.** `ports_of_causal` is generic; the steer supplies its three
   halves' steps. A concrete closed graph needs every other cell's step (item 1) and the sources'
   and sinks' (trivial cells, no B theorem).
5. The steer's branch BUS halves (`DatUpTo (cout b)`) are not the steer's (no data path in
   `bd_steer`; C's H_STEER_DATA); they must come from the data wire's own (FIFO) step.

## Verdict

**Works (for the composition principle and the steer); works with effort for the rest.** The
circularity of G1 is removed in principle: `net_refines_causal` derives every channel's `Port`,
and with each operator's `EarlierDet` C's refinement, from a base state and per-cell causal steps
(prefix of everything up to `N` ⇒ own driven halves up to `N + d`, `d ≥ 1`), with no whole-run
port assumption. The steer's step is proved from B's gate-level model, with its two event-form
obligations (H_S_PIN, H_ACK_SKEW) re-derived up to `N` from partner causality up to `N` and the
static per-arc obligations, and it is non-vacuous. The C-element primitive is restated. Remaining:
mux/muxn3 (~0.5-1 day each), link (~1 day after G5's `cph` map), then G2's convention and one
concrete closed graph.

What it buys: C's composition can now rest on B's timed cell theorems as a DERIVATION (well-founded
induction on time) instead of a consistency check of given ports; each cell's obligation is a
local, GLS-checkable statement about its own output wires in terms of its partners' wires up to
the same instant.

## Fidelity per primitive

- `ContractsTrunc.lean`: no primitive; pure interface (wires abstract traces). `TokN.fifo` is the
  FIFO bounded-delay arc of `PipeTimed.Ret` (H_LUT_FIFO / H_WIRE_FIFO: no glitch, no runt, no
  inertial filtering).
- Steer: unchanged from `OpsTimed`: `u` = real LUT6_2 INIT `0x8888888822222222` (O5/O6 via
  `lutB`, `steer_req0/1`), `uack` = real LUT2 `4'hE` (`or2_spec`), every LUT and wire a FIFO
  bounded-delay arc, no isochronic fork. The select wire `Ws` is a FIFO arc from the sender's
  driver. The data wire beside the steer is not modelled.
- C-element: `OpsTimedMux.CEl` unchanged: a feedback LUT whose excitation is `~rst · C(a, b)`
  (proved from the real INIT per instance by `c2_spec`/`j0_spec`/`j1_spec`), FIFO LUT arc, window
  feedback wire (H_FB, `WinDelay`), `1 ≤ L.lo + wl` (H_LOOP_POS).
- Witness: every arc a unit transport delay (`Ret.shift 1`), not a routed design.
