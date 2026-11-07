# B probe 6d: one timed `bd_link` stage, controller composed in

File: `formal/lean/Formal/Cells/LinkTimed.lean` (core Lean, ~730 lines). It imports
`Formal.Cells.CElemTiming`, `Formal.Cells.Bundling` and `Formal.Cells.LinkHandshake`
(read-only, through their oleans) and adds no shared definitions. Checks clean in
about 4.5 s with no warnings. It contains no `sorry`, `admit`, `axiom` or
`native_decide`.

Check command:

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/LinkTimed.lean

`#print axioms` was run on a scratch copy. Every main theorem (`ctl_phases`,
`enable_train`, `stage_token`, `stage_forward`, `stage_token_clean`,
`capture_win`, `phase_gap`, `timed_order`, `timed_refines`, `token_cycle`,
`causal_of_wire`) uses only a subset of {propext, Classical.choice, Quot.sound}.

## Gap closed

Probes 6a, 6b and 6c each left two gaps:

- They took the latch enable's shape as a hypothesis: `H_EN_CLEAN` in
  `Bundling.capture`, `H_EN_OPEN` in `Latch.holds_value`, and the free times
  `o/c/z` in `LinkHandshake.pipe_data`.
- The timed and interleaving models were not linked.

This file composes the real controller (`bd_c2n` INIT `0x00B200B200B200B2`, via
5b's `Loop`, with its feedback wire), the enable fanout (a separate window
`[elo i, ehi i]` for every latch bit), W latch bits (6c's `LatchRel`) and a timed
four-phase sender and receiver. It then derives the enable shape.

## Model

- **Controller.** `CElemTiming.Loop INIT_c2n req ack rst O qp dlmin dlmax dwmin dwmax`:
  - LUT: `WinDelay [dlmin, dlmax]`.
  - Feedback wire `O -> I2`: `WinDelay [dwmin, dwmax]`.
  - `loop_c2n` reduces it to a `bd_c2` loop on `(req, ¬ack)` using
    `c2n_as_c2`, which is proved from the INIT. 5b's theorems then apply unchanged.
- **Environment.** Event times at the controller pins:
  - `req_in` rises at `ρ k` and falls at `φ k`.
  - `ack_out` (I1 = `c_next`) rises at `α k` and falls at `β k`.
  - The pin traces have exactly this shape (`H_REQ_*`, `H_ACK_*`).
- **Causality.** Each environment event happens only after the party saw the
  node at the new value at some instant from the current phase start on, at
  least `E` earlier (`H_SND_FALL`, `H_RCV_RISE`, `H_SND_RISE`, `H_RCV_FALL`).
  `causal_of_wire` shows where `E` comes from: a party that reads the node
  through a `WinDelay [lo, hi]` wire, reads freshly, and reacts `S` later
  satisfies the hypothesis with `E = lo + S`.
- **Phase starts.** `cph (2k) = max (ρ k) (β (k-1))` and `cph (2k+1) = max (φ k) (α k)`
  are computed from the environment's times, not assumed.
- **Data.** Bit `i`:
  - The sender's net `d i` holds `val k i` on `[dS k, dE k)`.
  - Latch bit `i` is `Bundling.LatchRel (d i) O (q i)` with its own windows. The
    enable net is the node `O` itself, read through bit `i`'s fanout window.
  - The sender's release is causal: `dE k` comes at least `Erel` after the
    sender saw the node low (`H_DATA_REL`). `Erel` includes the DACK chain.

## Theorems (all proved)

1. **`ctl_phases`: the controller follows the environment.** For every phase
   `j`, the node equals `Vph j` (1 on even phases, 0 on odd) on
   `[cph j + dlmax, cph (j+1) + dlmin)`, and the feedback pin equals it on
   `[cph j + Dmax, cph (j+1) + Dmin)`.
   - It is an instance of 5b's `c2_four_phase`. All eight of that theorem's
     hypotheses are DERIVED from the environment model:
     - `ctl_order`, `ctl_both`, `ctl_next` and `ctl_ack` from event times and
       causality;
     - `ctl_norst` and `ctl_reset_done` from a reset pulse of length `Dmax`
       through 5b's `c2_reset`;
     - `Vph_alt` from the definition of `Vph`.
   - The induction over phases (tokens) is the one in `c2_four_phase`.
2. **`phase_gap` and `ctl_gap`.** Consecutive phase starts are at least `Dmax`
   apart, and for `dlmin` after a phase start the node still shows the old
   value. 5b proves this inside `c2_four_phase` but does not export it, so it is
   re-proved here generically by induction. It yields:
   - `obs_late`: no party can see the new value before `cph j + dlmin`;
   - `fall_after`: `cph(2k) + dlmin + E ≤ cph(2k+1)`;
   - `ack_rise_after` and `rel_after`: the release time is at least
     `cph(2k+1) + dlmin + Erel`.
3. **`enable_train`: the enable is a pulse train.** For token `k`, the node is:
   - high on `[cph(2k) + dlmax, cph(2k+1) + dlmin)`;
   - low on `[cph(2k+1) + dlmax, cph(2k+2) + dlmin)`.

   Both intervals are non-empty. Only the transition windows of width
   `dlmax - dlmin` are unconstrained: the window channel is non-FIFO, so glitches
   are allowed there.
4. **`capture_win`.** This generalises `Bundling.capture`: the enable is high on
   `[Ton, Toff1)`, arbitrary (glitches allowed) on `[Toff1, Toff2)` and low on
   `[Toff2, Tnext)`. Setup is measured against `Toff1` and hold against `Toff2`.
   The proof has the same three cases.
5. **`stage_token`: every token is latched.** For every token `k` and every bit
   `i < W`, `q i = val k i` on
   `[max (cph(2k) + dlmax + ehi i, dS k + dhi i), cph(2k+2) + dlmin + elo i)`.
   The enable times `Ton/Toff1/Toff2/Tnext` are DERIVED from `enable_train`, and
   setup and hold follow from the contract inequalities below.
6. **`stage_token_clean`.** With a fixed LUT delay (`dlmin = dlmax`), the derived
   node is exactly 6c's clean pulse, and `Bundling.capture` itself is applied
   with `h_on` and `h_off` derived. This is the literal discharge of `H_EN_CLEAN`.
7. **`stage_forward`.** The output holds `val k i` at least until the receiver's
   acknowledge falls (`β k`), which is the window the library promises
   (`BROAD=1`). Under the output-bundling inequality
   (`dlmax + ehi i ≤ dlmin + E` and `dhi i + Lag ≤ Sdr + dlmin + E`) it also holds
   from the receiver's acknowledge rise `α k` on.
8. **Link to 6b's interleaving model.**
   - `timed_order`: within each token, the node rise follows `req↑` and the
     previous `ack↓`; `req↓` and `ack↑` follow the whole rise window;
     `cph(2k+1) = max(φ k, α k)`; the next `req↑` and `ack↓` follow the whole
     fall window.
   - `token_cycle`: the corresponding word of `LinkHandshake.Step 1` is a run
     from reset back to reset, in either order of `req↓` and `ack↑`. It uses
     the real `ctlB` at every gate step.
   - `timed_refines` combines the two, choosing the order from the timing, and
     gives `Reach 1 reset (2(k+1)) (2(k+1))`.

## The stage's timing contract, in one place

Every row is a field of `CtlEnv` or `DataPath`, or a hypothesis of the
corollary named in the row.

**Notation.**
- `E` is the minimum latency from the node back to the controller's inputs
  through either neighbour.
- `Erel` is the minimum from the node falling to the sender's released data at
  its net (ack wire + DACK + sender).
- `Sdr` and `Lag` are the sender's data lead and lag relative to the request
  at the pin.

**"Rule" column.** H, I and A are rules in `cells/verify/tighten.py`; E is the
rule in `skew.py`.

| # | hypothesis | inequality / statement | physical meaning | rule |
|---|---|---|---|---|
| 1 | `H_CTL.H_LUT` | ctl LUT delay in `[dlmin, dlmax]` | prjxray LUT arc corners | input data. tighten.py uses nextpnr's flat 124 ps; the interval itself is unchecked |
| 2 | `H_CTL.H_FB` | feedback wire `[dwmin, dwmax]` | routed net `c` → I2 | input data (SDF INTERCONNECT); no rule |
| 3 | `H_CTL.H_LOOP_POS` | `0 < dlmin + dwmin` | real loop | trivially true |
| 4 | `H_REQ_*`, `H_ACK_*` | clean four-phase levels at the pins | no glitch on req/ack at the LUT pins | **unchecked.** For an upstream link it holds only outside its transition windows (see gaps) |
| 5 | `H_SND_FALL/RISE`, `H_RCV_RISE/FALL` | events ≥ `E` after a fresh observation of the node | four-phase partners | structural (any library cell); unchecked as a timing number |
| 6 | `H_ENV_POS` | `1 ≤ E` | | trivially true |
| 7 | `H_ENV_LATENCY` | `dlmax + dwmax ≤ dlmin + E` | env latency ≥ feedback wire max + LUT spread (5b) | **unchecked**: no rule compares a C-element's own feedback net with its neighbours' round trip |
| 8 | `H_RST_PULSE/OFF/EARLY` | rst high ≥ `Dmax`, released before the first req | reset sequencing | **unchecked** (testbench/top-level reset) |
| 9 | `H_LATCH` | Kleene mux over pin windows, real INIT | H_KLEENE_LUT (Prelim) | not a timing rule; 6a/MuxTree evidence |
| 10 | `H_WIN`, `H_LATCH_LOOP_POS` | windows well-formed, latch loop ≥ 1 | | trivially true |
| 11 | `H_DATA_VALID` | sender holds `val k` on `[dS k, dE k)` | sender contract | composition: an upstream stage's `stage_forward` |
| 12 | `H_DATA_LEAD` | `dS k + Sdr ≤ ρ k + Lag` | data vs request at the pin | **rule A** for a hand-written sender (request last, `Lag = 0`). For an upstream `bd_link`, `Lag` = its req-leads-data lag, which rule I accounts for. skew.py **rule E** only at steer/mux, not here |
| 13 | `H_DATA_REL` | release ≥ `Erel` after node seen low | sender releases on ack↓ | structural; `Erel` is what DACK pads |
| 14 | `H_PULSE_WIDTH` | `dlmax + ehi i + fhi i ≤ 2·dlmin + E + elo i` | enable high phase at bit `i` > its spread + one latch loop | **unchecked** (6c already noted no rule states the pulse part) |
| 15 | `H_DATA_SETUP` | `dhi i + fhi i + Lag ≤ Sdr + 2·dlmin + E + elo i` | data through D arc + one latch loop before the earliest enable fall at bit `i` | **rule I**. Its closing path (upstream rise → ack → upstream fall → min en arc) is this `E + 2·dlmin + elo`. Rule I is weaker by the I2-pin arc (6c's `counter_rule_I`) and uses min over bits of `elo`, which is conservative. Data entering from outside is "not audited" by I |
| 16 | `H_RULE_H` | `dlmax + ehi i ≤ dlmin + Erel + dlo i` | latest enable fall at bit `i` ≤ earliest next data at its D pin | **rule H**. H is stronger: it omits the D-pin arc and adds a guard, so it is sound |
| 17 | (`stage_forward`) | `dlmax + ehi i ≤ dlmin + E`, `dhi i + Lag ≤ Sdr + dlmin + E` | output valid by the receiver's ack rise | the consumer's own rule (next stage's rule I; B, D or E at an edge-sampling consumer) |

Rows 7, 8 and 14 are checked by no rule today. Row 15's rule (I) misses one arc
term (6c). Row 4 is the composition gap below.

## What did not work / not done

- **Composition into a pipe is not closed.** Under a genuine delay interval,
  `enable_train` lets the node glitch inside windows of width `dlmax - dlmin`.
  A downstream stage reading this node as its `req_in` needs a clean request
  (row 4), so N stages do not compose directly. Two ways to close it:
  - fixed delays (`dlmin = dlmax`), as in `stage_token_clean`, where the node
    is exactly clean;
  - proving FIFO single-transition behaviour (5b lists it as not done); or
    relaxing `CtlEnv`'s shape hypotheses to "clean outside a transition window"
    and re-deriving `H_NEXT`/`H_ACK`, which need care inside those windows.

  Estimate: 1 to 2 days.
- **The interleaving link is at the level of event order** (`timed_order`, plus
  the abstract word is a run). It is not a sampled-state simulation relation for
  arbitrary instants, which would need glitch-freedom.
- **Non-vacuity is not machine-checked.** No concrete trace is shown to satisfy
  all of `CtlEnv` and `DataPath`. A fixed-delay witness with a closed-form node
  trace would take about half a day.
- **Freshness clauses.** The environment's observations are assumed fresh
  (`u ≥ cph j`, the same clause as 5b's `H_ACK`). A sender FSM that starts
  looking only after its own last move needs one more induction to discharge
  this. Not done.
- **Delay lines.** DELAY, DACK and RFAST are not modelled as gates: they are
  folded into `E` and `Erel`. Rule F (FASTFALL flush) is out of scope.
- **Lumped arcs.** The controller is binary with a lumped LUT delay. There are
  no per-pin arcs (5b's caveat).

## Verdict

**Works.** For one `bd_link` stage, the controller's pulse train is derived
from the real INIT, the feedback-wire delay interval and a timed four-phase
environment, so it is no longer assumed. Every token is proved latched and
forwarded, for all `k` and all `W` bits. 6c's `Bundling.capture` is discharged
literally for fixed delays, and generalised (`capture_win`) for intervals. The
stage's whole contract is one list of 17 named items mapped to tighten.py's
rules, and the timed stage is tied to 6b's interleaving model token by token.

- **Effort to finish:** composable N-stage pipe (glitch-window shapes or FIFO),
  1–2 days; non-vacuity witness, 0.5 day; a sampled-state refinement, about
  1 day.
- **What it buys:** a single proved statement of everything a Muller link stage
  needs. It shows that three of the items (`H_ENV_LATENCY`, the pulse-width
  inequality and reset sequencing) are checked by no rule today. It also turns
  rules H and I into consequences of one derivation; I is still short by one arc.

## Fidelity per primitive

- **Controller LUT.** Real INIT `0x00B2…` through `lutB` (binary), with a lumped
  window delay `[dlmin, dlmax]`. It is non-FIFO, so glitches are allowed inside
  transition windows. There is no Kleene/X behaviour and no per-pin arcs.
- **Controller feedback wire.** A routed net with its own window `[dwmin, dwmax]`.
- **Enable fanout.** A separate window `[elo i, ehi i]` per latch bit (wire plus
  I1 arc). The node trace is the enable net.
- **Latch LUTs.** 6c's Kleene closure of the real INITs over per-pin windows
  (H_KLEENE_LUT), with their own feedback window `[flo i, fhi i]`.
- **Sender and receiver.** Abstract timed four-phase partners: event times plus
  causality with latencies `E` and `Erel`. Wires to and from them are folded
  into those latencies; `causal_of_wire` justifies this for a window wire.
- **Delay lines (DELAY/DACK).** Folded into `E` and `Erel`, not modelled as gates.
- **Time.** ℕ ticks.
