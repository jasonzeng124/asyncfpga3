# A-events2: the counter domain for open pipes, n-input C-elements, delay chains and general period bounds (shard A)

## Verdict

**Works.** All four extensions are proved, each with a negative control. They are proved in one
generalised domain (`Events2`), which also re-proves A-events' ring3 results (`Events2Ring3`).

| item | what is proved | negative control |
|---|---|---|
| **E2** open nets | `Beh.safe` under `Back`. `Pipe3.pipe3_safe`: every behaviour of the parsed `designs/pipe3.json` with ANY handshaking environment (response band `[elo, ehi]`, `1 ≤ elo`, `ehi ≤ 10^9` steps) has the three controller outputs equal to `ph false (M t j)` at every time | `slowfb_neg` (Back fails, by decide); simulation with feedback [130,150]: 50/50 runs break the counter model; open-loop sender faster than the pipe: 20/20 runs break it |
| **E4** n-input C-elements | `cel_ph` (n-input counter lemma); `InitOK` is decided on the real INITs of `bd_c2`, `bd_c2_set`, `bd_c2n`, `bd_c2n_set`, `bd_c3`, `bd_c4` (`cells_ok`, taken from `LutCells`, with their pin lists `cells_pins`); `lut_transport2` turns any LUT6 whose INIT passes into the abstract stage | `cells_neg`: four wrong (INIT, arity/bubble/reset) pairings are rejected by decide |
| **E1** chains on pins | `chain_warp`: any chain of buffer/inverter 1-input gates is ONE transport channel, with summed band and inverter parity. Used for pipe3's `r[i]` lines (route→LUT1→route, [81,101] steps) and for the environment | `inv_neg` (wrong parity rejected); `chain_neg` (a chain through the latch LUT is not a chain) |
| **E3** period bounds | `cycle_le`/`cycle_le_iter` (per-window upper bound from any closed walk); `rate_upper` and `rate_lower` (long-run rates from potential certificates, checked by decide); `LoCert.cycle`: a lower certificate exists only if `T/K ≥` the max cycle ratio, so the certificate method is exact | `lo_tight` (pipe3 and ring3): no certificate with `T < 171·K` exists; simulation reaches the per-window bound (minimum gap 135 steps observed = 135 proved) |

**Precision against XSim on pipe3.** I evaluated the domain's proved one-step inequalities on
pipe3's open-loop stimulus (`windows.py`, untrusted arithmetic).
- All **12** controller event windows are **identical** to XSim's X windows. Example: c2's first
  rise is [5250, 5850] ps in both.
- On this finite, acyclic stimulus XSim is already exact, and so is the counter domain.
- **The gains are not tighter windows:**
  - the result holds for all time instead of up to a 24 ns horizon;
  - it holds for every environment schedule that handshakes, not for one stimulus;
  - it closes the loops that XSim cannot.
- `windows.py` also checks the stimulus against the environment half of `Back`: every sender
  and receiver edge waits for its partner's latest possible event plus `hiQ − loG`. The answer
  is yes. This is evidence only; turning it into a theorem is W1 in `Wip/Events2.lean`.

## Files

| file | status |
|---|---|
| `formal/lean/Formal/Core/XAudit/Events2.lean` | proved. `fmin`, `cel`, **`cel_ph`**, `CNet` (arity, bubbles, inverting channels), `Bands`, walks (`walkOK`, `wTok`, `wLo`, `wHi`), **`Back`** (decidable), `Beh`, `M`, `M_mono`, `walk_le`, `pin_le_q`, **`Beh.safe`** |
| `formal/lean/Formal/Core/XAudit/Events2Time.lean` | proved. `cycle_le`, `cycle_le_iter`, `UpCert`/**`rate_upper`**, `ge_pins`, `LoCert`/**`rate_lower`**, `LoCert.walk`, **`LoCert.cycle`** |
| `formal/lean/Formal/Core/XAudit/Events2Design.lean` | proved. `testBit_addr`, `spec`, **`InitOK`**, `layout`, **`cells_ok`**, `cells_pins`, **`cells_neg`**, `chainOK`, **`chain_warp`**, `SMap2`, **`Recog2`**, `lut_transport2`, **`design_beh2`**, **`design_safe2`** |
| `formal/lean/Formal/Core/XAudit/Events2Pipe3.lean` | proved. The `--emit-lean` literal of `designs/pipe3.json` (slow corner); environment gates `envS`/`envR`; `recog`, `backOK`, `recog50`, `backOK50`; **`pipe3_safe`**, **`pipe3_rates`**; controls `slowfb_neg`, `inv_neg`, `chain_neg`, `lo_tight` |
| `formal/lean/Formal/Core/XAudit/Events2Ring3.lean` | proved. A-events' parsed ring3 through `Recog2`/`Back`; **`ring3_rates`**, `lo_tight` |
| `formal/lean/Wip/Events2.lean` | open shapes (`sorry`, not built): W1 open-loop window certificates, W2 per-window lower bound, E5, E6 |
| `formal/tools-A/xaudit/events2/cert.py` | untrusted certificate finder (cycle ratios, potentials) |
| `formal/tools-A/xaudit/events2/{ring3,pipe3_env50}.net.json` | its inputs |
| `formal/tools-A/xaudit/events2/pipe3_sim.py`, `pipe3_sim.txt` | random concrete transport simulation of pipe3 + environment, checked against the proved statements |
| `formal/tools-A/xaudit/events2/windows.py`, `pipe3_windows.txt` | counter-domain windows on the open-loop stimulus vs XSim |

### Check

From `formal/lean`:

    ../check.sh Formal/Core/XAudit/Events2.lean Formal/Core/XAudit/Events2Time.lean \
      Formal/Core/XAudit/Events2Design.lean Formal/Core/XAudit/Events2Pipe3.lean \
      Formal/Core/XAudit/Events2Ring3.lean
    # -> [audit] 1095 declarations checked, [check] OK   (about 25 s)

- There is no sorry, admit, axiom, native_decide or bv_decide.
- The only axioms are `propext`, `Classical.choice` and `Quot.sound`. `Classical.choice` comes
  from `Classical.choose`, which picks each gate's warp in `design_beh2`.
- Every instance fact is checked with `decide +kernel`. That covers the INITs over 64
  addresses, `Recog2` on the 42-gate pipe3 design, `Back`, and the certificates.
- No existing file was edited. There is no new executable: `EventsMain` is unchanged and no
  lakefile stanza is needed. See "What it does not do".

Tools (no Lean needed):

    cd formal/tools-A/xaudit/events2
    python3 -I cert.py pipe3_env50.net.json
    python3 -I windows.py
    python3 -I pipe3_sim.py 50
    python3 -I pipe3_sim.py 50 --fb 130 150
    python3 -I pipe3_sim.py 20 --openloop 60

## What changed from A-events, and why it is still one proof

### 1. A stage is an n-input C-element (`CNet`, `cel`)

- **Pins and polarities.** A stage has `ar j ≥ 1` pins. Each pin has two polarities:
  - a LUT bubble `neg`;
  - an inverting channel `inv` (an environment sender, or an odd chain).
- **The settled function** `cel` is "all inputs 1 ⇒ 1, all 0 ⇒ 0, else hold q".
- **`cel_ph`** replaces `maj_ph`. If the fed-back count `mq` satisfies `mq ≤ p_i ≤ mq+1` for
  every input phase `p_i`, then the output phase is `min_i p_i`. The proof has two cases: some
  input equals `mq`, which gives hold or follow at the old phase, or all inputs are `mq+1`.

### 2. A pin is ONE channel, whatever it is physically

- A routed arc, a `bd_delay` chain (E1) and the environment (E2) are each one monotone warp in
  a band.
- `chain_warp` composes chains at the netlist level.

### 3. `Back` replaces `Pairing ∧ Race`

Pin `p` of `j` needs a walk of pins from `src j p` back upstream to `j` that satisfies two
conditions:
- **tokens:** `tokens(walk) + off(j,p) ≤ 1`;
- **timing:** `hiQ j ≤ loG j p + Σ_walk (loF + loG)`.

Then `walk_le` gives `P j p s ≤ M (Q j s) j + 1`, and `safe` goes through unchanged. Two
special cases:
- A one-arc walk is exactly `Pairing ∧ Race`. `Events2Ring3.backOK` checks this on ring3.
- The environment's self-loop is the **empty** walk. The pin reads the stage's own output
  through the environment, inverted, so it has one token, and the race is
  `hiQ ≤ loG(env + route)`.

### 4. An open pipe is closed by its environment

- **The sender** is `req_in = ¬ack_in` delayed by `[elo, ehi]`: an eager producer that answers
  each acknowledge.
- **The receiver** is `ack_out = req_out` delayed: an eager consumer.
- At the netlist level these are two extra 1-input gates. They are stated as **hypotheses** on
  the input ports' waveforms (`pipe3_safe`'s `hsnd`/`hrcv`): `Transport elo ehi`, a monotone
  warp. Safety only uses `elo ≥ 1` and monotonicity.
- **What the hypothesis means.** The environment toggles a port only after the partner stage's
  matching event, and never skips ahead by more than that.
  - An environment that waits arbitrarily long is covered up to `ehi = 10^9` steps (10 ms).
  - A slower one only needs a bigger literal.
- **An open-loop stimulus is not a channel.** `windows.py` shows the shipped stimulus satisfies
  the corresponding inequality in every behaviour. Making that a theorem is W1.

## Results

### pipe3 (slow-corner ILLUSTRATIVE bands: LUT [9,13], route [36,44], feedback [27,33] steps of 10 ps)

**Safety (`pipe3_safe`).**
- It is proved for every behaviour, all time, with any environment band in [1, 10^9] steps.
- **Back margins.** The internal pins (0,1), (1,0), (1,1) and (2,0) close through a neighbour:
  - fastest round trip 126 steps against own feedback of at most 33;
  - margin 930 ps.
- **The two environment pins have a thin margin: 30 ps + the environment's minimum response
  time.** The margin is `loG(route) + elo − hiQ` = 360 ps + elo − 330 ps.
  - **Finding.** At an open boundary, the C-element race is protected only by the input port's
    route against the own-feedback route, plus whatever the environment adds.
  - **Impact.** A clocked rig answers in at least a clock cycle, so it is fine. A fast async
    neighbour (one LUT plus a short route) is not obviously fine.
  - **Recommendation.** This inequality should be a bdc/route gate on real per-arc bands, like
    `Race` (A-xaudit item 3).

**Rates (`pipe3_rates`, environment answering within [1,50] steps).** For every behaviour:
- **Per-window upper bound:** c0 fires at most once in every window of 135 steps. This is the
  critical cycle stage0 → stage1 → stage0: ack pin plus request line, one token,
  lo = 45 + 90 = 135.
- **Long-run upper rate:** `135·M ≤ t + ρ_j + 135`.
- **Long-run lower rate:** `t ≤ 171·M + π_j + (T + 158)`, i.e. at least one event per 171
  steps.
- **Handshake cycle:** 2.7 .. 3.42 ns per four-phase handshake.
- **Tightness:** `lo_tight` shows no certificate below 171·K exists.

**Simulation (`pipe3_sim.txt`).** This is evidence only.

| run | result |
|---|---|
| eager environment, correct bands, 50 runs | **0** runs with `c ≠ ph(M)`; 0 rate violations; min c0 gap **135** steps (the proved bound is attained); mean spacing 139..142 steps |
| feedback [130,150] | **50/50** runs break the counter model: glitches, min gap 1 step, spacing about 4 steps (self-oscillation) |
| open-loop sender, half-period 20, 60, 120 steps | **20/20** break the model each. At 60 the environment runs ahead and tokens are silently lost; at 20 and 120 there are glitches |
| open-loop sender, half-period 200, 300 steps | **0/20** break it. These are slower than the pipe's 171-step worst case, so they obey the handshake |

### ring3 through Events2 (`ring3_rates`)

- **Safety:** the same theorem as A-events' `ring3_design`, now from the general domain.
- **Per window:** at most one event per 135 steps per node, from the b-pin cycle (one token,
  3 hops).
- **Long run:** at least one event per 171 steps, from certificate π = (57, 0, 114).
- **Agreement with A-events:** this equals `EventsRing.node_period` ([3d, 3D] = [135, 171]).
  That theorem needed a ring-specific invariant; here the bound comes from a 3-number
  certificate.

## Fidelity

These items are in addition to A-events' fidelity table, which still applies.

| item | model | status | test |
|---|---|---|---|
| n-input C-element | real INIT bits of `bd_c3`/`bd_c4` (and the c2 family) on the `bd_ce.v` pin layout, all 64 addresses with unused pins 0 (`InitOK`, decided) | exact (UG474 LUT semantics) | GLS with the unisim LUT6 |
| delay chains | each 1-input gate (`bd_delay` LUT1, route arc) is a transport channel; a chain is their composition | the same FIFO (monotone-warp) hypothesis as every other arc. An inertial LUT1 that swallows a short pulse is **not** a warp. In the proved designs no pulse is shorter than a hop | GLS at both corners; board TDC on a `bd_delay` line |
| environment | an eager handshake partner: transport channel from its partner stage, band `[elo, ehi]` | **hypothesis** (`hsnd`, `hrcv`). The simulation shows the theorem's conclusion fails when the environment does not handshake | rig: the clocked FSM that drives req/ack must change a port only after it has *sampled* the partner's edge (through a synchronizer), which makes `elo` ≥ a clock cycle |
| env-pin race | `hiQ ≤ elo + loG(port route)` | checked inequality, thin margin (30 ps + `elo` on these bands) | per-arc prjxray bands; GLS with a fast environment model |
| period bounds | max cycle ratio of the counter graph with per-arc [lo, hi] | proved for every behaviour **of the model**. The numbers are as good as the bands, which are illustrative here | board ring/pipe period measurements against `cert.py` on per-corner bands |

## What it does not do

| item | what | estimate |
|---|---|---|
| executable `xevents2` | Recognising open nets automatically (chains, n-input INITs via `InitOK`, environment from a command-line spec), searching `back` walks and running `cert.py`'s search in Lean. Everything it would check is already decidable here (`Recog2`, `Back`, `UpCert`, `LoCert`). I did not write it: `EventsMain` defines `main`, so the parser would have to be copied a second time. **Lead:** factor the parser out of `Main`/`EventsMain` first, then it is about 0.5 day. No lakefile change today | 0.5 day after the refactor |
| W1 | open-loop stimulus as a theorem: the environment as a count-carrying source plus window certificates (`windows.py` in Lean, checked by decide) | 0.5 day |
| W2 | per-window LOWER bound. It is only long-run today; the potential gives an additive constant | 0.5 day |
| E5 | choice (mux/steer/merge/arbiter) | research, 3-5 days |
| E6 | bundling (data before latch enable) inside loops | 2-3 days |
| inertial delays | a pulse-swallowing LUT is not a warp | needs a different channel lemma |

## Effort and what it buys

**Effort.** The work took about 3 h. Bringing bdc's control skeleton without choice into the
domain is now mostly recognition:
- forks and joins are `bd_c3`/`bd_c4` or multi-pin stages;
- delay lines are chains;
- environments are channels.

All of these fit `Recog2`. What remains is the tool (0.5 day after the parser refactor), W1,
and then E6.

**What it buys:**
- **The first sound, all-time, all-environment hazard proof for an open bundled-data pipeline
  netlist (pipe3).** It has the same window precision as XSim where XSim applies.
- **Exact cycle-time bounds for any marked-graph control net.** They come from a 3-number
  certificate that the kernel checks, and `LoCert.cycle` shows the certificate cannot be
  beaten.
- **A concrete new obligation for bdc/route.** The open-boundary C-element race,
  `hiQ ≤ elo + loG(port route)`, is the thin-margin item.
