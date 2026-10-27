# C-12b: async-circuit and timed-automata tools (Workcraft, UPPAAL, ...)

Files (all mine): `formal/tools/async/tamodel.py`, `celem.py`, `arb.py`,
`meta_dtmc.py`, and this note. No Lean in this probe.

## Verdict

**Works with about 1 day of effort, but not with the tools the probe names.**

- **Blocked:** Workcraft, UPPAAL, TChecker and the PRISM binary (details below).
- **What works instead:** Storm 2.0.0, a probabilistic model checker that
  reads the PRISM language. It installs from PyPI in 38 s.
- **Front end:** on top of Storm I wrote a ~330-line Python front end,
  `tamodel.py`. It builds gate-level networks of timed automata (TA) from the
  real INIT constants and checks them under digital-clock semantics.
- **What it found:** C-element and arbiter checks take 0.02-30 s each. The
  front end found the exact delay bound where each property breaks, reproduced
  the header's 16 ps finding exactly, and found two timing conditions on the
  shipped `bd_arbiter` that its header presents as structural.
- **Probabilistic layer:** a Storm DTMC of the linearised loop reproduces the
  e^(-t/tau) resolution law over 2-3 decades. Only noise makes the far tail
  decay; with no noise, the saddle state never resolves.

## What installed and what was blocked (2026-10-27, through the agent proxy)

| tool | route tried | result |
|---|---|---|
| Workcraft | `gh release` / api.github.com | 403: "GitHub access to this repository is not enabled for this session" (REST) and GraphQL disabled |
| Workcraft | https://workcraft.org | CONNECT 403 (policy denial) |
| Workcraft | github.com/.../archive, codeload.github.com | HTTP 403 |
| Workcraft / TChecker / PRISM source | `git clone` (add_repo says anonymous git reads are served) | **not attempted: the shard-C brief forbids running any git command.** This is the most likely way to get TChecker (C++/CMake; boost, bison and flex are available from apt). Workcraft's backends (Petrify, MPSat, punf) are binaries from workcraft.org, which is blocked, so Workcraft would still be blocked even if cloned |
| TChecker | GitHub MCP `get_file_contents` | "repository not configured for this session" |
| UPPAAL | uppaal.org, download.uppaal.org | CONNECT 403 |
| PRISM | prismmodelchecker.org | CONNECT 403 |
| PRISM, Oxford mirror | www.cs.ox.ac.uk | CONNECT 403 |
| sourceforge | sourceforge.net | 403 |
| apt (Ubuntu 24.04 archive: reachable) | uppaal, tchecker, petrify, prism, nusmv, mcrl2, storm, ltsmin | none packaged. spin 6.5.2, cbmc 5.95 and z3 4.8.12 are available (untimed; not used) |
| PyPI (reachable) | `petrify`, `workcraft`, `pyprism` | **name squats or unrelated packages** (a CAD library, a worker queue, polymer physics). Not the tools |
| PyPI | **stormpy 2.0.0** (manylinux_2_34 wheel, cp311) | **installed in 38 s**; Storm's engine is inside the wheel |
| raw.githubusercontent.com | reachable | single files only, no tree listing, so no source checkout |

Venv: `$S/venv`, where `S=/tmp/claude-0/-home-user-asyncfpga3/1e7618db-96c2-5b39-8e46-9778d8fa891b/scratchpad`
(made with `python3 -m venv venv && venv/bin/pip install stormpy==2.0.0`).

## Model (`tamodel.py`)

**Timed automata.** Each node is one timed automaton.
- The node has a Boolean output x and a next-value function f(state). A LUT
  node uses the **real INIT and pin map**, Shannon-expanded over the pins. No
  hand-written Boolean equation is used. For the 6-input C-element, the
  expansion comes out as `rst ? 0 : maj(a,b,qp)`.
- Each node has its own rise and fall delay interval [lo,hi].
- There are two delay channels:
  - **inertial.** One clock runs while the node is excited, and resets when the
    excitation changes. The node fires within [lo,hi]. An excitation that is
    withdrawn before the node fires is swallowed.
  - **transport** (FIFO pure delay). A queue of K=3 in-flight edges, each with
    its own clock. A zero-width reversal is cancelled. When the next edge is
    already due, it annihilates with the head, so a pulse shrinks by the
    rise/fall asymmetry, as in B-arb-handover's `LutOut3`, and no zero-width
    output pulses appear.
  - Monitors: `ovf_x` flags queue overflow, i.e. where the model stops being
    exact. `mlt_x` flags that a second edge was queued behind an undelivered
    one, i.e. a runt at x's input.

**Time.** Integer ticks under digital-clock semantics: one global `tick` that
cannot pass a deadline. For closed TA with integer bounds, digital clocks
preserve reachability (Henzinger-Manna-Pnueli 1992). For the inertial model the
checks are therefore exact for integer bounds. For the transport model they are
exact only where `ovf` is unreachable.

**Encoding.** The network is emitted as one PRISM `mdp` module. Scheduler
nondeterminism stands for every delay choice and every interleaving, and
`Pmax=? [F bad]` is 0 or 1 (a qualitative answer). `witness()` reads a
violating run off Storm's scheduler and prints it as a waveform.

**Ties.** When two edges are due at the same instant, either order is
explored. This makes boundary cases fail at equality: "safe iff E >= X+1"
means the dense-time bound is E > X.

## C-element (`celem.py`, bd_c2, INIT 64'h00E8_00E8_00E8_00E8)

Nodes:
- `rst`: one-shot release in [0,2].
- `O`: the LUT pin, [dl_lo, dl_hi].
- `qp`: the feedback route at I2, [dw_lo, dw_hi].
- `a`, `b`: the environment. Each input toggles [e_lo, e_hi] after it sees O
  catch up with it. This is the speed-independent four-phase environment, and
  the two inputs are independently skewed.

Checks:
- spec: O moves only when a = b != O.
- haz: excitation withdrawn without firing (inertial only).
- live: Pmin of O eventually rising (deadlock check).

Run: `cd formal/tools/async && $S/venv/bin/python -I celem.py`. That is 144
checks, both channels, 8-32 s in total (0.02-0.2 s each, 16-17k states at
most). Log: `$S/celem.log`.

**Result (exact, both channels, every dl spread tried):** the spec holds iff
**e_lo >= dw_hi**, the environment's minimum response vs the feedback route's
maximum delay. It does **not** depend on the LUT's own delay or its spread.
- Rows: (dl=(1,1)|(1,3)) x (dw=(1,1)|(1,3)|(2,4)) x e_lo 0..5.
- For e_lo below the bound, Storm finds the C-element hazard. O rises, one
  input drops before qp has arrived, and maj(0,1,qp=0) pulls O back down.
- Inertial: hazard-free iff e_lo >= dw_hi+1. At e_lo = dw_hi the only extra
  event is a zero-duration excitation at the tie, which the inertial LUT
  swallows.
- Liveness Pmin = 1 everywhere.
- Transport: `ovf` is reachable only in rows that already fail (oscillation).

**Comparison with B (CElemTiming.lean):**
- B proves `c2_four_phase` under H_ENV_LATENCY `Dmax <= dlmin + E`, i.e.
  E >= dw_hi + (dl_hi - dl_lo). That is for the non-FIFO `WinDelay` channel.
- In FIFO channels (inertial or transport), the tight bound is the weaker
  E >= dw_hi. B's extra (dl_hi - dl_lo) is the price of the non-FIFO channel,
  or slack.
- Worth a Lean follow-up: either a WinDelay counterexample at E = dw_hi, or a
  FIFO version of the theorem.

**Comparison with C-12a (smt/celem.py):** 12a uses a different environment
(hold for W after the ideal z changes). It gets W >= Dmax, tight for WinDelay.
The two environments are not the same hypothesis, so the numbers are not
directly comparable.

## Arbiter (`arb.py`, bd_arbiter as shipped vs the UNHELD node)

**Nodes.**
- `q`/`R0`: ustate O6/O5. Either INIT 64'hFFF0_FFB2_ACAC_ACAC (held), or the
  unheld variant with O6 = FFB2_FFB2 (bd_c2n_set's function, A0 ignored).
- `g1`/`g2`: ugrant O5/O6, INIT 64'h0C0C_0C0C_A0A0_A0A0.
- `A1`/`A2`: bd_c2 (I2 = own output).
- Wires: `qs` (q->ustate.I2), `qg` (q->ugrant.I2), `A0s` (A0->ustate.I4).
- Environment: the server `A0` follows R0 after [s_lo, s_hi]. The clients
  raise r freely and drop it [1,6] ticks after their A rises. Reset is
  released in [0,2].

**Arcs.** 1 tick = 4 ps, taken from the header's zero-routing trace: O6 rise
56 / fall 124, O5 rise 52 / fall 28 ps (14/31/13/7 ticks).

**Monitors.**
- mutex: g1 & g2.
- amutex: A1 & A2.
- ho: a grant rises while A0 is still high from an already-acknowledged
  transaction.
- tx: a client acknowledged with no A0 rise since the previous acknowledge
  (the "80 completions vs 40 transactions" count).
- reach1/2: non-vacuity, = 1 in every row.

**Run.**
- `$S/venv/bin/python -I arb.py inertial` takes 27 s for 48 checks.
- `arb.py transport` takes 2-30 s per check, with up to 1.3 M states.
  - The first full transport run was **OOM-killed** by the sandbox memory
    cgroup at 5.3 GB RSS, in section 4 (unheld, transport, arc spread ±2).
  - A HELD transport+spread row was still building after 20 min at 5.2 GB.
    I killed it, so as not to take shared memory from shard Lean jobs (the
    same cgroup has OOM-killed `lean` twice today).
  - Transport mode now skips section 4.
- Logs: `$S/arb_in.log`, `$S/arb_tp.log` (sections 1-3), `$S/arb_tp2.log`.

**Effort figures.** About 2.5 h of work: about 40 min on tool hunting and the
proxy, about 1 h writing the front end (with 5 stormpy API fixes, since the
2.0 API differs from the docs), and the rest on sweeps, witnesses and notes.

### Inertial channel (exact for integer bounds)

1. **UNHELD, the header's 16 ps claim, reproduced exactly.** With zero routing
   the grants overlap. Exclusion holds iff the q->ugrant route is >= 5 ticks
   (20 ps): it is violated at 16 ps (tie) and holds at 20 ps. The rising grant
   path is 56+52 = 108 ps against the 124 ps falling grant. This agrees with
   B-arb-handover's proved 16 ps threshold.
2. **UNHELD protocol violation (ho, tx), reproduced.** It appears iff the
   server is slow enough that A0 is still high when q flips: srv_lo >= 20
   ticks (80 ps). With a faster server, R0's 28 ps fall reaches the server
   first.
   - Here R0 does fall. The header's simulation says R0 "never returned to
     zero". With an inertial or transport O5 arc of 28 ps against the 124 ps
     q flip, it cannot bridge.
   - The header's 80/40 count needs the slow server, which tb_arb has.
3. **HELD (as shipped).**
   - mutex, ho and tx hold in every inertial row with A0-fork skew <= 28 ticks.
     That includes arc spread ±2 ticks with q routes in [0,8] and A0 fork in
     [0,4] (13 k states, 0.6 s).
   - **Ack overlap A1 & A2 is reachable when the server is fast: srv_lo <= 14
     ticks (56 ps); it holds at >= 15 (60 ps).** Mechanism (witness at
     srv=[14,19]):
     1. r2 falls and R0 falls 28 ps later.
     2. The server drops A0, which unfreezes q.
     3. q flips for the waiting r1 (56), g1 and R0 rise (52), A0 rises (56)
        and A1 rises.
     4. All of this happens while ua2 = C(g2, A0) is still inside its 124 ps
        fall arc. g2 itself fell late, by O6's 124 ps fall arc.
   - That is a relative-timing condition, "server round trip > A-element fall
     completion". B-arb-handover reaches the same class from the untimed side.
     The tool gives the number for these arcs: the server's minimum latency
     must exceed about 56 ps. Realistic merge/server latencies are far longer,
     but the condition belongs in the cell's obligations.
   - **A0 fork, rising edge (H_A0_FORK, new direction): breaks iff the A0
     branch into ustate.I4 is >= 29 ticks (116 ps) slower than the branch into
     ua1/ua2.** Path (witness wa=29):
     1. A0 rises and A2 rises (56).
     2. Client 2 drops r2 (4).
     3. q, still unheld because A0s has not arrived, flips for the waiting r1
        (56). 56 + 4 + 56 = 116.
     4. The grant handover then happens with A0 high, which breaks every
        property.
   - With a 24 ps q->ugrant route, mutex survives that skew, but ho, tx and
     amutex do not.
   - B-arb-a0fork covers the falling edge of A0. This is the complementary
     condition.

### Transport channel (pure delay, short pulses NOT filtered)

- **Every model fails mutex, including HELD. Storm's witnesses all show runts.**
  The unheld runs also hit ho, amutex and tx in rows where no q runt is
  involved.
  - (a) Two requests within one loop delay. q starts toggling, and its
    excitation reverses before q's output lands, giving a runt on q, which
    then propagates to both grants. This is the header's tier 3.
  - (b) A runt on the grant LUT itself (unheld witness, wq_g = 24 ps):
    1. r1 wins and q rises.
    2. r2 rises at the same instant, so q is settled and correct.
    3. ugrant still sees the old qg for the q->ugrant route delay, so g2 has
       an excitation pulse that wide.
    4. Under pure delay with fall 124 > rise 56, that pulse stretches to about
       92 ps and overlaps g1.
  - So under pure delay the race window includes the q->ugrant route as well
    as the loop delay.
  - The inertial model swallows (b). The truth lies between the two models,
    and only the involution or analog model (A-delay-involution, B-arb-analog)
    or a GLS can say how a 24 ps pulse behaves at a LUT input.
- **HELD restricted to runs with no runt on q (`*_nr` properties):**
  - mutex_nr = 0 for every server latency tried (10-40 ticks) and every A0
    fork skew <= 24 ticks.
  - amutex_nr, ho_nr and tx_nr are 0 for srv_lo >= 15 ticks (60 ps), as in the
    inertial model, and fail for wa = 32.
- So the digital conditions match the inertial ones. The only new failures
  under pure delay are the runt (tier-3) class, which no binary model can
  exclude. This agrees with the header's tier table and with B-arb-kleene's xx
  grant pair.
- `ovf` (queue overflow) is reachable in the full transport model, but
  **`ovf_nr` = 0**: no overflow happens in any run without a q runt. The
  no-runt results above are therefore exact for K=3. Checked for HELD with
  srv [15,20] and [40,45] and wa = 24, 28, 29 (`$S/arb_tp2.log`, 3-7 s each,
  70-220 k states).
- The A0-rise fork bound is the same as in the inertial model: no-runt
  properties hold at wa = 28 and fail at wa = 29 (116 ps).

## Probabilistic: resolution law (`meta_dtmc.py`, Storm DTMC)

**Model.** This does not postulate an exponential. It is a DTMC of the
linearised loop around the saddle:
- v' = a v + noise, with a = exp(dt (g-1)/tau) as in B-arb-analog, and v
  stochastically rounded so that E v' = a v exactly.
- Grid of ±4000 levels; the node is resolved at |v| = 4000.
- v0 is uniform on ±400 (the request skew, uniform inside the aperture).
- Noise is ±1 with probability p.
- Storm computes P(unresolved after k ticks) exactly, as bounded reachability.

Run: `$S/venv/bin/python -I meta_dtmc.py`, 115 s for 9 chains of 8002 states.

**Result.**
- Over the deterministic window, the local decay rate is **1.00 x ln a** in
  every case, i.e. P(unresolved at t) ∝ e^(-t (g-1)/tau). That is the
  e^(-t/tau_r) law, with tau_r = tau/(g-1) coming out of the gate gain.
- With **p = 0** the tail flattens at exactly 1/801. That is the probability
  of starting on the saddle itself, which never resolves. This is the
  "mutual exclusion is not unconditionally provable, only a probabilistic
  bound" statement, in a model checker.
- With noise, the far tail keeps decaying at 0.66-0.90 x ln a. The shortfall
  comes from the grid: noise of one grid unit dominates near the saddle. It
  shrinks toward 1 as p grows.
- An MTBF number would need: the real aperture, the gain g and tau from
  B-arb-analog, the noise level, and the board measurement (verify/MTBF.md).
  Nothing here replaces that measurement.

## Effort and coverage compared with Lean (shard B) and SMT (12a)

| | this probe (Storm TA) | Lean, shard B (Formal/Cells/) | SMT 12a (z3 BMC/k-induction) |
|---|---|---|---|
| setup | 40 s pip; ~330 lines of front end, ~2.5 h total including dead ends | Lean core, hand-written traces | pip z3/cvc5 |
| C-element | full sweep in 8-32 s; exact bound E >= dw_hi for FIFO channels | proof for all parameter values (symbolic dl, dw, E); WinDelay channel | proved per parameter instance by k-induction; counterexample traces |
| arbiter | the whole bd_arbiter with server and clients; 4 failure classes with exact thresholds and witnesses, in seconds | separate files per claim (handover, A0 fork, Kleene, analog), each a theorem with named hypotheses | (see C-12a-smt.md) |
| parameters | concrete integers per run; bounds found by sweeping. No proof for all delays | universally quantified | concrete per run |
| channels | inertial and FIFO transport, mixed per node; no non-FIFO WinDelay (it would need per-tick sampling, which is SMT's natural form) | WinDelay, transport, Kleene, ODE | win / fifo / inertial |
| state explosion | arbiter: 2 k-260 k states inertial, up to 1.3 M transport; fine at 4 ps resolution. Grows with clock range x number of nodes, so a whole netlist would need zones (UPPAAL/TChecker), which is the blocked part | none (symbolic) | unrolling depth |
| probabilistic | yes (DTMC, exact numbers) | analog ODE theorems (Mathlib), no probabilities | no |
| trust | Storm is unverified C++; the front end's semantics is unverified Python | kernel-checked | solver-checked, unverified encoding |

**What it buys the project.**
- A quick model checker to explore with before proving. It finds the boundary
  and the witness in seconds. Lean then proves the general statement with that
  exact bound.
- In this session it gave three concrete Lean targets:
  1. Tight C-element latency E >= dw_hi for FIFO channels.
  2. The A0-rise fork bound (116 ps for these arcs).
  3. Server latency >= 60 ps for ack exclusion in the held arbiter.
- The probabilistic layer supports the claim that only an e^(-t/tau) bound
  holds.

**Fidelity of the primitives used.**
- LUT: real INIT, Boolean function per output, with a single rise and fall
  arc per output (not per pin). Not the pass-transistor mux tree: no X and no
  glitch from the mux structure itself. Rise/fall arcs are from the header's
  trace, not from prjxray-db min/max.
- Wires: the same channel as the LUTs, with explicit delays only on the
  feedback and fork branches that matter. Other routes are folded into the
  consumer arc.
- Inertial: optimistic. It filters any pulse shorter than the propagation
  delay, which real LUTs do not.
- Transport: pessimistic. It passes and stretches any pulse.
- Environment: idealised. Free clients, a server that is a pure delay of R0.
- ua1/ua2 feedback: zero delay.
- Metastability: absent from the binary models. Runts show up as the binary
  shadow of tier 3. The DTMC models it, linearised, with an assumed noise
  term.

## Not done

- No UPPAAL, TChecker or Workcraft run. These are blocked; TChecker could be
  attempted if a git clone is allowed.
- No STG / speed-independence check through Petrify or MPSat. The haz monitor
  is the hand-made equivalent of output persistency.
- No per-pin delays and no prjxray corner bounds.
- No transport run with arc spread. It blows up: more than 5 GB and more
  than 20 min, OOM. This is the explicit-state digital-clock limit. Zone-based
  tools (UPPAAL, TChecker) or a symbolic engine are what would fix it.
  `stormpy.build_symbolic_model` (Storm's BDD engine) has not been tried; it
  is the next cheap thing to try.
