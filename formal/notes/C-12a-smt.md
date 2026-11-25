# C-12a: the C-element and arbiter checks in a SAT/SMT model checker

> **Correction (2026-10-29, probe C-12d; details in `C-12d-corner.md`).** The arbiter
> sections use prjxray's FAST_MAX/SLOW_MAX pair as rise/fall ("O6 rise 56 / fall 124", and
> in 2d rise (2,2) / fall (4,5)): a corner mix. Re-run at one consistent corner
> (`formal/tools/smt/run_onecorner.py`, one interval per output for both edges):
> - **2a, the 16 ps handover race / "route >= 16 ps proved": ARTEFACT.** At route 0 mutex is
>   PROVED unbounded (k-induction) at FAST, SLOW and every corner-model setting with
>   kappa <= 1/11 (`results/onecorner_tb.txt`). It returns only with box-like scatter (cons,
>   kappa = 0.1988), which is B's box overlap.
> - **2d, early ack needs k >= 10: the number is an artefact, the form stands.** Early ack iff
>   late >= early + ua2 arc, i.e. k >= 3 lut + 2 route: k >= 8 at FAST (2,2), CEX trace in
>   `results/onecorner_fork.txt`; 10 came from q's mixed fall arc. Also: the `owner` monitor
>   flags a fast server answering before g2 is up (not a protocol error); `arb.py` now has
>   12b's `tx` token monitor, which finds no violation at fork 0 at FAST/SLOW (depth 60).
> - **2b, transport routes / aperture 152 ps: numbers are artefacts.** At one corner route 0
>   shows no violation to depth 60 (FAST, SLOW); at 48 ps FAST fails through the grant-fork
>   runt (q route > O5 arc) with a bounded aperture of 72 ps (not 152), SLOW does not fail
>   (it needs a route of about 96 ps or more). `results/onecorner_real*.txt`.
> - **2c (Kleene) caveat** "ternary exclusion is not evidence of binary exclusion when
>   rise != fall": the rise != fall in question was the corner mix; at one corner the binary
>   handover race is gone too, so the ternary and binary verdicts agree there.
> - Section (1), C-element: unaffected (symmetric delay intervals, never mixed corners).

Track 12 (other tools), probe a. Files: `formal/tools/smt/` (all of it) and
this note. No Lean in this probe.

## Verdict

**It works, at low effort, as a counterexample finder, a threshold sweeper,
and an unbounded prover for fixed delay numbers. It cannot replace Lean for
proofs that hold for every delay value.**

The work took about 3 hours and 1250 lines of Python on z3. It models
`bd_c2`, `bd_arbcell` and `bd_arbiter` at gate level, in binary and Kleene
{0,1,X} forms:
- every LUT uses its real INIT and its real pin map;
- every LUT output and every routed net is a bounded-delay channel, feedback
  wires included.

It reproduces every timing threshold that shard B derived in Lean and that I
set up here:
- the C-element pulse width `Dmax`;
- the 16 ps handover margin;
- that exclusion needs request separation;
- the A0-fork early-ack condition;
- the Kleene grant pairs.

For each threshold the tool:
- finds the counterexample trace automatically;
- proves the safe side **unboundedly**, by k-induction or by Spacer (IC3/PDR).

What it does not give is a theorem that holds for every delay value. Each
SMT run fixes one integer delay box. B's Lean theorems hold for every `dl`,
`dw`, `L` and arc. Above about 60 state bits with counters of 30 or more,
proofs slow to minutes.

## Tools (installed through the proxy; versions recorded)

| tool | version | how | used for |
|---|---|---|---|
| z3 (`z3-solver`, python3.13) | 5.3.2 | `pip install z3-solver` | everything: BMC, k-induction, Spacer CHC (IC3/PDR) |
| cvc5 (python) | 1.4.2 | `pip install cvc5` | installed, not needed |
| python-sat | 1.9.dev17 | `pip install python-sat` | installed, not needed |
| nuXmv / NuSMV / yices2 | -- | not in the apt archive | -- |
| yosys-smtbmc | in the openXC7 toolchain | present | not used: it has no delay model for the cells' combinational loops |

`pip` installs into python3.13. `python3` is 3.11 and has no z3, so use
`python3.13`.

## Files and run commands

    cd /home/user/asyncfpga3/formal/tools/smt
    python3.13 run_celem.py pulse      # bd_c2 W/R sweeps            -> results/celem_pulse.txt
    python3.13 run_celem.py 4ph        # bd_c2 four-phase env E sweep -> results/celem_4ph.txt
    python3.13 run_celem.py kleene     # bd_c2 ternary               -> results/celem_kleene.txt
    python3.13 run_mono.py             # bd_c2 hazard check (P_mono) -> results/celem_mono.txt
    python3.13 run_arb.py tb           # bare arbcell, bd_prims_sim semantics -> results/arb_tb.txt
    python3.13 run_arb.py real         # bare arbcell, transport routes       -> results/arb_real.txt
    python3.13 run_aperture.py 48      # bare arbcell aperture (H_SEP)        -> results/arb_aperture.txt
    python3.13 run_arb.py kleene       # ternary bare arbcell                 -> results/arb_kleene.txt
    python3.13 run_arb.py arbiter      # shipped bd_arbiter, A0 fork          -> results/arb_arbiter.txt

What is in each file:
- `tsmc.py` (228 lines): the transition-system checker.
  - BMC.
  - k-induction with simple-path constraints, which is complete for finite
    state.
  - Spacer through z3's CHC engine.
  - A text waveform printer.
- `cells.py` (204 lines): LUTs and channels.
  - `lutB`: binary LUT, real INIT, I0 = LSB.
  - `lutK`: Kleene closure, which is B's H_KLEENE_LUT.
  - `o5`: the O5 half of a LUT6_2.
  - Channels:
    - `win`: B's WinDelay, `y(t) = x(t-d(t))` with `d(t)` in `[lo,hi]` chosen
      every tick; not FIFO.
    - `fifo`: a monotone sample index, so each edge gets its own delay and
      order is kept.
    - `inert`: a delay per transition, with separate rise and fall
      intervals. The inertial threshold is nondeterministic in `[lo,hi]`.
    - `kwin`: the ternary window join, Brzozowski-Seger style.
- `celem.py`: the `bd_c2` model, its environment and its spec monitors.
- `arb.py`: `bd_arbcell` (binary and ternary) and `bd_arbiter` with clients
  and server.
- `run_*.py`: the sweeps.
- `results/*.txt`: the logged verdicts. Every counterexample is printed as a
  waveform.

`results/celem_pulse_v1.txt` is a complete pulse sweep from an earlier
version. Its W_follow and R_min columns are valid. Its W_mono column used an
earlier, wrong definition of P_mono (power-up history not flushed), so it is
superseded by `celem_mono.txt`.

The pulse, 4ph and kleene reruns were cut short: the processes died while
sharing a sandbox at load average 20. The results that matter are in the
files listed above.

Run time per check:
- C-element (12-31 state bits): 0.03-50 s.
- Bare arbiter, 4-8 ps ticks (65-80 bits): BMC takes 2-90 s. k-induction
  proofs take 8-380 s.
- `bd_arbiter` (50-66 bits): 20-90 s per BMC at depth 55, under heavy load.

## (1) C-element `bd_c2`

### Model

The gates:
- Excitation: `e(t) = lutB(0x00E8_00E8_00E8_00E8, [a, b, qp, rst, 0, 0])`.
- LUT output: `O = chan_LUT(e)`, delay in `[dl_lo, dl_hi]`.
- Feedback: `qp = chan_wire(O)`, delay in `[dw_lo, dw_hi]`. This is the
  routed feedback into I2.
- At power-up, every channel's history is arbitrary.

The environment hypotheses:
- **H_RST(R):** `rst` is 1 on `[0, R-1]`, then 0 forever.
- **H_ENV_PULSE(W):** `a` and `b` are free, with one exception. When the
  ideal C-element `z = rst ? 0 : maj(a, b, z)` changes, `a` and `b` hold
  for W ticks.

The properties:
- `P_follow`: `cnt >= dl_hi -> O = z`, where `cnt` counts ticks since `z`
  changed.
- `P_mono`: O makes exactly z's transitions and no others, lagging by at most
  one. It is a counter, `#z changes - #O changes` in {0,1}, checked from
  tick `dl_hi` on. This is the hazard check.

### Results

Every entry is PROVED unbounded at the threshold, and has a BMC
counterexample one value below it.

| channel | (dl),(dw) = (1,1),(1,1) | (1,2),(1,2) | (2,3),(1,3) | (1,3),(2,2) | (2,2),(3,3) |
|---|---|---|---|---|---|
| Dmax = dl_hi + dw_hi | 2 | 4 | 6 | 5 | 5 |
| W_min, win | 2 | 4 | 6 | 5 | 5 |
| W_min, fifo | 2 | 4 | 6 | 5 | 5 |
| W_min, inert | 2 | 4 | **5** | 5 | **4** |
| R_min (all kinds; inert as its W) | = W_min | | | | |
| P_mono at W_min, win | proved | proved | proved | **CEX (glitch)** | proved |
| P_mono at W_min, fifo / inert | proved | proved | proved | proved | proved |

- **Bounded pure delay (win and fifo).** `W_min = Dmax = dl_hi + dw_hi`
  exactly, in all 10 cases. This agrees with B's `c2_follow_hold` (the bound
  is sufficient) and with `runt_loop` / `runt_oscillates` (it is tight for
  fixed delays). Here tightness is also shown with nondeterministic delays.
  - The counterexample at `Dmax - 1` is the runt. The pulse ends before the
    new value has gone round the feedback wire, so O falls back. The
    `(1,2),(1,2)` trace shows `O = __11_` and `qp = ____1`.
- **Inertial channel (new; not in B).** `W_min = Dmax - dl_lo + 1` in all 5
  cases. The LUT's inertia swallows the gap between the end of the pulse and
  the feedback's arrival. B proved only "a runt shorter than the threshold is
  lost". This is the complementary sufficient bound, for 5 numeric cases;
  there is no proof for every delay value.
- **Hazards.** With the non-FIFO window channel and `dl_hi - dl_lo >= 2`,
  `P_mono` fails at every W. O goes `0 -> 1 -> 0 -> 1` inside one transition
  window. This is an artefact of the channel reordering samples: silicon does
  not do that.
  - With `fifo` or `inert` (both order-preserving), O makes exactly one
    transition, proved at `W_min` for every case.
  - Spacer closed all the fifo cases; k-induction did not converge on them
    within k = 25.
  - B left the FIFO single-transition claim unproved. Here it is checked for
    these delay sets.
- **Four-phase environment (H_ENV_LATENCY E).** This tests B's derived
  condition `E >= dw_hi + (dl_hi - dl_lo)`. Two clients toggle `a`/`b` only
  E ticks after seeing O at their own value.
  - For `win (1,2),(1,2)` the smallest E is **2** whether latency counts from
    the first glimpse of the ack (B's H_ACK; proved by Spacer) or from a
    stable sighting (proved by k-induction). B's bound is 3.
  - So B's bound is sufficient but not tight, by one tick here.
  - For `(1,1),(1,1)` the smallest E is 1, equal to B's bound.
  - The other delay sets were not finished: the run was killed under load.
- **Ternary (kwin + lutK, binary environment).** `W_min = Dmax` and
  `R_min = Dmax`, the same as binary, for all 5 delay sets. Power-up X is
  cleared by a reset of length `Dmax`.
  - With slow input edges (an input may be X for `xin` ticks before it
    changes), `P_follow` fails at every W. The trace: `a = 1`, `b` passes
    through X, so `O` is X at once.
  - That X is an honest "edge in progress", not a defect. `P_follow` needs a
    tolerance window after an input edge before it can say anything
    stronger. That variant was not done.

## (2) Arbiter

### 2a. Bare `bd_arbcell` under testbench semantics: the 16 ps margin, proved

`run_arb.py tb` uses `bd_prims_sim.v`'s semantics:
- every LUT arc is an inertial channel at its prjxray max (O6 rise 56 / fall
  124; O5 rise 52 / fall 150 on pin I2);
- `BD_ROUTE_PS` is added to every arc;
- r1/r2 come straight from registers;
- requests are free-running.

| tick | route (ps) | result |
|---|---|---|
| 4 ps | 0 | grant overlap, CEX at depth 28; longest overlap run = **16 ps** |
| 4 ps | 8 | CEX |
| 4 ps | 12 | CEX |
| 4 ps | **16** | **PROVED unbounded** (k-induction k = 42, 110 s) |
| 4 ps | 20 | **PROVED unbounded** (k-induction k = 43, 115 s) |
| 8 ps | 16 | CEX (rounding pessimism) |
| 8 ps | 24 | PROVED (k = 22) |
| 8 ps | 48 | PROVED (k = 25) |

The route-0 counterexample is the header's: r2 drops while r1 waits; g2 falls
in 124 ps; g1 rises in 56 + 52 = 108 ps. This matches:
- the header's "rising grant wins by 16 ps";
- B's exact 16 ps threshold in `ArbHandover`;
- tb_arb_overlap's 89 overlaps at 0 ps and 0 at 354 ps.

### 2b. Bare `bd_arbcell` with transport routes: exclusion needs a request-separation hypothesis

`run_arb.py real` and `run_aperture.py` use a more faithful setting:
- prjxray min..max intervals on every arc;
- a transport (non-inertial) wire on q, and on r1/r2 into both LUTs;
- 8 ps ticks.

**Mutual exclusion fails at every routing tried** (0, 48 and 100 ps on every
net), for a minimum request level time of 8 ps or 400 ps. At route 0 the
longest overlap run within depth 60 is 48 ps.

The counterexamples (in `results/arb_real.txt` and the earlier exploratory
runs) have two shapes:

1. **Near tie, same sense.** r1 rises and q starts to move. r2 rises before
   the moved q reaches ugrant. ugrant sees r2 and a stale q, so g2 rises.
   Then the new q raises g1 while g2's slow fall is still in progress.
2. **A request re-pulsing within one loop delay.** For example r1 falls,
   then rises again while q is in flight (the `sep = 18` trace). The tie hold
   cuts the in-flight q into a runt. The runt circulates as a binary
   oscillation, with an overlap on every turn.

**Aperture.** H_SEP(s) says any two request edges are at least `s` apart.
With 48 ps on every net, the smallest separation that gives exclusion is
**152 ps** (19 ticks):
- **PROVED unbounded** by k-induction, k = 42, 377 s;
- with a counterexample at 144 ps.

How this compares with shard B's `ArbBinary`:
- It agrees with `exclusion_needs_sep`, `runt_overlap`, and "the runt needs
  the same sense, or a request pulsing for less than L; opposite senses are
  clean".
- B's sufficient H_REQ_SEP is "more than L = state arc + feedback route".
  With these arcs that is up to 172 ps. The SMT aperture is a tighter number
  for this specific box.
- It corrects the header's "a plain tie ... is resolved deterministically".
  That holds only for exactly simultaneous arrival, as B also notes.

**Why tb_arb_overlap counts 0 in the routed regime while this model
overlaps.**
- `bd_prims_sim.v` lumps the route *into the inertial LUT arc*. Any q
  excitation pulse shorter than `56 + BD_ROUTE_PS` is swallowed, so the near
  tie is decided silently.
- A real wire is transport. A real LUT's inertial threshold, if it has one,
  is its own arc, not arc plus route.
- So the routed zero of the free-running bench depends on a channel choice
  that favours exclusion. That does not make the tb wrong about the handover
  race it targets. It does mean the bench cannot see the near-tie digital
  overlaps that a transport-route model predicts.

### 2c. Kleene bare cell (`run_arb.py kleene`)

Setup: lutK, kwin channels with one `[1,2]` window per LUT, route 1, free
binary requests.

- `mutex11`: g1 and g2 are never both definitely 1. PROVED, k = 1.
- `no_1x`: a definite-1 grant never meets an X on the other. PROVED, k = 2.
  This is B's `grant_pairs`, now over traces with delays rather than per LUT
  evaluation.
- **Does X reach both grants? Yes.** CEX at depth 11: a request moves while q
  is in its uncertainty window.
- **X on q persists through a stable tie.** It is reachable after 10 and
  after 30 ticks of `r1 = r2 = 1`. This is B's `arb_x_held`, here as a trace.
- `q_def` fails as well, but only because kwin marks every ordinary q
  transition as X during its window.
- **Caveat found here.** With one symmetric window per LUT, the ternary model
  shows the ordinary handover race of 2a as an (X,X) window, never as (1,1).
  It proves Kleene exclusion even for timings where the rise/fall-aware
  binary model overlaps.
  - So ternary exclusion is **not** evidence of binary exclusion when
    rise != fall.
  - The ternary model also cannot tell a digital overlap from a metastable
    one: both show as (X,X).
  - Ternary channels that know rise from fall would be needed.

### 2d. Shipped `bd_arbiter` with clients and server (`run_arb.py arbiter`)

Setup:
- two four-phase clients and a four-phase server, with minimum latencies and
  no maximum;
- inertial LUTs, rise (2,2), fall (4,5);
- route 1 on every output net;
- the A0 fork modelled as three separate branches: to ustate.I4, ua1.I1 and
  ua2.I1.

Protocol monitor: at each A0 rise, it records the grant that is high as the
`owner`. It flags:
- an A0 rise with no single grant;
- any A_i rise that does not belong to the current server transaction, which
  is an early ack.

Results:
- **No A0 fork skew:** no violation of `mutex`, `ackmutex` or `owner`
  within depth 60.
  - The unbounded attempt (k-induction to k = 50, then Spacer for 600 s)
    did not finish within about 60 min of shared CPU and was stopped.
  - It is **unproved**: bounded depth 60 only.
- **Early ack, A0 branch to ua2 delayed by k extra ticks:**
  - none within depth 55 for k = 7 and k = 9;
  - **CEX for k = 10** and k = 11, at depth 47.
  - Threshold: an early ack needs at least 10 extra ticks, so
    `late = 1 + 10 = 11`.
  - The trace runs the whole protocol: client 1 is served, r1 falls, A0
    falls, q flips, g2 rises, and A2 = C(g2, A0) fires on the stale high A0
    with `own = 0`.

Comparison with B's `ArbA0Fork`:
- B's `client2_iff` says an early ack happens iff `late > early`. Here
  `early` = A0->ustate + ustate fall + q->ugrant + ugrant rise + g2->ua2 =
  1+4+1+2+1 = 9.
- B's transport model therefore predicts k >= 9. The SMT threshold is
  k >= 10, i.e. `late >= early + 2`, where 2 is the inertial rise arc of ua2.
- The one extra tick comes from the channel. With inertial LUTs, an A0/g2
  overlap shorter than ua2's rise arc is swallowed.
- This matches B's split between `early_ack_at` (transport, any overlap) and
  `early_ack_latches`.
- The SMT version is a full client/server run, not an isolated A0 fall.

### 2e. Connection to the unexplained `bd_arbcell` overlap (ARBITER.md "The 8% is not explained")

- **The handover race is capped.**
  - Under tb semantics the longest overlap is 16 ps here.
  - B's `prj_overlap_caps` gives 72 and 94 ps for any skew.
  - With transport routes and spread arcs, the longest run found within
    depth 60 is 48 ps.
  - All of these are well below the 203 ps minimum filter threshold. This
    confirms ARBITER.md: a single digital overlap does not explain the
    filtered events.
- **New here: a second digital mechanism that `bd_prims_sim.v` cannot show.**
  It is the near tie on the grant decoder, or a request re-pulse inside the
  aperture, under transport routes. Its worst case is a runt q that
  oscillates and produces an overlap on every turn.
  - A sustained binary oscillation is the binary shadow of a metastable
    excursion; on silicon it decays or latches.
  - Each overlap is still short. But a *train* of short overlaps could
    satisfy `raw & delay(raw)` if the train's period lines up with the
    filter's delay.
  - That is an **untested hypothesis**. It is checkable in this tool: add
    the `bd_delay` filter as two more channels and ask for `filtered`.
    Effort: about half a day.
  - The free-running rig violates H_SEP constantly, because its oscillators
    ask about 10^8 times a second. The aperture (152 ps at 48 ps routing,
    for this box) is the window that sets how often near-ties happen.
- **Kleene model.** The only way to get an unbounded both-X grant interval is
  through the X latched on q, i.e. the metastable tier. That is consistent
  with B's analog result that only a probabilistic bound holds.

## Comparison with shard B's Lean results

| aspect | SMT (this probe) | Lean (shard B) |
|---|---|---|
| agreement | every threshold checked here agrees with B (list in the Verdict). Two are tighter for specific boxes: four-phase E (2 vs 3), aperture (152 ps vs < 172 ps). One differs by the inertial arc: the A0 fork (k >= 10 vs 9) | -- |
| coverage, delays | one concrete integer box per run, swept over a few values. Inside a box, delays are nondeterministic per tick or per transition | parametric: every dl, dw, L and arc, plus numeric corner instances |
| coverage, depth | BMC depth 50-110. Unbounded proofs, by k-induction or Spacer, for all of: C-element follow/mono/4ph, tb arbcell (route >= 16 ps), aperture, ternary exclusion. **Not** for the full `bd_arbiter` (bounded only) | unbounded, by induction over time |
| found first here | the inertial bound `Dmax - dl_lo + 1`; that the tb's routed zero depends on route lumped into an inertial arc; that symmetric ternary windows hide the binary handover overlap; tighter E and aperture numbers | parametric conditions, the environment-latency condition, the analog e^(-t/tau) law (out of SMT's reach) |
| effort | about 3 h and 1250 lines of Python. Most of it is the model; each new question is one property line plus a sweep | per probe, 0.5-1 day and 400-1400 lines per file |
| run time | 0.03 s to 6 min per check; sweeps take 20-60 min | 1-9 s per file |
| fidelity risk | the encoding (Python building z3 terms) is not itself verified, so a modelling bug would look like a result. Mitigation: every threshold has a counterexample one step below it, and the thresholds agree with B | a statement can be wrong, but its proof cannot |

**Recommendation: use SMT as Lean's front end.**
1. SMT sweeps for the threshold and its trace.
2. Lean states and proves the theorem for every delay value.
3. SMT re-checks numeric corners whenever routed numbers change.

Because SMT runs on concrete numbers, it could check per-instance margins,
for example the A0 fork or the aperture of all 192 rig copies, straight from
routed SDF arcs. Effort: about 1 day to read SDF into `arb.py`.

## What does not work, and what was not done

- **Proofs for every delay value:** not attempted. Delays are concrete in
  each run. Symbolic Int delay parameters are possible in principle, but
  k-induction over them is unlikely to close.
- **Full `bd_arbiter` unbounded proof:** not closed. k-induction to k = 50
  and Spacer for 600 s were stopped after about 60 min on a CPU shared at
  load 20. Bounded result only.
- **Spacer vs k-induction:** Spacer closed the fifo hazard proofs and one
  four-phase case that k-induction did not. It timed out (300 s) on the
  70-bit transport arbcell.
- **Unfinished sweeps:** the four-phase sweep beyond two delay sets, the
  narrowest-grant (runt grant) search, and the aperture at routes other than
  48 ps. All were cut by load. Re-run them with the commands above.
- **Not modelled:**
  - involution channels;
  - per-pin LUT arcs (lumped per output here);
  - analog behaviour;
  - ternary channels that know rise from fall;
  - the `hw/arb_mtbf.v` width filter.
- **Time quantisation:** 4 ps or 8 ps ticks. Rounding is pessimistic (ceiling
  for max, floor for min). At 8 ps it moved the tb threshold from 16 ps to
  24 ps; at 4 ps the threshold is exact.

## Fidelity of every primitive model

- **LUT6 / LUT6_2.**
  - The real INIT and pin map.
  - Values: binary `lutB`, or Kleene `lutK`. `lutK` is H_KLEENE_LUT and is
    not checked here against the mux tree; see B's MuxTree.
  - O5 is the lower 32 bits with I5 = 1.
  - Delay is lumped at the output: rise and fall intervals per output from
    prjxray, not per pin.
- **Channels.**
  - `win` is B's WinDelay: the weakest bounded pure delay, not FIFO. It
    allows sample-reordering glitches that silicon does not produce.
  - `fifo` keeps order and gives each edge its own delay.
  - `inert` has a nondeterministic threshold and separate rise/fall bounds.
    It is used for the LUT arcs in the arbiter. Whether a real LUT is
    inertial at all is unknown: involution channels say pulses shrink rather
    than vanish.
  - `kwin` is the ternary window join, an over-approximation (B-S).
- **Routing.** A fixed transport delay per net, implemented as a shift
  register. No RC shaping and no pulse degradation. The `tb` section instead
  uses the bench's lumped inertial route, on purpose.
- **Environment.**
  - Four-phase clients and server with minimum latencies and no maximum.
  - Free-running requests with a minimum level time, and optionally H_SEP.
  - A single reset pulse, or a start from any quiescent consistent state.
- **Time.** Discrete ticks: 4 or 8 ps for the bare arbiter, abstract units
  for the C-element and `bd_arbiter`.
