# C-12a: the C-element and arbiter checks in a SAT/SMT model checker

Track 12 (other tools), probe a. Files: `formal/tools/smt/` (all of it) and
this note. No Lean in this probe.

## Verdict

**Works, with little effort, as a counterexample engine and a parameter
sweeper. It is weaker than Lean for parametric proofs.** In about 3 hours and
about 1200 lines of Python on z3, the checker models `bd_c2`, `bd_arbcell` and
`bd_arbiter` at gate level. Every LUT uses its real INIT and pin map. Every LUT
output and every routed net is a bounded-delay channel, the feedback wires
included. The model is binary, and also Kleene {0,1,X}. The checker:

- re-derives, exactly, every timing threshold that shard B proved in Lean and
  that I could set up here (C-element pulse width, the 16 ps handover margin,
  the A0-fork early-ack condition);
- finds the counterexample traces automatically;
- proves the safe side **unboundedly** (k-induction) for concrete delay numbers.

What it does not give: a proof for *all* delay values. Every SMT result is for
one concrete integer delay box. Shard B's Lean theorems are parametric (for
every `dl`, `dw`, `L`, ...). Spacer (IC3/PDR) rarely closed anything that
k-induction could not. Above roughly 60 state bits with counters of 30 or
more, k-induction slows to minutes and Spacer times out.

## Tools (installed through the proxy, recorded versions)

| tool | version | how | used for |
|---|---|---|---|
| z3 (z3-solver, python3.13) | 5.3.2 | `pip install z3-solver` | everything: BMC, k-induction, Spacer CHC (IC3/PDR) |
| cvc5 (python) | 1.4.2 | `pip install cvc5` | installed, not needed (z3 was enough) |
| python-sat | 1.9.dev17 | `pip install python-sat` | installed, not needed |
| nuXmv / NuSMV / yices2 | -- | not in the apt archive, not on pip | -- |
| yosys-smtbmc | openXC7 toolchain | present | not used: no delay model for the combinational SCCs of the cells |

**Use python3.13.** `pip` installs into 3.13; `python3` is 3.11 and has no z3.

## Files and run commands

    cd /home/user/asyncfpga3/formal/tools/smt
    python3.13 run_celem.py            # C-element sweeps -> results/celem.txt   (~40 min)
    python3.13 run_arb.py tb           # bare arbcell, bd_prims_sim semantics -> results/arb_tb.txt
    python3.13 run_arb.py real         # bare arbcell, transport routes       -> results/arb_real.txt
    python3.13 run_arb.py kleene       # ternary bare arbcell                 -> results/arb_kleene.txt
    python3.13 run_arb.py arbiter      # shipped bd_arbiter, A0 fork          -> results/arb_arbiter.txt

- `tsmc.py` (228 lines): the transition-system checker. It has BMC, k-induction
  with simple-path constraints (complete for finite state), Spacer through
  z3's CHC engine, and a text waveform printer.
- `cells.py` (204 lines) holds the LUTs and channels:
  - `lutB` (binary, real INIT, I0 = LSB) and `lutK` (Kleene closure, B's
    H_KLEENE_LUT); `o5` for LUT6_2;
  - the channels `win` (B's WinDelay: `y(t) = x(t-d(t))`, `d(t)` in
    `[lo,hi]` chosen every tick, non-FIFO), `fifo` (the same, but monotone:
    every edge gets its own delay in `[lo,hi]` and order is kept), `inert`
    (per-transition delay with separate rise and fall intervals, and a
    nondeterministic inertial threshold in `[lo,hi]`) and `kwin` (ternary
    window join, Brzozowski-Seger style).
- `celem.py` holds the `bd_c2` model and its environment and spec monitors.
  `arb.py` holds `bd_arbcell` (binary and ternary) and `bd_arbiter`, with its
  clients and server.
- `results/*.txt` holds the logged results, with every counterexample printed
  as a waveform.

Run time per check: 0.03-40 s for the C-element (12-23 state bits). For the
bare arbiter at 4-8 ps ticks (65-80 bits) it is 2-500 s. For `bd_arbiter`
(50-66 bits) it is 20-90 s per BMC at depth 60.

## (1) C-element `bd_c2`

**Model.** The excitation is `e(t) = lutB(0x00E8_00E8_00E8_00E8, [a, b, qp,
rst, 0, 0])`. Then `O = chan_LUT(e)` with delay in `[dl_lo, dl_hi]`, and
`qp = chan_wire(O)` with delay in `[dw_lo, dw_hi]`, the routed feedback into
I2. At power-up every channel's history is arbitrary. The environment:

- **H_RST(R):** `rst = 1` on `[0, R-1]`, then it falls and stays low.
- **H_ENV_PULSE(W):** a, b are free, except that once the ideal C-element `z`
  changes (an enabling `a = b = v != z` appears), a and b hold for W ticks.

The spec monitor computes `z(t) = rst ? 0 : maj(a, b, z(t-1))` and
`cnt` = ticks since `z` changed. Two properties:

- `P_follow`: `cnt >= dl_hi -> O = z`.
- `P_mono`: O makes exactly z's transitions and no others, lagging by at most
  one. It is a counter, `dz = #z-changes - #O-changes in {0,1}`. This is the
  hazard check.

**Results** (`results/celem.txt`; every row is PROVED by k-induction at the
threshold and has a BMC counterexample one below it):

| channel | dl | dw | Dmax | W_min (P_follow) | W_min (P_mono) | R_min |
|---|---|---|---|---|---|---|
| win  | (1,1) | (1,1) | 2 | 2 | 2 | 2 |
| win  | (1,2) | (1,2) | 4 | 4 | 4 | 4 |
| win  | (2,3) | (1,3) | 6 | 6 | 6 | 6 |
| win  | (1,3) | (2,2) | 5 | 5 | **never** (glitch) | 5 |
| win  | (2,2) | (3,3) | 5 | 5 | 5 | 5 |
| fifo | same five | | | = Dmax in every row | see results file | = Dmax |
| inert| (1,1) (1,1) / (1,2) (1,2) / (2,3) (1,3) / (1,3) (2,2) / (2,2) (3,3) | | 2/4/6/5/5 | **2/4/5/5/4** | 2/4/5/5/4 | 2/4/5/5/4 |

- **Bounded pure delay (win, fifo):** `W_min = Dmax = dl_hi + dw_hi`,
  exactly, in every case. This agrees with shard B's `c2_follow_hold`
  (sufficient) and `runt_loop` / `runt_oscillates` (tight for fixed delays).
  Here the tightness is also shown with nondeterministic delays. The
  counterexample at `W = Dmax - 1` is the runt: the pulse ends before the new
  value has gone round the feedback wire, so O falls back. See
  `results/celem.txt`, e.g. the `(1,2),(1,2)` trace with `O = __11_` and
  `qp = ____1`.
- **Inertial channel (new, not in B):** the exact bound is
  `W_min = Dmax - dl_lo + 1`. It fits all five delay sets. The LUT's inertia
  swallows the gap of up to `dl_lo - 1` ticks between the end of the pulse and
  the feedback's arrival. B proved only that "a runt shorter than the
  threshold is lost". This is the complementary sufficient bound, but only for
  these five numeric cases; it is not proved parametrically.
- **Hazards:** with the non-FIFO window channel, `P_mono` fails at every W
  once `dl_hi - dl_lo >= 2`. The `(1,3),(2,2)` counterexample shows O going
  `0 -> 1 -> 0 -> 1` inside one transition window: a sample-reordering
  artefact of the non-FIFO channel. With `fifo`/`inert` (order-preserving)
  there is no hazard at the same `W_min`. So the choice of channel matters for
  glitch questions and not for the settle question. B's notes leave the FIFO
  single-transition claim unproved; here it is checked for these delay sets.
- **Four-phase environment (H_ENV_LATENCY E)** checks B's derived condition
  `E >= dw_hi + (dl_hi - dl_lo)`. Two clients toggle a/b only E ticks after
  seeing O at their own value.
  - Latency counted from the *first glimpse* of the ack (B's H_ACK): see the
    results file.
  - Latency counted from a *stable* sighting (a glitch restarts the count):
    E_min is smaller (e.g. 2 against B's 3 for `(1,2),(1,2)`). B's bound is
    sufficient, not always tight; how tight it is depends on how the
    environment observes the ack.
- **Ternary (kwin, lutK):** the same W sweep is in the results file. Power-up
  X is cleared by reset with `R_min = Dmax`. When an input edge may be X for
  `xin` ticks (a slow edge), see the `xin` rows. An X that enters the loop on
  a non-agreeing input stays (B's `c_fixpoints`).

## (2) Arbiter

### 2a. Bare `bd_arbcell`, testbench semantics: the 16 ps margin, reproduced exactly

`run_arb.py tb` uses the `bd_prims_sim.v` semantics:

- every LUT arc is an inertial channel at its prjxray max (O6 rise 56 /
  fall 124; O5 rise 52 / fall 150 on pin I2);
- `BD_ROUTE_PS` is added to every arc;
- r1 and r2 come straight from registers.

With 4 ps ticks:

- route 0 / 8 / 12 ps: grant overlap reachable (counterexample at depth 28-34;
  the trace is r2 dropping while r1 waits);
- route 16 ps: no overlap to depth 110 (bounded);
- with 8 ps ticks (2 ticks of rounding pessimism): route 24 and 48 ps are
  PROVED unbounded by k-induction (k = 22, 25).

This is the header's "rising grant wins by 16 ps" and B's exact 16 ps
threshold (`ArbHandover`), found by search rather than by derivation. The
maximum overlap run at route 0 is in `results/arb_tb.txt`.

### 2b. Bare `bd_arbcell` with transport routes: no exclusion without a separation hypothesis

`run_arb.py real` is the more faithful setting:

- prjxray min..max intervals on every arc;
- a transport (non-inertial) wire on q **and** on r1/r2 into both LUTs.

Here mutual exclusion **fails at every routing tried** (0, 48, 100 ps on
every net), with any minimum request level time, P = 1 or 400 ps.

The counterexample is the **near-tie: both requests rising (same sense)
within the decision window**:

1. r1 rises and q starts to move.
2. r2 rises before the moved q has reached ugrant.
3. ugrant sees r2 and a stale q, so g2 rises.
4. The new q then raises g1 while g2's slow fall (124 ps) is still in
   progress.

Alternatively, the in-flight q is cut by the tie hold into a runt that
circulates (binary oscillation). Either way g1 and g2 are both high, and
runt grants appear.

- This agrees with shard B's `ArbBinary`: `exclusion_needs_sep`,
  `runt_overlap`, and "the runt needs the requests moving in the SAME sense
  within one loop delay; opposite senses are clean".
- It is a correction to the header's "a plain tie ... is resolved
  deterministically": that holds only for exactly simultaneous arrival.

The **aperture**, the smallest H_SEP (any two request edges at least `sep`
apart) that makes the cell mutually exclusive, is swept in
`results/arb_real.txt`.

**Why tb_arb_overlap's routed count is 0 while this model overlaps.** In
`bd_prims_sim.v` the route is lumped *into the inertial LUT arc*. A q
excitation pulse shorter than `56 + BD_ROUTE_PS` is therefore swallowed, and
the near-tie is silently decided. The real wire is transport, and the real
LUT's inertial threshold, if it has one, is its own arc and not arc plus
route.

So the testbench's routed-regime zero rests on a channel choice that favours
exclusion. That does not make the tb wrong for the handover race it targets.
But it means the free-running bench cannot see the near-tie digital overlap
that a transport-route model predicts. That overlap is a candidate
contributor to the hardware rig's events (see 2e).

### 2c. Kleene bare cell (`run_arb.py kleene`)

Setup: lutK, kwin channels with one `[lo,hi]` per LUT, binary free requests.

- `mutex11`: g1 = g2 = definite 1 never happens. PROVED, k-induction k = 1.
- `no_1x`: a definite-1 grant never meets an X on the other. PROVED, k = 2.
  This is B's `g1_t_forces`/`grant_pairs`, now over traces with delays and
  not only per LUT evaluation.
- **X reaches both grants: yes.** `no_xx` gives a counterexample at depth 11:
  a request moves while q is in its uncertainty window.
- **X on q persists through a stable tie:** reachable for 10 and 30 ticks of
  `r1 = r2 = 1` (B's `arb_x_held`, here as a trace).
- **Caveat found here.** With one symmetric window per LUT, the ternary model
  shows the *ordinary* handover race (2a) as an (X,X) window and never as
  (1,1). It cannot tell a digital overlap from a metastable one, and it
  proves Kleene exclusion even for configurations where the binary model with
  rise/fall arcs overlaps. Ternary exclusion is therefore **not** evidence of
  binary exclusion when rise != fall. Rise/fall-aware ternary channels would
  be needed.

### 2d. Shipped `bd_arbiter` with clients and server (`run_arb.py arbiter`)

The protocol monitor `owner` is set at each A0 rise from the grant that is
high. It flags:

- an A0 rise with no single grant;
- an A_i rise that does not belong to the current server transaction (an
  early ack).

Also checked: `mutex` (g1 g2) and `ackmutex` (A1 A2).

Delay model: LUT rise (2,2), fall (4,5), route 1 on every output net,
inertial LUTs.

- With no A0 fork skew: no violation of any of the three to depth 60. The
  unbounded attempt (k-induction / Spacer) is in the results file.
- **Early ack** is reachable when the A0 branch into ua2 is delayed enough.
  The trace in `results/arb_arbiter.txt` is the full protocol (client 1
  served, r1 falls, A0 falls, q flips, g2 rises, A2 = C(g2, A0) fires on the
  stale A0 high, `own = 0`).
  - B's `client2_iff` says early ack iff `late > early`, with
    `early = A0->ustate + ustate fall arc + q->ugrant + ugrant rise arc +
    g2->ua2` = 1+4+1+2+1 = 9 ticks here, and `late = 1 + skew`.
  - The threshold the sweep finds is in the results file, with the inertial
    rise arc of ua2 as the expected offset.
  - This agrees with B's `ArbA0Fork`, and gives the counterexample as a
    complete client/server protocol run rather than an isolated A0 fall.

### 2e. Connection to the unexplained bd_arbcell overlap (ARBITER.md "The 8% is not explained")

- The handover race (2a) is capped. B's `prj_overlap_caps` gives 72/94 ps,
  and the bounded max-overlap search here agrees in order of magnitude (see
  results). That is below the 203 ps filter threshold, so it cannot explain
  the filtered events, as ARBITER.md says.
- The binary transport model (2b) adds a second digital mechanism that
  `bd_prims_sim.v` cannot show: the near-tie on the grant decoder, plus
  sustained binary oscillation of a runt q.
  - On silicon a sustained oscillation is not stable. It is the binary shadow
    of a metastable excursion.
  - The width of each overlap is still bounded by the grant fall/rise skew,
    but the oscillation can repeat it every loop period.
  - A two-link width filter that ANDs `raw` with `raw` delayed could
    therefore fire on a *train* of short overlaps, if the train's period lines
    up with the filter delay. That is an untested hypothesis, but it is
    expressible and checkable in this tool: add the `bd_delay` filter as two
    more channels.
- In the Kleene model, a long both-X grant interval (unbounded) is reachable
  only through the X-latch on q. That is the metastable tier, consistent with
  B's analog result that only a probabilistic bound holds.

## Comparison with shard B's Lean results

| aspect | SMT (this probe) | Lean (shard B) |
|---|---|---|
| agreement | every shared threshold agrees: W = Dmax; the 16 ps handover margin; exclusion needs request separation (same-sense near tie); A0-fork early ack iff late > early; Kleene (1,1) impossible, (X,X) reachable, X latched on a tie | -- |
| coverage: delays | one concrete integer box per run, swept over a handful of values; each box allows nondeterministic per-tick / per-transition delays | parametric: for all dl, dw, L, arcs (symbolic), plus numeric corner instances |
| coverage: depth | BMC bounded (depth 60-110); k-induction unbounded where it closed (C-element: all; tb arbcell: routes >= 24 ps; ternary arbcell); Spacer: no closures beyond k-induction in the time given | unbounded by induction over time |
| what it found first | the inertial-channel bound `Dmax - dl_lo + 1`; that the tb's routed zero relies on the route being lumped inertially; that symmetric ternary windows hide the binary handover overlap | the parametric conditions, the environment-latency condition, the analog e^(-t/tau) law (out of SMT's reach) |
| effort | ~3 h, ~1200 lines of Python, mostly the model; each new question is one property line plus a sweep | per probe 0.5-1 day; ~400-1400 lines per file |
| run time | 0.03 s - 10 min per check; whole sweeps 20-60 min | 1-9 s per file |
| fidelity risk | the encoding (Python building z3 terms) is not itself verified; a modelling bug looks like a result. Mitigation: every threshold has a counterexample one step below it, and the thresholds agree with B | the statement can be wrong but the proof cannot |

**Recommendation.** Use SMT as the search front end to Lean:

1. Sweep and find the threshold and its trace with SMT.
2. State the parametric theorem in Lean.
3. Re-check numerical corners with SMT when the routed numbers change. It
   runs on concrete SDF numbers, so it could check per-instance margins (all
   192 rig copies) directly from routed delays. Effort: about 1 day to read
   the SDF arcs per copy into `arb.py`.

## What does not work / not done

- **Parametric proofs:** not possible directly. Integer delays are concrete
  per run. An SMT encoding with symbolic delays (Int parameters in the
  transition relation) is possible in principle, but k-induction over
  symbolic delays did not seem worth trying in the time box.
- **Spacer (IC3):** timed out (300 s) on the 70-bit transport arbcell. It
  added no proofs beyond k-induction.
- **fifo P_mono proofs:** k-induction does not converge quickly (the lag
  variable makes long unreachable paths). Some rows end UNKNOWN after a 120 s
  Spacer run (see the results file).
- **Not modelled:**
  - involution channels;
  - per-pin LUT arcs (O5 per pin is in prjxray; lumped per output here);
  - analog behaviour;
  - rise/fall-aware ternary channels;
  - the width filter of `hw/arb_mtbf.v`.
- Time quantisation: 4 or 8 ps ticks. Rounding is pessimistic (ceil for max,
  floor for min), and that shifted the 8 ps tb threshold from 16 to 24 ps.

## Fidelity of every primitive model

- **LUT6 / LUT6_2:** the real INIT and pin map, binary `lutB`, or Kleene
  `lutK` (H_KLEENE_LUT, not verified against the mux tree here; see B's
  MuxTree). O5 is the lower 32 bits with I5 = 1. The delay is lumped at the
  output: per-output rise/fall intervals from prjxray, not per pin.
- **Channels:**
  - `win` is B's WinDelay (weakest bounded pure delay, non-FIFO). It allows
    sample-reordering glitches that silicon does not produce.
  - `fifo` is order-preserving, with per-edge delays.
  - `inert` has a nondeterministic threshold in `[lo,hi]` and rise/fall
    asymmetric bounds. It is used for the LUT arcs in the arbiter. Whether a
    real LUT is inertial at all is unknown (involution channels say pulses
    shrink, not vanish).
  - `kwin` is the ternary window join (over-approximation, B-S).
- **Routing:** a fixed transport delay per net (shift register). No RC
  shaping and no pulse degradation.
- **Environment:** clients and server are four-phase, with minimum latencies
  and no maximum. Free-running requests have a minimum level time. Reset is
  one pulse.
- **Time:** discrete ticks of 4 or 8 ps (arbiter) or abstract units (C-element,
  bd_arbiter).
