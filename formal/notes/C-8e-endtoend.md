# C-8e: end to end, "the checker accepts the routed pipe" ⇒ "the pipe is a FIFO" (tracks 8 + 10)

## Verdict

**Works, for the fixed-delay (one delay per arc per run) reading of 10a's
semantics.** One theorem, `Formal.Net.EndToEnd.end_to_end`:

    checkPipe R n W m h = true → PipeRun n W P → Realizes R n W P → 0 < n →
      (every link obeys the four-phase protocol) ∧ (#tokens out ≤ #tokens in) ∧
      (k-th token out = k-th token in, same value)

`checkPipe` is a conjunction of calls to 10a's verified `check` on small
race netlists built from the routed arc intervals; `PipeRun` is a gate-level
model of `bd_pipe` (pins are routed copies, the real `bd_c2n` and `bd_latch`
INITs evaluated on the pins); the conclusion is literally 8a's
`muller_pipeline` conclusion, obtained by instantiating `muller_pipeline`.
On the toy: accepted 2-stage route ⇒ FIFO (`good_fifo`), with a satisfying
run that delivers the token (`good_delivers`); the same route without its
SDELAY line is rejected for every `(m, h)` (`bad_rejects`) and has a concrete
run inside its intervals that delivers 0 for a sent 1 (`bad_counterexample`).

No sorry / admit / axiom / native_decide. About 1000 lines of core Lean, ~2.5 h.
Each file checks in seconds (the toy's kernel `decide`s over 64-80 ticks are
fast).

Not covered (stated as hypotheses or out of scope, see below): per-event
(glitch-passing) BoundedDelay in a multi-token run; FASTRISE/FASTFALL delay
lines with N ≥ 2 (asymmetric); the latch's and C-element's own feedback-loop
timing (shard B's contracts, here a one-tick LUT cell / an SI gate).

## Files and run command

| file | content |
|---|---|
| `formal/lean/Formal/Net/EndToEndRace.lean` | `Path`, `inPath` (per-arc delays in intervals), `fan2 E L` (launch + early chain + late chain netlist), `race2` (= 10a `check` on it), `fanRun` (the step-launch `FixedRun` of `fan2` for given delays), `race2_sound` |
| `formal/lean/Formal/Net/EndToEnd.lean` | change counts `N`, `parity`; `PinLink` and its lemmas (`inv`, `protocol`, `sep`, `hold`, `openWidth`, `srcData`); latch cell (`latchF`, `latch_pair`, `latch_bit`); `enc` bus; `Pipe`, `PipeRun`, `Route`, `Realizes`, `checkPipe`, `Timing`; `timing_of_check`, `links`, `cel_si`, `latch_contract`, `src_setupHold`, `sep_ok`, `hold_ok`, `stage`, `fifo_of_timing`, `end_to_end` |
| `formal/lean/Formal/Net/EndToEndToy.lean` | `good` / `bad` routes, `good_check`, `bad_check`, `good_fifo`, runs `cex` / `run_good`, `cex_run`, `good_run`, `cex_realizes`, `good_realizes`, `bad_rejects`, `bad_counterexample`, `good_delivers` |
| `formal/lean/Wip/C8e/Axioms.lean` | `#print axioms` on the main theorems (proves nothing) |

    cd /home/user/asyncfpga3/formal/lean && export PATH=$HOME/.elan/bin:$PATH
    export LEAN_PATH=$PWD/.lake/build/lib/lean
    # deps (already built by 8a/10a): Formal/Timing/{Semantics,Checker}, Formal/Net/{Handshake,HandshakeMuller}
    for f in EndToEndRace EndToEnd EndToEndToy; do
      ../slot.sh lean -o .lake/build/lib/lean/Formal/Net/$f.olean Formal/Net/$f.lean; done
    ../slot.sh lean Wip/C8e/Axioms.lean

The lead must add the three modules to the root `Formal.lean` and `check.sh`.

## Where 8a's and 10a's time bases did not match, and the refinement

8a's `MullerStage` (the one `muller_pipeline` uses) is a node-level
speed-independent model: one tick = one possible gate step, the C-element at
step t reads its neighbours' nodes AT t (zero wire delay), the fork of `c` is
isochronic (`H_NODE`: req_out = ack_in = latch enable), data wires have zero
delay, and the latch is an abstract node-level contract (`H_LATCH`).
(`MullerStageW` adds a 1-tick wire on the two controller pins; it is not
what `muller_pipeline` takes.) 10a's `Run` is a single-launch DAG: node 0
switches once at 0, each arc has a pin trace in `BoundedDelay lo hi` of its
source, cells are zero-delay functions of pins. Four mismatches:

1. **Wire delay at the controller pins / non-isochronic fork.** Refinement:
   `PipeRun.H_CEL` evaluates the real `bd_c2n` INIT (`celN`) on the PINS,
   `R` pin of stage k = `shift (dR k) (x (k-1))`, `A` pin =
   `shift (dA k) (x (k+1))`, `shift` being 10a's exact-delay pin (the
   `FixedRun` pin). Each branch of each node's fork has its own delay. The
   node-level protocol is then derived (`PinLink.protocol`) from a
   change-count invariant (`PinLink.inv`):
   `N q t ≤ N p (t - dR)` and `N p t ≤ N q (t - dA) + 1`
   (receiver ≤ what the sender had done dR ago; sender ≤ one more than what
   the receiver had done dA ago). From the protocol on both adjacent links,
   8a's `H_CEL_SI` follows (`cel_si`). This also discharges 8a's open item
   "general bounded wire delay at all pins" for fixed delays of any size, and
   removes the isochronic-fork assumption for the controller.
2. **Multi-token cyclic run vs single launch.** The obligations are checked on
   launch-relative race netlists (`fan2`). They apply to every token because
   an exact shift is time-invariant: the response of a path to any event at
   time e is its step response moved to e. `race2_sound` turns the check into
   an inequality between the run's path sums (via a step-launch `FixedRun` and
   10a's `check_sound`, not by re-deriving interval arithmetic); the
   event-ordering lemmas (`PinLink.sep/hold/openWidth/srcData`, all from the
   count invariant) turn those inequalities into 8a's `Sep`, `Hold`,
   `SetupHold`.
3. **Per-event vs per-run delay.** The multi-token result is for
   H_FIXED_DELAY (10a's `FixedRun` reading: one delay per arc per run, the
   "one PVT corner, one wire" reading). With per-event `BoundedDelay` a pin may
   follow a new value and then echo the old one (a glitch inside [lo, hi] of a
   transition); the pin then changes more often than its source and the count
   invariant fails. Whether the pipe stays correct then needs a pulse-width
   condition (the echo must die before the other party can react: a loop delay
   ≥ hi - lo per pin). Not done. The checker side is unaffected (every FixedRun
   is a Run).
4. **Data wires, latch enable fan-out, latch contract.** 8a's `H_LATCH` is a
   node-level contract with zero-delay wires. Here it is DERIVED
   (`latch_contract`, from `latch_bit`) for a pin-level LUT latch
   (`latchF` = `bd_latch`'s `B8` INIT; `latch_pair` shows both outputs of the
   `FF33_CC00_B8B8_B8B8` LUT6_2 are the same latch function) with D pin
   `shift (dD j b) (Q j b)` (bus wire of bit b) and enable pin
   `shift (dG j b) (x (j+1))` (that LUT's branch of the enable net), one tick
   of cell delay. It needs three facts per bit, all checked: data at the D pin
   by the node close (`dD + 1 ≤ m`), data held until the enable pin closes
   (`dG ≤ dD + h`), and the enable pin seeing the open phase before the close
   (`dG ≤ dR(j+2) + dA(j+1) + 1`, open width = next stage's round trip, from
   `PinLink.openWidth`). The third one is new: 8a's zero-delay model hides
   it. A 1125 ps enable spread (LIBRARY.md, 32-bit link) against a short
   round trip would violate it.

A smaller mismatch: 8a's chan data is a `Nat`; here it is `enc W` of W bit
traces (`enc_inj`/`enc_congr` move between them), so per-bit wire skew is
visible to the checker.

## The obligations as checker constraints (`checkPipe R n W m h`)

`race2 E L s`: 10a `check` on `fan2 E L`, "latest(L) + s ≤ earliest(E)".
Paths are the routed arc lists; constants are dummy arcs `(c, c)`.

| 8a obligation | cells/arcs it reads (bd_link.v / bd_latch.v) | race | rule |
|---|---|---|---|
| `SetupHold m h (ch 0)`, setup half | source req wire, DELAY line, C-LUT pin of stage 0 | `race2 (req 1) [] (m-2)` | (bundling at the input) |
| `SetupHold`, hold half | stage-0 node → ack_in wire (DACK), source pin | `race2 (ack 0) [] (h-1)` | H (pin source) |
| `Sep m (ch j) (ch (j+1))` | node j → wire, SDELAY line, wire, C-LUT req pin of stage j+1 | `race2 (req (j+2)) [] (m-1)` | I |
| `Hold h (ch j) (ch (j+1))` | node j+1 → ack wire (DACK), C-LUT ack pin of stage j | `race2 (ack (j+1)) [] (h-1)` | H |
| `H_LATCH` setup, stage j bit b | data bus wire into the latch LUT | `race2 [(m-1,m-1)] (dat j b) 0` | (latch setup) |
| `H_LATCH` hold | enable wire vs data wire + h | `race2 (dat j b ++ [(h,h)]) (en j b) 0` | H (enable skew) |
| `H_LATCH` open width | enable wire vs next-stage round trip | `race2 (req (j+2) ++ ack (j+1) ++ [(1,1)]) (en j b) 0` | (new; L-like) |

The "+1"/"+2" are the one-tick gate steps of the SI C-element (each node move
takes at least one tick after its pins).

Decision: 8a's `muller_pipeline` takes ONE `(m, h)` for all links, so the
races are cut at the node with a global margin: the real bundling race "data
wire of stage j+1 vs request path into stage j+1" is checked as
`dat ≤ m-1 ≤ req`. Sound, conservative by the slack between the two halves.
Changing that needs a per-link `(m_j, h_j)` version of `muller_pipeline`
(a small edit to 8a's files, which I don't own).

## Toy runs (`EndToEndToy.lean`, units of 10 ps, ILLUSTRATIVE)

- `good`: req 1 = wire 6..8, DELAY LUT 6..8, pin 1..2; req 2 = wire 2..3,
  SDELAY LUT 10..12, wire 1..3, pin 1..2; req 3 = 10..12, 1..2; ack = 1..2,
  1..2 (DACK = 0); en = 2..14; dat = 12..14. `checkPipe good 2 2 15 2 = true`
  (kernel `decide`; most races at zero slack). `good_fifo` = `end_to_end` on it.
  `good_delivers`: an ASAP run with delays inside the intervals satisfies every
  hypothesis and the sink's first close (tick 59) carries the source's 1.
- `bad` = `good` without the SDELAY line (req 2 = wire 2..3, pin 1..2, i.e.
  `bd_pipe` with SDELAY = 0). `bad_rejects : ∀ m h, checkPipe bad 2 2 m h = false`
  (Sep needs m ≤ 4, the stage-1 latch setup needs m ≥ 15).
  `bad_counterexample`: the run `cex` (delays: req1 13, req2 3, req3 11, ack 2,
  en 14/2, dat 12/14, all inside `bad`'s intervals; ASAP firing) satisfies
  `PipeRun` and `Realizes bad`, and its sink's token 0 (close at tick 47) is 0
  while the source's token 0 is 1, so the FIFO conclusion is false. Mechanism:
  stage 1 closes (node at 35, enable pin at 38) before stage 0's latch output
  (1 at tick 30) has crossed the 14-tick data wire (tick 44): the "closing wave
  outruns the data wave" failure LIBRARY.md reports for tb_link.
  The rejection is not proved to be exact in general; on this route it is.
- Finding while building the counterexample: with a single global m, the
  source-setup race forces the input request path to be as slow as the slowest
  data wire in the pipe, and that slack can hide a Sep violation in 2 stages.
  The counterexample needed a slow stage-0 enable branch (14) against a fast
  stage-1 one (2), i.e. enable fan-out skew, to show a corruption. Real pipes
  accumulate the gain over stages (LIBRARY.md: 441 ps over 4).

## Fidelity of every primitive model used

- **Time:** ℕ ticks (1 ps in the library, 10 ps in the toy). Edges are atomic.
- **Wires / pips / delay elements (H_FIXED_DELAY, H_ROUTE):** an exact shift by
  the sum of per-arc delays, each inside the routed interval, fixed for the
  run. Faithful at one PVT corner if intervals come from prjxray-db fast/slow
  min/max (10b: the SDF nextpnr writes is a single slow-max number and misses
  site-pin delays; feed prjxray intervals, not the SDF). Not modelled:
  per-event jitter, glitches, data-dependent delay, RC loading.
  Test: GLS at both corners with SDF min/max; compare event times to the
  shift sums.
- **Delay lines:** only symmetric lines are shifts. `bd_delay` with
  FASTFALL/FASTRISE and N ≥ 2 (DACK ≥ 2 is FASTRISE) is an OR/AND of shifts
  with different rise and fall delays: not covered. N ≤ 1 is a plain buffer
  and is covered; bd_pipe's defaults (SDELAY = 1, DACK = 0) are covered.
  Extending: replace `shift` by a monotone channel with rise delay dr and fall
  delay df; the count invariant should survive because in protocol runs no
  pulse is shorter than a round trip (~0.5 day).
- **C-element (H_CEL):** the real `bd_c2n` INIT through `lutB`, on the pins,
  as an SI gate (keeps its value or takes the function value, at least one
  tick). Holds for every gate delay. The LUT's internal feedback loop and
  runts are abstracted (shard B's `CElemTiming` gives the conditions).
- **Latch (H_LATCH_CELL):** the real `bd_latch` INIT (`B8`, and the LUT6_2
  pair) on the pins, one tick of cell delay, deterministic (it follows D when
  the enable pin is high). The cell's own G→Q and D→Q delays are folded into
  `dG`/`dD` (per-pin LUT delay, prjxray's model). The feedback-loop
  conditions of the LUT latch (shard B's `holds_value_bin`, loop delay L) are
  NOT re-proved; this is a stronger cell model than B's, and the bridge to B's
  K3 latch is still open.
- **Source / sink (H_SRC, H_SNK, H_SRC_DATA):** pin-level four-phase parties;
  the source changes its data only on the tick of its request rise (data and
  request launched together; a source that sets data earlier only gains).
- **Bus:** W independent bit traces, `enc` to 8a's `Nat` value.

## What it buys the project

- A single machine-checked statement of what "a routed bd_pipe is correct"
  means and needs: seven race checks per link/bit on the routed arc intervals,
  plus named cell and environment hypotheses. Each check is the verified 10a
  checker on a real arc list, so a PASS is a theorem about every delay
  assignment in the intervals, and the FIFO property follows with no further
  argument.
- It shows which project rules are the obligations: rule I = Sep (SDELAY),
  rule H = Hold (DACK) plus the enable-vs-data race; it adds one the rules do
  not have (latch open width vs enable fan-out).
- It removes two of 8a's idealisations for the controller (zero wire delay,
  isochronic fork) by proof, for fixed delays.

## Effort to finish

- Per-link margins (`muller_pipeline` with `m_j`, `h_j`): ~2 h, removes the
  global-m conservatism.
- Asymmetric delay lines (DACK ≥ 2, FASTFALL request lines): ~0.5 day.
- Per-event BoundedDelay (glitches) in the multi-token run: needs a
  pulse-width side condition; ~1-2 days, and should be checked against the
  inertial channel work (shard A) first.
- Feeding real arc intervals: route paths from nextpnr's FASTM/SDF with
  prjxray-db intervals into `Route` (Python exporter) and `decide` the check;
  10a's note on kernel cost applies (fine for tens of arcs per race; each race
  here is a separate small netlist, so it scales linearly in links × bits).
- Bridge to shard B's per-bit K3 latch contract: 0.5-1 day.
