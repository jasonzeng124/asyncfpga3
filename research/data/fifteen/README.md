**Best gated xorshift: board item 14, 30.0 ns per iteration (8 routes); gap to 15 ns: 15.0 ns. Best measured (not yet
gated): levers 1-3 + 5, 18.45 / 17.64 ns (seeds 1, 3).**

# xorshift at 15 ns per iteration, four-phase (PROGRAM.md FIRST, owner 2026-11-12)

Bench top, x0.5 sizes, the itercost stack (bits-decoded netlist, prjxray SDF, fid, delay chains 0.21, CARRY4/F7F8/FF
1, rest 0.288, no scatter), one 256-round vector run twice. nextpnr 9c732bc6303458df. Predictions are from the timed
event graph of the previous row's routes (`research/tools/eventgraph`), written in the journal before each build.

| lever (cumulative) | knob | predicted (s1 / s3 / s4 / s5) | measured (s1 / s3 / s4 / s5) | gate |
|---|---|---|---|---|
| item 14 (start) | p8 + BDC_MERGE_OUT_LINK + BDC_LINK_FASTFALL | | 29.14 / 29.54 / 32.42 / 28.46 (8 routes: mean 30.0) | 24/24 (item 14) |
| 1. latch on the merge fork's result branch | BDC_MERGE_RES_LINK=ucontrol_merge0 | 21.85 / 21.87 / 23.10 / 23.57 | 23.37 / 23.40 / 24.12 / 23.43 | not run |
| 2. ring floor counts those latches (counter-ring pipe 3 -> 1) | BDC_RING_COUNT_OLINKS=1 | ~21.7 / ~21.7 (by hand) | 22.95 / 21.99 / 20.01 / 21.97 | not run |
| 3. latch on the rounds fork's steer branch | BDC_FORK_OUT_LINK=n11__0 | 21.21 / 20.60 (from lever 2's graphs) | 19.86 / 20.64 / 20.91 / 21.36 (s6-9: 19.58 / 21.36 / 20.39 / 20.70; 8-route mean 20.55) | running (8 routes) |
| 4. placement (on lever 3) | BD_RLOC=v4 / BD_PLACE_WEIGHT=8 / BD_RLOC=v8 | 17.5-18.5 if adjacent (wire budget) | v4 20.55 / 18.75; PW8 20.89 / 19.72 (s1 / s3); v8 does not place | mixed by seed, not adopted |
| 5. drop the rule-1 link between i+1 and the compare (on lever 3) | BDC_NO_LINK=ulink_n30__1 | ~17.9 / ~18.6 (by hand) | 18.45 / 17.64 / 18.71 / 20.15 (s6-8: 18.72 / 17.37 / 17.95) | running (8 routes) |
| 5b. also drop ulink_n7 | BDC_NO_LINK=ulink_n30__1,ulink_n7 | ~17.5 | 21.96 (s1): ring_depths deepens ulink_n_trueResult_6, which lands on the cycle | rejected |

The three knobs are new in `bdc/emit.py`, opt-in; with them unset the emitted Verilog is byte-identical on gcd, xorshift,
collatz, collatz64, ipow and isprime. simcheck PASS with all of them on xorshift.

## Step 1: the budget (item 14's routes, `budget_pmf_*.txt`, `research/tools/fifteen/budget.py`)

| route | period | RTZ on the cycle | delay removable (rules) | handshake wire removable | all three taken |
|---|---:|---:|---:|---:|---:|
| s1 | 29.14 | 10.28 | 2.01 (1.36 select) | 1.98 | 17.56 |
| s3 | 29.54 | 10.71 | 2.34 | 2.28 | 16.71 |
| s4 | 32.42 | 12.66 | 2.00 | 3.20 | 17.48 |
| s5 | 28.46 | 9.90 | 2.05 | 1.93 | 17.06 |
| s6-s9 | 29.1-31.1 | 10.6-11.7 | 1.4-2.5 | 2.2-3.0 | 17.2-17.7 |

- Delay "removable" = on-cycle time minus (worst settle of the bundled data over the whole run / GUARD_LO 0.772); the
  select rule keeps most of it. Wire "removable" = routed wire minus the graph's 10th-percentile wire (adjacent cells).
- All three taken leaves 16.7-17.7 ns: not under 15. What remains is the counter ring's own rising logic (i+1: its
  worst settle over the run, 3.8 ns, is above its on-cycle delay, 2.85 ns -- open question, see the journal; the
  compare needs 3.1 ns) and the handshake hops between its 11 stages.

## Why levers 1 and 3 work

Both rings that bind after item 14 close through a FORK whose acknowledge waits for all its consumers, one of which is
a loop steer's join that waits for the loop compare. So a token's return-to-zero (the select of umux0, the rounds value
of umux2) rides the whole counter computation. One latch on that fork output lets the fork complete at once. The graph
found both; the search over existing knobs could not, because bdc had no knob for a fork output.

## Does NOT show

- The gate for levers 1-3 (lever 3's is running); silicon; corners or scatter (itercost bands only).
- Seeds 4/5 of lever 3 (running).
