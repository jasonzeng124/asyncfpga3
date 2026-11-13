**Best gated xorshift: board item 18, 18.69 ns per iteration (8-route mean; 17.37-20.53); gap to 15 ns: 3.7 ns.**


# xorshift at 15 ns per iteration, four-phase (PROGRAM.md FIRST, owner 2026-11-12)

Bench top, x0.5 sizes, the itercost stack (bits-decoded netlist, prjxray SDF, fid, delay chains 0.21, CARRY4/F7F8/FF
1, rest 0.288, no scatter), one 256-round vector run twice. nextpnr 9c732bc6303458df. Predictions are from the timed
event graph of the previous row's routes (`research/tools/eventgraph`), written in the journal before each build.

| lever (cumulative) | knob | predicted (s1 / s3 / s4 / s5) | measured (s1 / s3 / s4 / s5) | gate |
|---|---|---|---|---|
| item 14 (start) | p8 + BDC_MERGE_OUT_LINK + BDC_LINK_FASTFALL | | 29.14 / 29.54 / 32.42 / 28.46 (8 routes: mean 30.0) | 24/24 (item 14) |
| 1. latch on the merge fork's result branch | BDC_MERGE_RES_LINK=ucontrol_merge0 | 21.85 / 21.87 / 23.10 / 23.57 | 23.37 / 23.40 / 24.12 / 23.43 | not run |
| 2. ring floor counts those latches (counter-ring pipe 3 -> 1) | BDC_RING_COUNT_OLINKS=1 | ~21.7 / ~21.7 (by hand) | 22.95 / 21.99 / 20.01 / 21.97 | not run |
| 3. latch on the rounds fork's steer branch | BDC_FORK_OUT_LINK=n11__0 | 21.21 / 20.60 (from lever 2's graphs) | 19.86 / 20.64 / 20.91 / 21.36 (s6-9: 19.58 / 21.36 / 20.39 / 20.70; 8-route mean 20.60) | **24/24 -> board item 17** |
| 4. placement (on lever 3) | BD_RLOC=v4 / BD_PLACE_WEIGHT=8 / BD_RLOC=v8 | 17.5-18.5 if adjacent (wire budget) | v4 20.55 / 18.75; PW8 20.89 / 19.72 (s1 / s3); v8 does not place | mixed by seed, not adopted |
| 5. drop the rule-1 link between i+1 and the compare (on lever 3) | BDC_NO_LINK=ulink_n30__1 | ~17.9 / ~18.6 (by hand) | 18.45 / 17.64 / 18.71 / 20.15 (s6-9: 18.72 / 17.37 / 17.95 / 20.53; 8-route mean 18.69) | **24/24 -> board item 18** |
| 5b. also drop ulink_n7 | BDC_NO_LINK=ulink_n30__1,ulink_n7 | ~17.5 | 21.96 (s1): ring_depths deepens ulink_n_trueResult_6, which lands on the cycle | rejected |
| 6. the compare computes i+1 < rounds from i (dup_add.py: a duplicate add fused into it; on lever 3, without 5) | MLIR pre-pass; UCMPI1 = 9 + 6 elements (upper bound) | ~16.2 / ~17.0 (by hand) | 20.86 / 20.35 | rejected: the static worst path needs >= the safe size (below) |

The three knobs are new in `bdc/emit.py`, opt-in; with them unset the emitted Verilog is byte-identical on gcd, xorshift,
collatz, collatz64, ipow and isprime. simcheck PASS with all of them on xorshift.

## Where it stands after lever 5 (8 routes, mean 18.69 ns; best 17.37)

- Seeds 1 and 3 (18.45 / 17.64): no polarity change left; the cycle is umux0 -> adder (i+1) -> compare -> steer -> merge ->
  merge-output link -> select link -> umux0, all rising: add 2.75 + compare 4.71 ns (their delays at or just under what
  the data's worst settle needs), merge 2.82, merge-output link 2.13, select link 2.77, the rest ~2.
- Seeds 5 and 9 (20.15 / 20.53): a new coupling, fork ufork8 (the adder's output) -> ulink_n7, because with the rule-1
  link gone the compare branch of that fork has no storage, so the fork's acknowledge waits for the compare and the
  steer. A latch back on that branch with no request delay (graph): -1.0 ns on seed 9, +0.2 on 5, +0.6 on 1, -0.1 on 3.
  Not a lever.
- So 15 ns needs ~3.5 ns more out of the rising pass, which the knobs here do not reach: the add and compare in series
  (7.5 ns of the cycle, sized to their worst settle under GUARD_LO), and ~5 ns of handshake through the merge, its
  output link and the select link. The levers left are cell-level (PROGRAM's list): a compare fused with the add, or a
  delay made of the adder's own carry chain so it tracks instead of covering with margin; and fewer handshake stages
  between the merge and umux0.

## Lever 6, rejected on static sizing

The fused add+compare settles in 2.2-2.6 ns in the run (i is small, so carries do not travel), but a matched delay must
cover the static worst path: tighten.py's rule A on dup seed 1's route puts the fused region's latest output at 7.55 ns
and asks for 17 elements -- more than the 15 (sum of the two) the build used. So under the rules there is nothing to
shrink, and the fused compare is slower than add -> link -> compare was. A data-dependent delay (completion detection on
the carry chain) would be the way to cash the 2.2-2.6 ns, which is a new cell, not a size.

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

## Step 5 of PROGRAM: the other kernels

The event-graph search with the new knobs (`search.py --new-knobs`) picks lever 1 alone on each; each gated 24/24 on 8
bench routes (BOARD-QUEUE items 19-21):

| kernel | before (board item) | + BDC_MERGE_RES_LINK (8-route mean) | gain | Dynamatic |
|---|---:|---:|---:|---:|
| xorshift | 30.0 (14) | 18.69 with levers 1-3 + 5 (item 18) | 1.61x | 12.73 |
| collatz | 58.49 (15) | 48.86 (item 20) | 1.20x | 14.05 |
| ipow | ~45.8 (13) | 39.14 (item 19) | 1.17x | - |
| collatz64 | 56.46 (16) | 47.64 (item 21) | 1.19x | 17.84 |
