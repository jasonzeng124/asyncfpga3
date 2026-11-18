**THE AUTOMATIC COLUMN over every kernel judged so far (PROGRAM "General first" / "A benchmark suite for the compiler") --
one switch, nothing set per kernel: BDC_AUTO=1 with the flow's own sizing loop (research/tools/auto/auto_size.sh, flow
v6: start at emit.py's estimates x 0.3, the rule with C-element joins at the draw model's two worst vertices, join
credit, the steer self-bound, the token floor, a raise-only finish phase), judged by draws of the delay model. Farm
suite6 (the four original fast kernels, 8 seeds, 8 draws, nextpnr 6e5d224472232d5d) + suite3a / suite3b / suite8 (suite
kernels, seeds 1-4 / 1-2, 4 draws, same nextpnr) + suite7 (isprime, flow v5); 2026-11-18.** Every judged route returns
every right answer under every draw. Many suite kernels have fewer than 4 judged routes because their sizing loop hit
the farm's 240-minute task limit (60-80 min per iteration at 2 cores); suite9 (23 kernels x 4 seeds, resumable)
fills them in, and gcd / isprime wait for a faster rule step (subagent loopfast).

| kernel | status | routes judged / built | draws passing | ns per iteration (P), median (range) | worst latency per call, ns | kernel LUTs | Dynamatic, ns per iteration | ratio | hand recipe's best, ns |
|---|---|---|---|---|---|---|---|---|---|
| brhash | PASS | 4 / 4 | 16 / 16 | - | 8664 | 2110 | 36.40 (ESTIMATE) | - | - |
| collatz | PASS | 8 / 8 | 64 / 64 | 17.04 (14.96-19.46) | 5136 | 1214 | 14.05 (measured, 1 route) | 1.21 | 21.50 |
| collatz64 | PASS | 7 / 8 | 56 / 56 | 23.27 (22.03-26.12) | 9192 | 1767 | 17.84 (measured, 1 route) | 1.30 | 31.40 |
| countloop | PASS | 4 / 4 | 16 / 16 | 25.05 (22.15-26.60) | 6864 | 1772 | 8.36 (ESTIMATE) | 3.00 | - |
| dot2 | PASS | 1 / 1 | 4 / 4 | 156.00 (156.00-156.00) | 960 | 1434 | - | - | - |
| fold64 | PASS | 1 / 1 | 4 / 4 | - | 5868 | 2773 | 11.93 (ESTIMATE) | - | - |
| gather | PASS | 1 / 1 | 4 / 4 | 55.22 (55.22-55.22) | 1824 | 1523 | - | - | - |
| horner | PASS | 2 / 2 | 8 / 8 | 29.13 (28.03-30.22) | 7788 | 1737 | 41.81 (ESTIMATE) | 0.70 | - |
| ipow | PASS | 7 / 7 | 56 / 56 | 21.58 (19.84-23.36) | 780 | 1331 | 49.98 (ESTIMATE) | 0.43 | 36.20 |
| isprime | PASS | 1 / 2 | 4 / 4 | 363.19 (363.19-363.19) | 16116 | 3918 | 9.26 (ESTIMATE) | 39.22 | - |
| lfsrfind | PASS | 4 / 4 | 16 / 16 | 26.90 (23.18-29.27) | 7536 | 890 | 19.52 (ESTIMATE) | 1.38 | - |
| quadrec | BUILD-FAILED (it=5: TIMING FAILED: 81.74 MHz < 83 MHz target.) | 0 / 1 | - | - | - | - | 9.09 (ESTIMATE) | - | - |
| sqrtsub | PASS | 1 / 1 | 4 / 4 | 21.17 (21.17-21.17) | 5484 | 1394 | 8.36 (ESTIMATE) | 2.53 | - |
| straight | PASS | 4 / 4 | 16 / 16 | - | 72 | 1327 | - | - | - |
| test_bitint | PASS | 2 / 2 | 8 / 8 | - | 300 | 633 | 44.32 (ESTIMATE) | - | - |
| test_int16 | PASS | 4 / 4 | 16 / 16 | - | 60 | 3 | - | - | - |
| test_loop_free | PASS | 2 / 2 | 8 / 8 | - | 72 | 1005 | - | - | - |
| unused_arg | PASS | 4 / 4 | 16 / 16 | - | 72 | 86 | - | - | - |
| varshift | PASS | 1 / 2 | 4 / 4 | 39.06 (39.06-39.06) | 10056 | 2542 | 11.84 (ESTIMATE) | 3.30 | - |
| xorshift | PASS | 7 / 7 | 56 / 56 | 22.28 (19.43-23.46) | 6060 | 1365 | 12.73 (measured, 1 route) | 1.75 | 16.76 |

19 of 20 kernels pass (quadrec: the bench's PS-side clock missed 83 MHz on its one finished route, a build failure, not a
wrong answer); geometric mean of the ratio over the three MEASURED Dynamatic figures: 1.40; with the ESTIMATES (n = 10):
2.02 (countloop 3.00, sqrtsub 2.53, varshift 3.30: the simple counted loops are where the automatic flow is furthest
behind Dynamatic's estimate; isprime's 39 compares an outer-trial period with Dynamatic's inner-shift cycle: not a
ratio yet). Our ns are the simulation's (~8 % slower per iteration than the August board, research/SIM-VS-BOARD.md);
Dynamatic's measured figures are single nextpnr routes (Fmax x cycles), not board runs. Hand recipes: xorshift 16.76
(x55a10, 28 routes), collatz 21.5, collatz64 31.4, ipow 36.2. Flow v6 against v3 (suite4) on the same four kernels:
collatz 18.98 -> 17.04, collatz64 23.71 -> 23.27, ipow 24.10 -> 21.58, xorshift 20.11 -> 22.28 (subagent xorgap).
Board items from the automatic path: 38 (ipow), 39 (collatz), 40 (collatz64), 41 (xorshift), all flow v3.

Previous headline (flow v3, suite4, 27 routes, 216 / 216 draws): collatz 18.98, collatz64 23.71, ipow 24.10, xorshift
20.11 ns per iteration.

**2026-11-17, judged by draws (PROGRAM "The board decides"): xorshift 16.85 ns per iteration** -- item 33's sizes x0.55
except the incrementer (fr4a_x55a), median of 32 farm routes (15.93-18.19), every one of 128 delay-model draws returning
every right answer (bench_gate.sh draw:K; the model fails a known-bad build 16 / 16). Gap to 15 ns: 1.85 ns. The
simulation at band 0.288 runs ~8% slower per iteration than the board on the August builds (research/SIM-VS-BOARD.md), so
the board figure is probably nearer 15.5. The first size that fails draws is x0.40a (2 of 16 routes). Before it: item 33,
18.91 ns (static rules as gates).

**Best xorshift that passes the gate and every static check over the full input range except rule M's rows (shown
pessimistic in simulation on its board route): board item 33 (#34), item 27 + seed 2's own datapath proposal, 18.91 ns
per iteration (median of 31 farm routes, 17.97-20.86; latency -0.40 ns vs item 27, 22/30 faster). Gap to 15 ns: 3.9 ns.
(2026-11-16.)**

**Best xorshift that passes the gate, the static check and the hold check over the full input range: board item 27
(#28), lever 8 (the loop test reads i against n-1), 19.39 ns per iteration (median of 31 farm routes, 18.98-21.16;
the board seed is clean on every row, 11 of 31 routes carry small H / I rows, pad round fxd2 running). Gap to 15 ns:
4.4 ns.** Before it: item 23 (xf4) 23.49 ns; the bench's 12-bit range only: item 17, 20.60 ns. Collatz full range: item
25 (#26), 35.8 ns (item 22 41.2); collatz64 item 26 (#27), 36.2 ns (item 24 45.2): the same idea, exit test n == 2.

**2026-11-15 caveat: "the static check" above was rules A / A' / E only. Rule H (hold) and I (capture) rows were never
read, and on item 23's route they are below 0 (worst corner: H -274 ps on ulink_n7, the stage that corrupted xf2_1).
Item 23 is gate-clean, not statically hold-clean. Re-gating: sizes fr4 (hold_pads.py), farm fxf5 / fxs5 (JOURNAL).**


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
| 5. drop the rule-1 link between i+1 and the compare (on lever 3) | BDC_NO_LINK=ulink_n30__1 | ~17.9 / ~18.6 (by hand) | 18.45 / 17.64 / 18.71 / 20.15 (s6-9: 18.72 / 17.37 / 17.95 / 20.53; 8-route mean 18.69) | 24/24, but **ON HOLD**: static rule E -4.65 ns raw (see the top) |
| 5b. also drop ulink_n7 | BDC_NO_LINK=ulink_n30__1,ulink_n7 | ~17.5 | 21.96 (s1): ring_depths deepens ulink_n_trueResult_6, which lands on the cycle | rejected |
| 6. the compare computes i+1 < rounds from i (dup_add.py: a duplicate add fused into it; on lever 3, without 5) | MLIR pre-pass; UCMPI1 = 9 + 6 elements (upper bound) | ~16.2 / ~17.0 (by hand) | 20.86 / 20.35 | rejected: the static worst path needs >= the safe size (below) |
| R. full-range re-baseline of lever 3 (owner rule 2026-11-14) | xorshift_sizes_T3s50_fr_bench.vh (uaddi0 6 -> 13, uxori1/2, umux3 pads) | 22.04 / 22.61 / 22.99 / 23.50 (s1 / s3 / s4 / s5) | 22.52 / 23.58 / 23.34 / 22.82 (s6-9: 23.30 / 21.78 / 21.60 / 23.36; mean 22.79) | running; static check s1: only the merge1 index (exercised) |
| 7. drop umux0's select link (on lever 5) | BDC_NO_LINK=ulink_n30__1,ulink_n12__0 | ~16.4 / ~15.5 (by hand) | 19.41 / 20.42 (s1 / s3): the merge fork's select branch loses its storage, the fork re-couples to umux0 (polarity change at ucontrol_merge0_f -> its olink) | rejected |
| 8. the loop test reads i against n-1, computed once before the loop (pre_dec.py; on R / fr4, without levers 5-7) | MLIR pre-pass (MLIR_OVERRIDE), bdc unchanged | 19 (18-20) on s10 (from xf5_10's graph) | s10 19.15 (period-2: 18.92 / 19.38); 31 farm routes median 19.39 (18.98-21.16), latency -3.76 ns paired vs fxf5 (27/28) | **93/93 -> board item 27**; static A / A' / E 29/31, H / I rows on 11/31 (pads fxd2) |
| 9. select links sized by rule E (2026-11-16; on 8) | fr4s3: ulink_n12__0/1/2, ulink_n_index_15 5/8/6/5 -> 3 | -0.2 to -0.4 ns / iteration vs fxd | 32 routes median 19.45; latency -0.23 median paired vs fxd (16/31 faster) | 96/96; rejected (noise): the select lines are off xorshift's cycle |
| 10. ulink_n7f__1's ack (no sizes.vh macro, RTL default 6; on x27_2's critical fall) -> 1 (on 8) | fr4u | -0.5 to -1.0 | 32 routes median 19.21; latency -0.05 paired (16/31) | 96/96; rejected: the next cycle does not contain the line |
| 11. mux delays sized by rule M (the mux data outputs, never checked before; on 8) | fr4m: umux0/1/2 2 -> 5/7/3, umux3 14 -> 9 | +0.3 to +1.0 (the cost of the contract) | 27 routes median 20.55; +1.20 paired vs fxd (2/26 faster) | 81/81; not adopted: rule M is pessimistic on xorshift in simulation |
| 12. seed 2's own corner_audit proposal on datapath lines (on 8; the collatz item 31 method) | fr4a: uxori1 / uxori2 7 -> 5, umux3 14 -> 9, ucmpi0 12 -> 10, uaddi0 13 -> 12 | -0.3 to -0.6 | 31 routes median 18.91; -0.40 paired vs fxd (22/30) | **93/93 -> board item 33** (M rows: pessimism, mux_settle) |

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

After lever 1, collatz, ipow and collatz64 already run at their worst cycle with no polarity change: the search with
every storage knob finds nothing (seed 1 of each). What is left is each datapath's rising pass (seed 1, ns on the cycle):
collatz uselect0 10.0, uaddi0 8.4, ulink_n14__0 (select) 7.9, ucmpi2 7.8; ipow ushrsi0 10.4, ucmpi2 8.8, umux1 4.9;
collatz64 uaddi0 11.5, uselect0 9.2, ulink_n14__0 6.8, ucmpi2 5.9. Those are matched delays sized to static worst paths
(item 9/12/7 sizes), the select rule's links, and the compares -- sizing and cell work, not storage.

## 2026-11-14: where xorshift stands after lever 5's hold, and what 15 ns would need

- Lever 5 is ON HOLD (top of this file). Lever 9 builds on it and inherits the hold. Lever 10 (PLACE_WEIGHT on the
  binding rings' handshake nets only, `BD_PLACE_WEIGHT_CELLS`) is seed-sensitive: on lever 5, s1 19.70 / s3 17.83 (ring 1
  only), 17.79 / 18.61 (both rings), against 18.45 / 17.64. Not a lever. Lever 9c (rule H's uack size) 17.66 on s1 vs 9a
  17.76: not a lever.
- The binding cycle (lever 5 s1, graph): 18.45 ns = 15.82 ns of wire + 2.63 ns of cell arcs. Delay-chain hops (27
  elements) 10.68 ns, handshake hops (~19) 7.77 ns.
- The counter's add + compare is statically SHORT at the gate's own worst corner even at lever 3 (item 17): uaddi0 A'
  -752 ps (corner_audit asks 6 -> 11), and only 238 ps of rule E margin at ucond_br6 after ulink_n30__1. The gate never
  sees it because its vectors keep i < 1000 (the board bench masks rounds to 12 bits). So the x0.5 counter is not shown
  correct for a general 32-bit rounds, and a fully covered counter costs MORE time on the cycle than today
  (~5 elements of uaddi0, ~2 ns), not less.
- So 15 ns in four-phase needs, beyond what the knobs here reach: (1) the counter's add and compare bounded by their real
  settle instead of the static full carry -- completion detection on the carry chains, a new cell (the measured settle
  of the fused add+compare in the run is 2.2-2.6 ns against 7.5 ns of matched delay on the cycle); (2) ~3 ns less
  handshake wire, which placement weights did not give (levers 4, 10). Neither is available without new cells or a
  placer objective for ring period.
