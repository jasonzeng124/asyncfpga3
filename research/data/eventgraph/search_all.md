# The storage search over every site, and what bounds the loops it cannot help (subagent graphsearch, 2026-11-18)

PROGRAM "General first" item 1 and idea 6b: "latch placement took xorshift from 30 to 20.6 ns. On collatz, ipow and
collatz64 the search found nothing with the knobs it had. What would a search over all sites find?" Numbers are the
itercost simulation stack (prjxray SDF, fid, bands 0.21 / 1 / 0.288), not silicon. Every routed number: nextpnr
6e5d224472232d5d. Predictions were written in the subagent's PREDICTION.txt before each build (copied at the end).

**Answer.** With every handshake channel a candidate, the search finds one new kind of storage site that pays and that bdc
already builds, **a latch on one fork output** (`BDC_FORK_OUT_LINK`) where rule F does not put one, and it explains why
collatz, ipow and collatz64 get little from storage: their loops are coupled through a **source shared by several
literals**, which no storage site reaches well; a new opt-in bdc rewrite, **`BDC_SPLIT_SOURCES=1`** (one source per
literal, so the literal is folded), removes that coupling.

| kernel | change (on BDC_AUTO=1 flow v6 routes, the farm's own sizes and seeds) | routes | P before -> after, mean (ns) | per route | draws |
|---|---|---|---|---|---|
| xorshift | latch on the loop test's fork into the x steer's condition (`n32__2`, 1 bit) | 4 (s2 s3 s4 s8) | 21.14 -> 16.94 (-4.20, -19.9 %; 4 of 4 faster) | s2 19.71 -> 17.90, s3 22.46 -> 16.32, s4 19.43 -> 15.47, s8 22.96 -> 18.08 | 6 / 6 pass |
| countloop | latch on the loop test's fork into the s steer's condition (`n24__3`, 1 bit) | 4 (s1-s4) | 24.71 -> 20.83 (-3.88, -15.7 %; 4 of 4 faster) | s1 26.60 -> 21.40, s2 22.15 -> 20.83, s3 25.80 -> 21.78, s4 24.30 -> 19.32 | 4 / 4 pass |
| collatz | BDC_SPLIT_SOURCES | 4 (s2 s3 s4 s6) | 17.64 -> 16.30 (-1.34, -7.6 %; 3 of 4 faster) | s2 14.96 -> 15.54, s3 19.46 -> 16.67, s4 17.11 -> 15.19, s6 19.03 -> 17.81 | 5 / 5 pass |
| ipow | BDC_SPLIT_SOURCES | 4 (s1 s2 s3 s4) | 22.21 -> 20.36 (-1.86, -8.4 %; 4 of 4 faster) | s1 21.73 -> 20.49, s2 21.20 -> 19.61, s3 23.36 -> 18.97, s4 22.57 -> 22.37 | 5 / 5 pass |
| collatz64 | BDC_SPLIT_SOURCES | 3 (s4 s7 s8) | 24.27 -> 22.74 (-1.54, -6.3 %; 2 of 3 faster) | s4 22.13 -> 19.81, s7 26.12 -> 23.80, s8 24.57 -> 24.60 | 3 / 3 pass |

The depth-only search (subagent xorgap's `AUTO_SEARCH` phase) finds p8 on xorshift (the same coupling, cut with a 32-bit
second stage instead of a 1-bit latch: p8 alone at v6's sizes, xorgap, s2 / s3 / s4 18.23 / 18.87 / 15.84 against 17.90 /
16.32 / 15.47 here) and nothing on countloop, collatz, ipow, collatz64. The farm's flow-v6 medians these routes come from:
xorshift 22.28, countloop 25.05, collatz 17.04, ipow 21.58, collatz64 23.27 ns per iteration.

## 1. The search over every site (`search.py --all-sites`)

`search.py GRAPH SIZES --all-sites [--buildable-only] [--wire PS] [--sd N --dack N] [--top N]`:

- **Candidates.** A bd_link stage on every *bare* handshake channel of the kernel module (whatif.py `G.channels()`: each
  `X_req` / `X_ack` pair with one producer and a reader, not already behind a link), and +1 depth on every channel link (a
  stage on its input channel, where bd_pipe adds it; this covers bd_pipe links, which the depth-only search cannot model).
  A new link gets `--sd` / `--dack` chain elements (default 1 / 1: what flow v6's sizing gave rule F's fork-output link)
  and a fast acknowledge rise; a new pipe stage the pipe's SDELAY from SIZES (else `--sd`) and no acknowledge delay.
- **Sites and the knob that builds each.** fork output -> `BDC_FORK_OUT_LINK=<chan>`; merge output / result branch ->
  `BDC_MERGE_OUT_LINK` / `BDC_MERGE_RES_LINK`; link depth -> `BDC_LINK_DEPTHS`. **mux, steer and fused compute-cell
  outputs: no knob** (reported as `NEEDS-BDC:<site>`, never built; `--buildable-only` drops them).
- **Wires.** To put a stage between a channel's producer and consumer, the graph nodes of its request and acknowledge must
  be found through the netlist's wires: a fused cell's `e*_ack` is its `z_ack` (its bd_join's `ack_out`), a top-level
  bd_join's `ack_out` entries are its `ack`, a bd_mux's `ctl_ack` is its `z_ack` (rtl/bd_mux.v), a constant's / extui's
  request and acknowledge are `assign`s (`G.aliases()`). The acknowledge's readers are found toward the PRODUCER only
  (`up_ack`: through a fused producer to its own input links; never the consumer's sibling join inputs, which share the
  physical net). Before this, every channel into a join (a steer's data or condition, a fused cell's output) raised
  ValueError and was skipped silently. All of it is behind `G.use_aliases`, which only `--all-sites` sets: every other use
  of whatif.py is unchanged.
- **Wire charge.** The graph under-charges an inserted stage by 1-3 ns of wire (README step 5). `--wire PS` adds PS on
  every input arc of every inserted stage; search with `--wire 1000` in the flow (ipow below: a 4-stage pick that only
  paid at wire 0 measured between the wire-0 and the wire-1000 prediction).
- **ENV is complete.** `--all-sites` prints each knob with the links the route already has (rules F / M, read off
  kernel.v), because a knob in the environment REPLACES what `BDC_AUTO` chooses (bdc/emit.py `_auto_apply`). So the ENV line
  can be passed to a `BDC_AUTO=1` build as it is, which is what subagent xorgap's `AUTO_SEARCH` phase (auto_size.sh, after
  the loop, on the shipped route) does with `--depth-only`'s ENV. To let that phase pick the new sites: its search line
  with `--all-sites --buildable-only --wire 1000` (`out/optional_on_top_of_xorgap/0001-*.patch`: `AUTO_SEARCH_ARGS`,
  default unchanged; checked on xorgap's branch merged with this one: both modes run, no conflict).
- **Not at it 0.** The sizing loop's first route (xorshift seed 3 at the estimates x 0.3, `gs0_xorshift_3`, P 26.08) is at
  its rising floor (25.89): the search finds nothing there. It has to run on a sized route, as xorgap's phase does.

## 2. What bounds each kernel's cycle (graph only)

P = the route's period; R-floor = the worst cycle with no polarity change (the rising pass: no storage goes below it); RTZ
= P - R-floor (the most storage could take); "via" = what the critical cycle couples through. `v6x_*` are subagent xorgap's
byte-identical rebuilds of farm suite6, `su_xorshift_2_7` the bot's, `gs_*` mine (farm suite3a / suite6 sizes, same sdf
as the farm); the rest are older automatic routes (flow v3-v5). "Without the source" deletes every arc out of a shared
source's network (an upper bound on de-handshaking those literals, before the join inputs that would also go).

| graph | P | R-floor | RTZ | the critical cycle couples through | without the source |
|---|---:|---:|---:|---|---:|
| v6x_xorshift_1 / su_2_7 / v6x_3 / v6x_4 / v6x_8 | 19.80 / 19.72 / 22.47 / 19.43 / 22.96 | 17.16 / 17.69 / 17.61 / 14.87 / 18.18 | 2.6 / 2.0 / 4.9 / 4.6 / 4.8 | the loop test's fork9 into the x steer's condition | - |
| gs_countloop_2 / _4 | 22.15 / 24.30 | 20.41 / 19.45 | 1.7 / 4.8 | the loop test's fork9 into the s steer; a's fork5 | - |
| v6x_collatz_1 | 16.97 | 16.76 | 0.2 | (at its rising floor) | 16.97 |
| bqa_collatz_6 / su_collatz_1_4 / rpA_collatz_3 | 18.99 / 18.06 / 17.71 | 14.60 / 14.10 / 14.13 | 4.4 / 4.0 / 3.6 | **shared source2** (fork5: literals true and 1) | 17.17 / 16.03 / 17.23 |
| v6x_ipow_1 / bqa_ipow_2 / rj_ipow_4 | 21.73 / 22.71 / 21.61 | 16.39 / 18.05 / 17.32 | 5.3 / 4.7 / 4.3 | **shared source1 + source2** (fork7, fork8) | 19.36 / 19.78 / 19.32 |
| rpA_ipow_5 | 21.47 | 19.28 | 2.2 | the merge index fork into mux0's select | 21.47 |
| gs_collatz64_7 / bqa_collatz64_5 | 26.12 / 23.71 | 20.97 / 19.73 | 5.1 / 4.0 | **shared source3** (fork5) | 24.74 / 22.32 |
| rpA_collatz64_3 / su_collatz64_1_4 | 21.50 / 30.01 | 19.56 / 23.27 | 1.9 / 6.7 | the merge index fork into mux0's select | 21.50 / 30.01 |

**Why the depth-only search finds nothing on collatz, ipow, collatz64 and countloop.** On countloop the coupling is a fork
output into a steer: the fork's acknowledge waits for that steer, so only storage on the fork's output decouples it (depth
on the steer's output link does not). On collatz, ipow and collatz64 the coupling, on 8 of 12 routes, is a **source shared
by several literals**: Dynamatic fires every literal of a block from one `source` through a `fork` (collatz: `source2 ->
fork5 -> {true -> the parity andi, 1 -> fork6 -> shli, addi, addi1, shrsi, sinkeq2}`; ipow: `source1 -> {true -> andi, 1
-> shrsi}`, `source2 -> {false -> cmpi1, 0 -> the loop test cmpi2}`). bdc keeps those literals as handshake channels
(BDC_CONST_DATA makes their data a literal, the channel stays), and a fork cannot take the next token before every reader
has acknowledged, so readers in different places of the loop body wait for each other's return to zero. No link depth
reaches a fork's acknowledge. Where that does not bind, these routes are within 0.2-2.2 ns of their rising floor, or the
binding coupling is the merge's index fork into a mux select.

**Where a simple ring's time goes (the rising floor itself).** Split of the R-floor cycle: matched-delay chain elements
with their wiring; handshake hops between units; arcs inside units (C-elements, joins, the merge's arbiter, mux logic)
with their wire:

| graph | R-floor | matched-delay chains | hops between units | inside units | storage stages on it |
|---|---:|---:|---:|---:|---:|
| gs_countloop_2 / _4 | 20.41 / 19.45 | 10.00 / 8.52 (49 / 44 %) | 6.04 / 6.23 (30 / 32 %) | 4.37 / 4.70 (21 / 24 %) | 5 |
| su_xorshift_2_7 / v6x_3 / _4 / _8 | 17.69 / 17.61 / 14.87 / 18.18 | 46 / 45 / 38 / 47 % | 33 / 31 / 35 / 32 % | 21 / 23 / 27 / 21 % | 4 |
| v6x_collatz_1 | 16.76 | 7.80 (47 %) | 5.57 (33 %) | 3.39 (20 %) | 4 |
| v6x_ipow_1 | 16.39 | 9.73 (59 %) | 3.00 (18 %) | 3.66 (22 %) | 2 |
| bqa_collatz64_5 | 19.73 | 10.05 (51 %) | 5.07 (26 %) | 4.62 (23 %) | 3 |

Wire is 83-86 % of every floor (a chain element is ~62 ps of cell and ~400 ps of route). countloop's ring has 11 handshake
units (merge, its output link, the select link, mux0, a link, the incrementer, a link, the compare, the steer's join and
steer, the back-edge link): its matched delays alone (8.5-10 ns) are about Dynamatic's whole estimated cycle (8.36 ns),
and the handshake (hops and units) adds as much again. Storage only takes the RTZ part; the floor needs fewer units on the
ring (fusing mux / incrementer / compare / steer), shorter delays or shorter wires.

## 3. The search's picks, per graph (greedy; a step must gain 300 ps)

| graph | P | R-floor | wire 0 per inserted stage: steps -> predicted P | wire 1 ns per inserted stage |
|---|---:|---:|---|---|
| v6x_xorshift_1 | 19.80 | 17.16 | stage n32__2 (FORK_OUT_LINK n32__2) -> 17.30 | stage n32__2 (FORK_OUT_LINK n32__2) -> 17.30 |
| su_xorshift_2_7 | 19.71 | 17.69 | stage n31 (**no knob**: ucmpi1 output) -> 18.38 | stage n32__2 (FORK_OUT_LINK n32__2) -> 19.06 |
| v6x_xorshift_3 | 22.46 | 17.61 | stage n32__2 (FORK_OUT_LINK n32__2) -> 17.61 | stage n32__2 (FORK_OUT_LINK n32__2) -> 17.68 |
| v6x_xorshift_4 | 19.43 | 14.87 | stage n32__2 (FORK_OUT_LINK n32__2) -> 15.90; stage n32__3 (FORK_OUT_LINK n32__3) -> 15.36 | stage n32__2 (FORK_OUT_LINK n32__2) -> 15.90 |
| v6x_xorshift_8 | 22.96 | 18.18 | stage n32__2 (FORK_OUT_LINK n32__2) -> 18.57; depth ulink_n_trueResult_10=4 -> 18.18 | stage n32__2 (FORK_OUT_LINK n32__2) -> 18.57 |
| gs_countloop_2 | 22.15 | 20.41 | stage n12 (**no knob**: umux2 output) -> 20.41 | stage n12 (**no knob**: umux2 output) -> 20.41 |
| gs_countloop_4 | 24.30 | 19.45 | stage n24__3 (FORK_OUT_LINK n24__3) -> 19.79; stage n12 (**no knob**: umux2 output) -> 19.45 | stage n24__3 (FORK_OUT_LINK n24__3) -> 19.79; stage n12 (**no knob**: umux2 output) -> 19.45 |
| v6x_collatz_1 | 16.97 | 16.75 | nothing >= 0.3 ns | nothing >= 0.3 ns |
| v6x_ipow_1 | 21.73 | 16.39 | depth ulink_n_trueResult_10=3 -> 20.36; stage n22__1 (FORK_OUT_LINK n22__1) -> 19.21; stage n28 (**no knob**: uselect0 output) -> 18.55; stage n29 (**no knob**: umuli1 output) -> 18.17 | stage n14 (FORK_OUT_LINK n19__0) -> 21.28 |
| bqa_xorshift_8 | 20.11 | 15.86 | stage n32__2 (FORK_OUT_LINK n32__2) -> 15.86 | stage n32__2 (FORK_OUT_LINK n32__2) -> 15.86 |
| rj_xorshift_2 | 23.01 | 17.45 | stage n32__2 (FORK_OUT_LINK n32__2) -> 17.45 | stage n32__2 (FORK_OUT_LINK n32__2) -> 17.45 |
| rpA_xorshift_1 | 20.39 | 14.93 | stage n32__2 (FORK_OUT_LINK n32__2) -> 15.26 | stage n31 (**no knob**: ucmpi1 output) -> 16.75 |
| bqa_collatz_6 | 18.99 | 14.60 | stage n12 (FORK_OUT_LINK n17__0) -> 17.17; stage n9 (**no knob**: umux0 output) -> 16.27; stage n31__0 (FORK_OUT_LINK n31__0) -> 15.80 | stage n12 (FORK_OUT_LINK n17__0) -> 17.17 |
| su_collatz_1_4 | 18.06 | 14.10 | stage n12 (FORK_OUT_LINK n17__0) -> 16.02; stage n9 (**no knob**: umux0 output) -> 15.53 | stage n12 (FORK_OUT_LINK n17__0) -> 16.02 |
| rpA_collatz_3 | 17.71 | 14.13 | depth ulink_n_falseResult_9=3 -> 16.86 | stage n12 (FORK_OUT_LINK n17__0) -> 17.23; stage n30 (**no knob**: ucmpi2 output) -> 16.81 |
| au_collatz_1_1 | 19.53 | 18.68 | nothing >= 0.3 ns | nothing >= 0.3 ns |
| bqa_ipow_2 | 22.71 | 18.05 | stage n14 (FORK_OUT_LINK n19__0) -> 21.00; stage n33__2 (FORK_OUT_LINK n33__2) -> 20.41; depth ulink_n_trueResult_10=3 -> 19.90; depth ulink_n_trueResult_6=3 -> 19.37 | stage n14 (FORK_OUT_LINK n19__0) -> 21.00 |
| rj_ipow_4 | 21.61 | 17.32 | stage n14 (FORK_OUT_LINK n19__0) -> 19.84; depth ulink_n_trueResult_10=3 -> 19.27; depth ulink_n_trueResult_6=3 -> 18.76 | stage n22__1 (FORK_OUT_LINK n22__1) -> 21.10; stage n28 (**no knob**: uselect0 output) -> 20.58; stage n29 (**no knob**: umuli1 output) -> 19.52 |
| rpA_ipow_5 | 21.47 | 19.28 | depth ulink_n_trueResult_6=3 -> 21.02 | nothing >= 0.3 ns |
| bqa_collatz64_5 | 23.71 | 19.73 | depth ulink_n_falseResult_9=3 -> 21.74 | stage n12 (FORK_OUT_LINK n19__0) -> 22.32; stage n9 (**no knob**: umux0 output) -> 21.88 |
| rpA_collatz64_3 | 21.50 | 19.56 | depth ulink_n_falseResult_9=3 -> 21.03 | nothing >= 0.3 ns |
| su_collatz64_1_4 | 30.01 | 23.27 | depth ulink_n_falseResult_9=3 -> 29.41; stage n9 (**no knob**: umux0 output) -> 27.19; stage n12 (FORK_OUT_LINK n19__0) -> 25.27 | nothing >= 0.3 ns |

"stage nX" is a latch on channel nX (a fork output unless marked). xorshift's `n32__2` and countloop's `n24__3` are the loop
test's fork into the condition of the steer of the loop-carried value with the longest datapath (x; s); countloop's
`n13__0` is a's fork into its own steer; collatz's `n12` / `n17__0`, ipow's `n14` / `n19__0` and `n22__1`, collatz64's `n12`
/ `n19__0` are a shared source's fork into a literal. The "no knob" sites (the compare's output on xorshift, a mux output on
countloop / collatz, the select / multiply outputs on ipow) tie or trail a buildable site at 1 ns of wire: bdc support for
them is not urgent on these kernels.

## 4. A structural fix for the shared source: `BDC_SPLIT_SOURCES=1` (bdc/emit.py, opt-in)

Every source tree (a source, the forks of its token, the literals it fires, the forks of their values) with more than one
reader becomes one `source` + `constant` per reader, so each literal has exactly one reader and compute_fusion folds it into
its fused region like every unshared literal: no channel, no link, no join input. Only where it is the same function: every
reader must be a fusable op with another operand that is not a source's literal (it fires once per arrival of that operand;
an infinite stream of one value replaced by another infinite stream of the same value changes nothing it computes), or a
sink (dropped with its literal: a lone source -> sink pair would oscillate). A tree with any other reader is left alone.
Unset: byte-identical (emit.py --no-top on all 108 build/frontend kernels, default and BDC_AUTO=1: 90 identical, 0 differ,
126 fail to emit in both trees). It changes collatz (5 readers of source2; 66 -> 58 matched delays: uselect0's join 5 -> 3
inputs, uaddi0's 4 -> 2, four links gone), ipow (source1, source2: 2 readers each) and collatz64 (source3: 4 readers);
xorshift and countloop have no shared source (byte-identical). bdc/simcheck.py with BDC_AUTO=1 BDC_SPLIT_SOURCES=1 (its
Python references, the C semantics): collatz 8 / 8 vectors (n = 1 .. 703), ipow 8 / 8 and 17 / 17 (the C oracle on the gate
vectors, e up to 2^31 - 1), collatz64 3 / 3 (113383 leaves int32): PASS. Negative control: the split collatz DUT with
its folded `3n + 1` edited to `3n + 3` FAILS (vector 2 never terminates), so the check sees a wrong literal.
After the split no critical cycle of the 11 routes built passes a source; what binds next is the merge's index fork into
mux0's select and the loop test's fork into a steer (collatz s3: a latch on `n31__2`, -0.5 ns in the graph; collatz s6 /
collatz64 s7: a link on mux0's output, -1.4 / -1.6 ns, no knob), or the route is at its rising floor (collatz s2).

## 5. Builds: prediction against measurement

Each B / S route is the farm's A route (same flow v6 sizes, same `NEXTPNR_SEED`, `BDC_AUTO=1`) plus the change; a new
link's two lines at 1 / 1 element (flow v6's size for rule F's link), every other line untouched (the loop would re-size
them on the new route). The A routes rebuild byte-identical (countloop s2 / s4 here, xorshift s1 / s3 / s4 / s8, ipow s1,
collatz s1 by xorgap, collatz64 s7 here: the farm's sdf and P). Draws: bench_gate.sh draw:K, K = 10000 + 100 * seed + j
(the farm's own model points for that seed), every vector of the kernel's gate file, expected values from the C.

| route | kernel, seed | change (on BDC_AUTO=1, the farm's sizes) | A: farm P | predicted | measured P | dP | bits | draws |
|---|---|---|---:|---|---:|---:|---|---|
| gsB_xorshift_2 | xorshift s2 | FORK_OUT_LINK n32__2 | 19.71 | 19.06 | 17.90 | -1.82 | EQUIVALENT, ffmux-clean, sdf f359db46 | 1 / 1 |
| gsB_xorshift_3 | xorshift s3 | FORK_OUT_LINK n32__2 | 22.46 | 17.61 | 16.32 | -6.14 | EQUIVALENT, ffmux-clean, sdf 86f77f45 | 2 / 2 |
| gsB_xorshift_4 | xorshift s4 | FORK_OUT_LINK n32__2 | 19.43 | 15.90 | 15.47 | -3.96 | EQUIVALENT, ffmux-clean, sdf 423a1871 | 2 / 2 |
| gsB_xorshift_8 | xorshift s8 | FORK_OUT_LINK n32__2 | 22.96 | 18.57 | 18.08 | -4.88 | EQUIVALENT, ffmux-clean, sdf 4c84097f | 1 / 1 |
| gsB_countloop_1 | countloop s1 | FORK_OUT_LINK n24__3 | 26.60 | - (no A graph) | 21.40 | -5.20 | EQUIVALENT, ffmux-clean, sdf 37b29f66 | 1 / 1 |
| gsB_countloop_2 | countloop s2 | FORK_OUT_LINK n24__3 | 22.15 | 20.41 | 20.83 | -1.32 | EQUIVALENT, ffmux-clean, sdf 47426932 | 1 / 1 |
| gsB_countloop_3 | countloop s3 | FORK_OUT_LINK n24__3 | 25.80 | - (no A graph) | 21.78 | -4.01 | EQUIVALENT, ffmux-clean, sdf fa1753a7 | 1 / 1 |
| gsB_countloop_4 | countloop s4 | FORK_OUT_LINK n24__3 | 24.30 | 19.79 | 19.32 | -4.98 | EQUIVALENT, ffmux-clean, sdf 576b90a8 | 1 / 1 |
| gsB_ipow_1 | ipow s1 | 4 picks at wire 0: LINK_DEPTHS trueResult_10=3, n15=2; FORK_OUT_LINK n22__1, n19__0 | 21.73 | 18.34 (wire 0) / 22.08 (1 ns) | 20.23 | -1.50 | EQUIVALENT, ffmux-clean, sdf cd4661f2 | 1 / 1 |
| gsS_ipow_1 | ipow s1 | BDC_SPLIT_SOURCES | 21.73 | 19.0-20.5 (bound 19.36) | 20.49 | -1.23 | EQUIVALENT, ffmux-clean, sdf ccdc3184 | 2 / 2 |
| gsS_ipow_2 | ipow s2 | BDC_SPLIT_SOURCES | 21.20 | A-3 .. A+1 | 19.61 | -1.59 | EQUIVALENT, ffmux-clean (P: stride-2 trace), sdf fd46690a | 1 / 1 |
| gsS_ipow_3 | ipow s3 | BDC_SPLIT_SOURCES | 23.36 | A-3 .. A+1 | 18.97 | -4.39 | EQUIVALENT, ffmux-clean, sdf c28f035b | 1 / 1 |
| gsS_ipow_4 | ipow s4 | BDC_SPLIT_SOURCES | 22.57 | A-3 .. A+1 | 22.37 | -0.20 | EQUIVALENT, ffmux-clean, sdf a4f8bb35 | 1 / 1 |
| gsS_collatz_2 | collatz s2 | BDC_SPLIT_SOURCES | 14.96 | ~A (fastest route) | 15.54 | +0.57 | EQUIVALENT, ffmux-clean, sdf 9508036a | 1 / 1 |
| gsS_collatz_3 | collatz s3 | BDC_SPLIT_SOURCES | 19.46 | A-2.0 .. A | 16.67 | -2.80 | EQUIVALENT, ffmux-clean, sdf 8d390111 | 2 / 2 |
| gsS_collatz_4 | collatz s4 | BDC_SPLIT_SOURCES | 17.11 | A-3 .. A+1 | 15.19 | -1.92 | EQUIVALENT, ffmux-clean, sdf 87a34f5f | 1 / 1 |
| gsS_collatz_6 | collatz s6 | BDC_SPLIT_SOURCES | 19.03 | A-3 .. A+1 | 17.81 | -1.22 | EQUIVALENT, ffmux-clean, sdf 746ea82f | 1 / 1 |
| gsS_collatz64_4 | collatz64 s4 | BDC_SPLIT_SOURCES | 22.13 | A-3 .. A+1 | 19.81 | -2.31 | EQUIVALENT, ffmux-clean, sdf bb1f522d | 1 / 1 |
| gsS_collatz64_7 | collatz64 s7 | BDC_SPLIT_SOURCES | 26.12 | 24.0-25.0 (bound 24.74) | 23.80 | -2.32 | EQUIVALENT, ffmux-clean, sdf abb442f7 | 1 / 1 |
| gsS_collatz64_8 | collatz64 s8 | BDC_SPLIT_SOURCES | 24.57 | A-3 .. A+1 | 24.60 | +0.03 | EQUIVALENT, ffmux-clean, sdf 9bb66f2c | 1 / 1 |

- xorshift, FORK_OUT_LINK n32__2: n = 4, A mean 21.14 -> 16.94 (-4.20 ns, -19.9 %), every route faster; B range 15.47-18.08
- countloop, FORK_OUT_LINK n24__3: n = 4, A mean 24.71 -> 20.83 (-3.88 ns, -15.7 %), every route faster; B range 19.32-21.78
- ipow, BDC_SPLIT_SOURCES: n = 4, A mean 22.21 -> 20.36 (-1.85 ns, -8.3 %), every route faster; B range 18.97-22.37
- collatz, BDC_SPLIT_SOURCES: n = 4, A mean 17.64 -> 16.30 (-1.34 ns, -7.6 %), every route NOT all faster; B range 15.19-17.81
- collatz64, BDC_SPLIT_SOURCES: n = 3, A mean 24.27 -> 22.74 (-1.53 ns, -6.3 %), every route NOT all faster; B range 19.81-24.60

## 6. Does NOT show

- Silicon; the automatic flow with the change inside it. The B / S routes keep the A route's sizes; the flow would re-size
  every line on the new route (and the rule may lengthen the new link). Farm request `asearch2` (written for the bot, not
  filed) runs xorgap's phase with `AUTO_SEARCH_ARGS="--all-sites --buildable-only --wire 1000"`; BDC_SPLIT_SOURCES would go
  through the farm the same way (suite_one.sh with it set) before it could go into BDC_AUTO.
- 1-2 draws per route (the farm judged its A routes with 8); every judged route passed every draw.
- ipow s2's split P (19.61) comes from the full-stack trace (13 equal 2-iteration intervals of 39.23 ns): the event graph
  needs 16 and was not built; its B / S table row says so.
- collatz s2 got 0.58 ns slower with the split: the farm's fastest collatz route (14.97), whose cycle did not run through
  the source; the split route sits at its rising floor (the loop-control ring, longer wires after re-placement).
- The two changes were not built together (the split does nothing on xorshift / countloop: no shared source).
- A rule: n32__2 / n24__3 are the loop test's fork into the condition of the steer whose data has the longest path, which a
  rule could find without a route; I did not write one (the search finds them on every route it was run on).
