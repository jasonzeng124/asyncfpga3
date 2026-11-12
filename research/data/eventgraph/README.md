# Where storage goes, computed (PROGRAM.md FIRST item, owner 2026-11-10)

The timed event graph of the control network, built from one full-stack run, reproduces every measured period and
critical cycle exactly; edited instead of the design, it predicts the second-latch variants already built to within
the seed scatter, and its search proposed one new build that measured as predicted. Numbers below are simulation
(the itercost stack), not silicon.

## Stack and tools (`research/tools/eventgraph/`)

- `fullstack_dump.sh`: the itercost stack (`../itercost/README.md`): netlist decoded from the `.bit`, prjxray SDF,
  `GLS_MODEL=fid`, bands delay chains 0.21 / CARRY4-F7F8-FF 1 / rest 0.288, no scatter; one long vector run twice
  (`ps7_bench.v`, +FCLK_PS=12000), every top-level net dumped. Replaces the 11-08 dump top, which was never committed.
- `eventgraph.py`: one node per (net, edge) of every net that is periodic in steady state (data and harness-clocked nets
  are not); one arc per ENABLING input of each edge: the LUT INIT (or F7/F8) evaluated on the delayed pin values, a pin
  is enabling if restoring its previous value would keep the old output. Weight = routed wire + arc, token offset from
  the trace, slack >= 0. Every edge on every run was AND-type (no OR-causality edge occurred).
  Period = maximum cycle ratio (`maxplus.py`, the max-plus recursion run to its periodic regime, cycle read back).
- `whatif.py`: edits on the graph. `stage:REQ:ACK:SD:DACK` / `depth:LINK:SD:DACK` (one bd_link stage on a channel;
  channels found from the kernel Verilog, fork pass-through and DELAY/DACK-0 aliases resolved); `fastfall:INST`;
  `nofall`; `deco:CELL` (a link stage replaced by `cells/verify/attempts/bd_deco_attempt.v`'s controller). Added
  weights come from the same graph: a chain element is the median measured element (rise / fall), a C-element input
  is the arc it replaces. Nothing is fitted. `report`: period, floor, two-phase bound, next cycles.
- `search.py`: greedy over the edits bdc can already build (BDC_LINK_DEPTHS +1 on any link, BDC_MERGE_OUT_LINK on any
  arbitrated merge, BDC_LINK_FASTFALL), stop under 300 ps gain; prints the knobs. `protocol.py`: the step-6 table.
- `storage_pass.sh` (step 5): build -> run -> graph -> search -> rebuild with the knobs -> measure. A driver around
  bdc; no bdc default changes.
- `predict_variants.sh`: the step-3 edit list (fixed in commit b3eaf9cd before any prediction was computed).
- `graphs/<run>/`: every run's nodes, arcs, check, kernel Verilog, provenance and BENCHRES.

Toolchain: nextpnr 9c732bc6303458df (patches 789a7120c912d393), toolchain.sh PASS. Routes rebuilt from the recipes in
BOARD-QUEUE; the rebuilt sdf md5s equal the recorded ones (x0.5 s1 c5b8ca02, T3 e3024283, collatz cs 1ab39716,
T3 6134880a) and every rebuilt period equals the recorded one.

## Step 1: the graph reproduces every run exactly

All 26 runs of `../itercost/` and `../itercost/second_latch/` rebuilt (x0.5 base 1-4, T3, collatz cs and T3, p8 1-4,
all3 1-4, p11, p12, mo 1-4, p8mo 1-4): graph period == measured period to the ps, critical cycle == trace.py's
back-walk == the committed `cycle_hops.tsv`, edge for edge. The same holds on every other run of this session
(ipow 1-4, collatz cd / cd+merge link 1-4, the step-4 builds, p12 2-4, x0.5 seed 5). x0.5 seed 1: 230 nodes, 325 arcs.

## Step 2: floors and next cycles (no builds)

| kernel (bench route) | measured period | floor: worst cycle with no polarity change | every falling arc 0 | storage only (search) |
|---|---:|---:|---:|---:|
| xorshift x0.5, seeds 1-5 | 39.06 / 38.88 / 40.59 / 39.43 / 41.18 | 19.99 / 19.75 / 19.24 / 20.66 / 20.15 | 21.9 / 21.6 / 22.7 / 22.4 | 31.7 / 32.5 / 31.6 / 32.7 |
| xorshift T3, seed 1 | 57.03 | 30.09 | 33.1 | 44.8 |
| ipow x0.75, seeds 1-4 | 55.50 / 51.84 / 54.27 / 54.23 | 37.26 / 35.27 / 37.25 / 36.68 | 37.9 / 41.9 / 38.7 / 40.6 | 52.4 / 49.7 / 50.5 / 50.3 |
| collatz BDC_CONST_DATA (T3cd), seeds 1-4 | 60.16 / 60.75 / 60.34 / 60.90 | 41.81 / 41.39 / 42.00 / 42.30 | 43.0 (s1) | 57.9 (s1) |
| collatz per-cell cs / T3, seed 1 | 67.82 / 77.56 | 49.35 / 56.31 | 51.1 / 57.3 | 64.7 / 72.1 |

- The floor is the rising pass of the loop's own ring: on xorshift the loop counter (umux0 -> uaddi0 -> ucmpi1 ->
  steer -> merge), on collatz and ipow the datapath ring (collatz: uaddi0 -> uselect0 -> ucmpi2 -> merge -> umux0;
  ipow: umux1 -> ushrsi0 -> ucmpi2 -> merge). It is 49-51% of today's period on xorshift and 67-70% on ipow and collatz.
- **Added storage is far from spent on xorshift, nearly spent on collatz and ipow.** Storage alone (the search)
  reaches 1.23x on xorshift x0.5 but only 1.04-1.06x on collatz and ipow: there the polarity changes are at the
  merge only, and what is left between today and the floor is the rising pass's own delays.
- Next cycles (x0.5 s1, `whatif.py report`): without the umux1 select ring (umux1's coupling) the counter ring binds
  at 33.0 ns (slack 6.1); without ulink_n8 a variant of the same ring at 35.9; without the merge/steer stages a
  third ring (umux2 -> ulink_n11__1 -> ucmpi1 -> ucond_br8) at 24.1. On collatz cs, the next cycle without ulink_n10__1
  is a parallel route of the same ring (slack 0.15 ns); structurally different cycles are 14-20 ns below.

## Step 3: predicting what was built, from the base graph alone

Edits fixed before any prediction (b3eaf9cd). NOT blind: the measured values were already in
`second_latch/README.md`. Per seed in `step3_predictions.tsv`.

| variant | predicted mean | measured mean | error mean | per-seed error |
|---|---:|---:|---:|---|
| p8 (ulink_n_trueResult_8 = 2) | 33.56 | 33.91 | -0.35 | -1.12 .. +0.86 |
| all3 | 34.72 | 34.68 | +0.04 | -1.22 .. +0.85 |
| mo (merge-output link) | 38.08 | 38.08 | -0.00 | -1.23 .. +0.95 |
| p8mo | 32.14 | 31.78 | +0.36 | -0.79 .. +1.38 |
| p11 (seed 1) | 39.06 | 39.87 | -0.81 | |
| p12 (seed 1) | 39.06 | 44.33 | **-5.27** | see below |
| collatz cd + merge link, seeds 1-4 | 58.10 | 58.73 | -0.63 | -3.00 .. +1.46 |

- The predicted cycles move where the measured ones did: p8, all3, p8mo to the loop-counter ring, still changing
  polarity at the merge (p8, all3) or at the merge-output link's fork (p8mo).
- **p12 is a miss of one route, not of structure.** Its measured cycle (`second_latch/p12_1/stages.tsv`) is the base
  cycle, the same 13 stages and 86 hops, with every stage longer in wire (ulink_n12__1 11.26 vs 9.17 ns, umux1 5.77 vs
  4.48, merge 4.97 vs 3.99): the added stage is off the cycle, as predicted, and the re-placement lengthened the ring.
  p12 seeds 2-4 were built to test that: see the journal (2026-11-12).
- Criterion "within the seed scatter (~1 ns)": met by every mean except p12 seed 1; single seeds miss by up to 1.4 ns
  (xorshift) and 3.0 ns (collatz seed 4, whose measured period is above its own base). A graph of one route cannot
  know another route's wires; that is the residual.

## Step 4: search, then build only the winners

| kernel | knobs chosen (same on every seed) | predicted (per seed) | measured (per seed) | over the base, measured |
|---|---|---|---|---|
| xorshift x0.5 | BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 | 29.07 / 29.29 / 30.13 / 30.11 (s1/3/4/5) | 29.14 / 29.54 / 32.42 / 28.46 | 1.340 / 1.374 / 1.216 / 1.447, mean 1.34 (predicted 1.34) |
| ipow x0.75 | BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 | 46.09 / 44.92 / 45.06 / 44.08 | 46.84 / 45.02 / 46.04 / 45.24 | 1.185 / 1.152 / 1.179 / 1.199, mean 1.18 (predicted 1.20) |
| collatz cd | BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 | 53.03 / 53.93 / 53.50 / 53.71 | (journal) | |

- xorshift seed 2 is excluded: its bitstream leaves a constant-D harness flop unconfigured (no AFFMUX), the run returns
  X data. A known nextpnr gap (JOURNAL 2026-11-08 08:21, there a C5FF), now in an AFF slot;
  `research/tools/ffmux_scan.py` finds it from the FASM alone (1 of 35 FASMs this session).
- Every measured cycle is the predicted one (xorshift: the 11 counter-ring stages and the 2 polarity changes at the
  merge-output link's fork). The misses are wire on those stages.
- Over the best measured design before this (p8mo, board item 11), xorshift gains 1.07 / 1.10 / 0.97 (seeds 1/3/4):
  fast fall is what this adds, and on seed 4 the re-placement ate it.
- None of these has passed the full gate (8 routes x 3 corners, fasm_equiv): not board candidates yet.

## Step 6: the protocol table (graph only, no RTL), ns per iteration, seed 1

| | xorshift x0.5 | xorshift T3 | ipow x0.75 | collatz cd | collatz cs | Dynamatic |
|---|---:|---:|---:|---:|---:|---|
| today (measured) | 39.06 | 57.03 | 55.50 | 60.16 | 67.82 | xorshift 12.73, collatz 14.05 |
| storage as in step 4 | 31.72 | 44.81 | 52.35 | 57.85 | 64.66 | |
| + every delay chain falls fast | 29.07 | 38.82 | 46.09 | 53.03 | 61.04 | |
| deco controller at the coupling stages | 37.15 | 54.24 | 55.50 | 60.16 | 67.82 | |
| every falling arc 0 (two-phase bound) | 21.91 | 33.11 | 37.94 | 42.98 | 51.08 | |
| floor (no polarity change) | 19.99 | 30.09 | 37.26 | 41.81 | 49.35 | |

- **Two-phase is the largest lever on every kernel, and on collatz and ipow nearly the only one**: its bound is
  1.78x (xorshift) and 1.40-1.46x (collatz cd, ipow), against 1.13-1.34x for storage plus fast fall.
- **The decoupled controller (bd_deco_attempt) buys almost nothing** (1.05x on xorshift, 1.00x on collatz and ipow):
  its outgoing request rises only after the sender has dropped its request, so the sender's return-to-zero moves onto
  the forward path. At ulink_n11__1 (behind a fork whose branches rejoin at ucmpi1) the graph has a zero-token cycle:
  that design would deadlock.
- Even the two-phase bound stays 1.7-3x above Dynamatic's clocked period. What remains is the rising pass itself:
  matched delays and req/ack wires (itercost: wires are 85% of the period).

## Does NOT show

- Silicon; any PVT corner or scatter (the itercost bands only); the full gate for any new build.
- The graph is the steady state of one vector per kernel; a data-dependent branch (collatz parity) gives the same
  period on both arms here, which the trace showed (identical periods), but other kernels may not.
- Predictions hold to the route the graph came from; across re-placement the error is the seed scatter (and one
  5.3 ns outlier, p12 seed 1).
- The deco and two-phase rows are graph edits, not designs; the deco equations are the attempt file's, unverified.
