# Fewer handshake units on each loop ring: the update and the test fused (subagent ringfuse, 2026-11-19)

PROGRAM "General first" idea 6c ("the rising pass: handshake stages on the counter ring, fused by a pass, for any
loop") and FIRST item 2 ("fewer handshake stages on the counter ring ... by fusing its mux, add, compare and steer").
Every routed number: nextpnr 6e5d224472232d5d (`cells/verify/toolchain.sh` all ok), flow v7 (auto_size.sh with the
search phase), BDC_AUTO=1 with no kernel list (BDC_AUTO_REWRITES=0), `suite_one.sh K S 4 4`, draws with GATE_RUNTS=1.
Simulation numbers (itercost stack, prjxray SDF), not silicon.

**HEADLINE (local, 1-3 routes per kernel: not yet a claim).** `BDC_RING_FUSE=2` -- the loop's update and test fused
into one cell with two results, and a link on its 1-bit test output -- through the whole automatic flow (flow v7, no
kernel list), against the same kernel and seed without it: **xorshift 18.79 / 18.08 / 19.61 ns on seeds 1-3 against
20.55 / 20.42 / 22.19 (-1.76 / -2.34 / -2.59 ns; latency per call -10 to -12 %); all three below the fastest of the
8 no-list baseline seeds (20.42)**; collatz 20.64 / 20.73 against 18.98 / 22.86 (+1.66 / -2.13); ipow 21.34 / 20.01
against 21.73 / 21.20 (-0.39 / -1.20; ipow's baseline is flow v6); countloop 19.58 / 22.68 / 24.30 against 20.92 /
21.37 / 20.45 (-1.34 / +1.31 / +3.85: on s2 / s3 the flow's search phase found the decoupling link countloop needs,
`n13__0`, but did not reach a rule-clean route in its 4 raise-only routes, so the loop's own route shipped). 10 routes:
faster on 7, median paired difference -1.27 ns, every draw passing (4 per route), 0 runts. **The merge alone
(`BDC_RING_FUSE=1`) is worse on 3 of 4** (seed 1: +3.98 / -0.63 / +3.17 / +3.58 ns): taking the link between the
update and the test off the ring puts return-to-zero on the cycle. **Why the gain is at most a few ns:** the merged
cell bundles the same update-then-test data path the two lines did, so what a merge takes off the ring is per-unit
overhead (a link's C-element and its hops, a join, a `uor`) and some of one line's margin -- on the segment from the
update's input to the steers, 11.07 -> 8.19 ns (xorshift s1), 9.01 -> 6.15 (collatz s2), 9.92 -> 9.70 (countloop s1,
where the 1-bit test link's line grew to 5 elements to cover the fanout to five steers) -- of a 19-23 ns ring, and it
has to keep a storage stage (=2's test link) or lose more than that to return-to-zero. Farm request for 8 seeds x 4
kernels: out/ringfuse1.sh (not filed).

## 1. What is on each ring, and what each unit costs (rising-only floor, per unit)

`research/tools/eventgraph/rfloor.py GRAPH`: the worst cycle with no polarity change (the rising pass: no storage can
go below it), split per kernel instance into the hop into it (inter-instance wire), its matched-delay chain (elements
and their wiring) and the rest (C-elements, joins, `uor`, mux logic). Wire is 85-87 % of every floor. ns per unit, in
ring order (el = matched-delay elements); P = the route's period.

| graph (no kernel list; seed) | P | rising floor | the floor's ring, unit by unit (ns) |
|---|---:|---:|---|
| gsB_countloop_1 (v7 structure, farm sizes) | 21.40 | 19.36 | merge 1.29 (1 el) -> its olink 1.36 (2) -> select link n16__0 2.25 (3) -> mux0 2.40 (4) -> link n10__0 0.65 -> **add 2.14 (6) -> link n22__1 0.82 -> compare 6.96 (15)** -> steer join 0.72 -> steer 0.34 -> back link 0.41 |
| gsB_countloop_2 | 20.83 | 20.83 | select link 2.00 (4) -> mux0 2.00 (3) -> link 0.63 -> **add 4.63 (9) -> link 0.62 -> compare 5.73 (11)** -> steer join 0.60 -> steer 0.46 -> back link 0.49 -> merge 2.39 (3) -> olink 1.28 (2) |
| gs_countloop_4 | 24.30 | 19.45 | steer join 0.60 -> steer 0.52 -> back link 0.49 -> merge 1.41 (1) -> olink 1.12 (2) -> select link 1.85 (3) -> mux0 2.38 (4) -> link 0.62 -> **add 3.64 (9) -> link 0.69 -> compare 6.12 (12)** |
| bqa_ipow_2 (e ring) | 22.71 | 18.05 | select link 0.99 (1) -> mux1 3.32 (5) -> link 0.74 -> **shrsi 1.35 (1) -> link n31__1 0.72 -> compare 6.19 (10)** -> steer join 0.73 -> steer 0.53 -> back link 0.49 -> merge 1.81 (2) -> olink 1.19 (2) |
| rj_ipow_4 (r ring) | 21.61 | 17.32 | mux2 3.00 (4) -> link 0.49 -> select region (andi, cmpi, muli, select) 11.06 (24) -> steer join 0.81 -> steer 0.42 -> back link 1.53 (1) |
| bl_xorshift_1_7 (norw1's shipped s1 route rebuilt here: sdf f10ea738, P 20550 as on the farm) | 20.55 | 20.55 | select link 1.44 (2) -> mux0 2.83 (4) -> link n7 0.33 -> **add 5.02 (10) -> link n30__1 0.72 -> compare 5.33 (10)** -> steer join 0.84 -> steer 0.33 -> back link 0.49 -> merge 2.13 (3) -> olink 1.09 (2) |
| bl_collatz_2_7 (norw1's s2 route rebuilt: sdf 493f84e6, P 22864 as on the farm) | 22.86 | 22.55 | merge 1.33 (1) -> olink 1.38 (2) -> select link 1.22 (2) -> mux0 3.70 (6) -> link 0.77 -> 3n+1 region 2.77 (5) -> link n26 0.42 -> **select region 3.18 (5) -> link n28__1 0.47 -> compare 5.36 (12)** -> steer join 0.75 -> steer 0.59 -> back link 0.62 |
| *with BDC_RING_FUSE=2 (section 4):* rf2_xorshift_1_7 | 18.79 | 18.79 | select link 2.43 (3) -> mux0 2.31 (3) -> link n7 0.58 -> **add + compare 7.30 (15) -> test link n31 0.89 (1)** -> steer join 0.61 -> steer 0.52 -> back link 0.38 -> merge 2.41 (3) -> olink 1.38 (2) |
| *=2:* rf2_collatz_2_7 | 20.73 | 20.69 | steer join 0.55 -> steer 0.59 -> back link 0.41 -> merge 1.45 (1) -> olink 1.41 (2) -> select link 2.11 (3) -> mux0 2.72 (5) -> link 0.65 -> 3n+1 region 4.14 (7) -> link n26 0.51 -> **select region + compare 5.16 (9) -> test link n30 0.99 (1)** |
| *=2:* rf2_countloop_1_11 | 19.58 | 19.58 | select link 1.73 (3) -> mux0 2.78 (5) -> link 0.30 -> **add + compare 6.37 (14) -> test link n23 3.33 (5)** -> steer join 0.64 -> steer 0.34 -> back link 0.22 -> merge 2.58 (3) -> olink 1.30 (2) |

The update and the test are 7.8-11.1 ns of the counter ring's 18-21 ns floor (40-53 %; collatz: select + test 8.5 ns
of 22.6), and the units between them --
the rule-1 link in front of the test (0.62-0.82 ns), the test's own N=2 join and `uor` (0.9-1.2 ns of "other") and its
in-hop (0.29-0.47) -- about 2 ns. That 2 ns, plus whatever the merged line saves against two lines, is all a merge
can take: the matched delays themselves bundle a data path that does not get shorter by being in one cell.

What merging consecutive units would save, priced on these rows (the merged unit pays its own data path):

| merge | units it removes from the floor | saved (graph) | needs |
|---|---|---:|---|
| mux + increment | link n10__0 (0.62-0.65) + the add's in-hop (0.50-1.44) + its join arc (0.07) | 1.2-2.1 ns + a guard | a new cell (bd_mux is frozen and carries its own line); the mux's output also feeds the accumulator on countloop (a second result) |
| **increment + compare** (built here) | link n22__1 (0.62-0.82) + the test's in-hop (0.29-0.47) + the add's join arc; one line instead of two | 1.0-1.4 ns + what one line saves on two (measured on the =2 routes: 0.2-2.9 ns on that segment, section 4) | nothing new: a fused region with two results, and a link on the test output to keep the decoupling |
| compare + steer | the steer's join (0.60-0.72) per steer on the floor; fork9's hop | 0.6-1.0 ns per steer | a new cell (a steer bank with the test inside: one join over every loop-carried value), out of scope here |

Every merge also takes a STORAGE stage off the ring (the link between the merged units), and with it the decoupling it
gave: section 4 measures what that costs.

## 2. What bdc's fusion merges, and why it stops on these rings

`compute_fusion()` (bdc/emit.py, BDC_OP_FUSION, on by default) unions fusable ops (addi subi muli cmpi andi ori xori
shli shrsi shrui select; not mux, not the dividers) along DIRECT op-to-op edges, absorbs a fork only when its whole
fanout reconverges into ONE region (`_absorb_forks`), caps a region at BDC_MAX_FUSE_NODES = 4 members, and requires
every region to have exactly ONE result (`_build_region` raises otherwise). On the four rings it stops at:

- **the fork between the update and its two readers** (all four kernels): `x' = f(x)` is forked to the loop test
  (a fusable cmpi) and to the loop's data steer (cond_br, not fusable): countloop / xorshift `i + 1` (fork8 -> cmpi1,
  cond_br6), collatz the select region's new n (fork7 -> cmpi2, cond_br7), ipow `e >> 1` (fork9 -> cmpi2, cond_br7).
  The fork does not reconverge into one region, so it is not absorbed, and a region with the test in it would have two
  results. That is the rule-1 link in front of the test and the test's own join, `uor` and line.
- **the mux** (excluded on purpose: bd_mux is a select-driven rendezvous with its own line and select join);
- **the steer** (cond_br: a bd_join of condition and data and a bd_steer, control, not data);
- **the 4-member cap** (collatz: {shli, addi, addi} = 3n+1 and {andi, cmpi, shrsi, select} are two regions with a link
  n26 between them, on the ring; with BDC_MAX_FUSE_NODES=8 they are one: emitted, not simulated or routed here);
- **constants from a shared source** (collatz, ipow: source -> fork -> several constants; BDC_CONST_DATA keeps their
  channels as join inputs, so the readers of one source wait for each other: graphsearch's BDC_SPLIT_SOURCES).

## 3. The pass: BDC_RING_FUSE (bdc/emit.py, opt-in)

`BDC_RING_FUSE=1` (unset: `compute_fusion` and the Verilog are byte-identical): `_ring_merge` takes every fork whose
operand is a fused region's result and some of whose outputs feed fusable ops in other regions, and merges those
regions into one; the fork's other outputs become results of the merged region. Nothing is keyed on a kernel: it
matches the fork shape anywhere (81 merges over build/frontend: 49 fixtures emit differently with it, 46 of them
suite kernels -- 46 of the 62 the suite lists).
The merged cell is the usual fused module -- one bd_join over its external inputs, one `uor`, one matched delay
(named after the topologically last member, e.g. `ucmpi1`), the members as wire assigns -- with every result side
by side in `z_data`; a bd_fork `<inst>_fo` splits its request into one channel per result, each its slice (a result
that rule F names in BDC_FORK_OUT_LINK keeps its link). A merge is refused unless (1) every member and the fork are
in one basic block, (2) the merged region has at most BDC_RING_FUSE_MAX (8) members, and (3) no path leaves the
merged region and re-enters it without crossing a mux / merge / control_merge (an iteration boundary): the merged cell
fires only when all its inputs are there, so an input that needs one of its own results in the same firing would
never come. (3) refuses 7 merges on the fixtures (dot2, gather, iterative_sqrt x 2, memsum, share_test_2, varshift):
e.g. memsum's `i + 1` reaches its own test through an `extui` outside the region.

`BDC_RING_FUSE=2`: the same merge, and a bd_link (a BDC_FORK_OUT_LINK) on every result of a multi-result cell that
has no storage yet -- in practice the 1-bit test output (the data result already has rule F's link). Why: section 4.

On the four kernels, =1 takes off the ring: countloop / xorshift the link n22__1 / n30__1 between `i + 1` and the
test and the test's join, `uor` and line (one cell `ucmpi1` = addi + cmpi); collatz the link n28__1 between the
select region and `n == 1` (one cell {andi, cmpi, shrsi, select, cmpi2}); ipow the link n31__1 between `e >> 1` and
`e > 0` (one cell {shrsi, cmpi2}).

**Correctness** (zero-wire RTL, cells/sim primitive arcs):
- switch unset: `emit.py --no-top` byte-identical on all 195 outputs of build/frontend in default, BDC_AUTO=1 and
  BDC_HOST_MEM=1 (header line aside: it names the input path), exit codes identical on the 138 refusals, at the
  first and at the final commit; with =1, the final commit's 195 outputs equal the first commit's (the fused cells'
  output fork renamed `_f` -> `_fo` aside);
- with =1 and with =2, every suite kernel the switch changes (46 of 62; the other 16 are byte-identical with it):
  simcheck (21 scalar kernels: `--c-oracle` or the REFS path, as subagent hangs ran them) and memtb (25 memory kernels,
  `--timeout-us 5000`, 2 runs per call, every array read back), default flow and BDC_AUTO=1: **=1 92 / 92 PASS,
  =2 92 / 92 PASS** (the tables: out/rtl/ of the subagent's report);
- **negative controls, both fail:** (a) BDC_RING_FUSE_NEGCTL=1 (a multi-result cell drives every later result with
  the first one's value): countloop / xorshift / collatz TIMEOUT (the counter never reaches the bound), ipow WRONG 12
  of 17 vectors (b=3, e=15: got 27, expected 14348907), both flows, with =1 and with =2; (b) the deadlock check
  removed: memsum's refused merge {addi2, cmpi1, cmpi2, andi0} hangs memtb at call 0 (TIMEOUT after 5 ms of circuit
  time); with the check, PASS 5 / 5;
- bdc/test_ring_fusion.py: the merge, its three refusals (other block, cap, memsum's same-firing cycle) and the loop
  header case; with test_fork_fusion.py and test_fusion_sharing.py, 42 tests pass.

## 4. Through the whole automatic flow

`research/tools/suite/suite_one.sh K S 4 4` with the switch in the environment (every bdc call of the flow reads it),
SUITE_TAG rf (=1) / rf2 (=2), CA_JOBS=1, DRAW_JOBS=1, local, nextpnr 6e5d224472232d5d. =1 ran at 56d0b2979 /
4dc8c2ecf (byte-identical emission), =2 at 21be026af. Predictions: out/PREDICTION.txt (UTC, before each build).
"P of the loop's own route" is the route the sizing loop ended on, before the search phase (flow v7 then ships the
search's route only if it is rule-clean and faster, or the loop's route was not clean). Baseline: the same kernel and
seed through the same flow without the switch, from the farm (base source = request/task).

| kernel | seed | switch | P shipped (ns) | P of the loop's own route | rule | draws | LUTs | latency sum (ns) | base P (ns) | base rule | base LUTs | base latency sum | dP (ns) | base source |
|---|---:|---|---:|---:|---|---|---:|---:|---:|---|---:|---:|---:|---|
| collatz | 1 | =1 | 22.15 | 28.95 | clean | 4/4 | 1305 | 36360 | 18.98 | clean | 1265 | 31368 | +3.17 | norw1r2/9 |
| collatz | 1 | =2 | 20.64 | 20.64 | not-clean | 4/4 | 1270 | 33810 | 18.98 | clean | 1265 | 31368 | +1.66 | norw1r2/9 |
| collatz | 2 | =2 | 20.73 | 20.73 | not-clean | 4/4 | 1255 | 34926 | 22.86 | not-clean | 1292 | 39030 | -2.13 | nsearch1/8 |
| countloop | 1 | =1 | 24.90 | 24.90 | clean | 4/4 | 1686 | 10074 | 20.92 | clean | 1844 | 8694 | +3.98 | nsearch1/15 |
| countloop | 1 | =2 | 19.58 | 24.44 | clean | 4/4 | 1780 | 8190 | 20.92 | clean | 1844 | 8694 | -1.34 | nsearch1/15 |
| countloop | 2 | =2 | 22.68 | 22.68 | not-clean | 4/4 | 1713 | 9534 | 21.37 | clean | 1806 | 9168 | +1.31 | nsearch1/16 |
| countloop | 3 | =2 | 24.30 | 24.30 | not-clean | 4/4 | 1714 | 9888 | 20.45 | clean | 1819 | 8658 | +3.85 | nsearch1/17 |
| ipow | 1 | =1 | 25.30 | 24.69 | clean | 4/4 | 1333 | 5286 | 21.73 | not-clean | 1344 | 4680 | +3.58 | suite6/25 |
| ipow | 1 | =2 | 21.34 | 20.96 | clean | 4/4 | 1357 | 4542 | 21.73 | not-clean | 1344 | 4680 | -0.39 | suite6/25 |
| ipow | 2 | =2 | 20.01 | 20.01 | not-clean | 4/4 | 1282 | 4440 | 21.20 | clean | 1330 | 4698 | -1.20 | suite6/26 |
| xorshift | 1 | =1 | 19.92 | 21.43 | clean | 4/4 | 1297 | 38022 | 20.55 | not-clean | 1315 | 39162 | -0.63 | nsearch1/1 |
| xorshift | 1 | =2 | 18.79 | 18.79 | not-clean | 4/4 | 1280 | 35340 | 20.55 | not-clean | 1315 | 39162 | -1.76 | nsearch1/1 |
| xorshift | 2 | =2 | 18.08 | 18.08 | clean | 4/4 | 1296 | 35028 | 20.42 | clean | 1332 | 39852 | -2.34 | nsearch1/2 |
| xorshift | 3 | =2 | 19.61 | 19.61 | not-clean | 4/4 | 1279 | 37662 | 22.19 | clean | 1339 | 42576 | -2.59 | nsearch1/3 |

**=1 (the merge alone) loses on 3 of 4.** Its routes' rising floors are low (countloop 16.87, xorshift 16.84 ns on the
loop's routes, against 19.4-20.8 on the baseline countloop graphs and 20.55 on xorshift's, section 1), but the period
is not at the floor:
the merged cell cannot take its next inputs before every steer its test feeds has acknowledged (the link that stood
between the update and the test decoupled that), and return-to-zero comes onto the cycle -- countloop s1 24.90 ns
through `ucmpi1 -> fork9 -> cond_br8 -> back link -> mux -> ucmpi1_f -> link n15__1`, ipow s1 through the shared source
into the fused test. The flow's search phase ranks the 1-bit stage on the test's output first on all three graphs it
was run on (zero extra wire; countloop 24.90 -> 20.91, xorshift 21.43 -> 18.73, collatz 28.95 -> 22.19 ns predicted),
but on countloop =1 named it `BDC_MERGE_RES_LINK=ucmpi1`, a knob nothing reads (the output fork was called
`ucmpi1_f`, which the eventgraph tools take for a control_merge's result fork: renamed `_fo` in 316f32812), so it
never built it.

**=2 builds that link from it 0.** Every `=2` route passes its 4 draws with 0 pulses under 1 ns (GATE_RUNTS=1) and is
EQUIVALENT in the bits. On xorshift the loop's own route already sits at its rising floor (the search finds nothing
to add) on all three seeds, 1.8-2.6 ns below the baseline's; on collatz both routes sit at their floors (20.64, 20.69
ns), below 7 of the 8 baseline seeds but above seed 1's 18.98 (a loop that was clean at it 2); on ipow the floor is
the multiply ring the pass does not touch (rf2_ipow_1_9: select region 9.76 ns, 20 el) and the gain is 0.4-1.2 ns;
on countloop the ring the pass shortens is not the one that binds once the test is fused: the `a` operand's fork
(`n13__0`, into its steer) couples the accumulator ring to the test's acknowledge, and only the search's fork-out
link removes that (s1: 24.44 -> 19.58 ns; s2 / s3: picked, predicted 19.63 / 20.76, never rule-clean in 4 routes).

**Where the time goes on a fused ring (=2, countloop s1 shipped route, 19.58 ns at its rising floor):** merge 2.58 ->
olink 1.30 -> select link 1.73 -> mux0 2.78 -> link 0.30 -> fused add + test 6.37 (14 el) -> test link n23 3.33 (5
el) -> steer join 0.64 -> steer 0.34 -> back link 0.22 (10 units, was 11). The merged cell's line is sized to the same
update-then-test data path: 15 elements on =2 xorshift s1 where the baseline's seed 1 had add 10 + test 10; 9 on =2
collatz s2 against select 5 + test 12; 14 on =2 countloop s1 (16 on =1) against 6 + 15 on the baseline's seed 1 --
somewhere between a few elements under the sum and the sum itself (=1 xorshift s1's shipped route: 20). And on
countloop the fanout of the test bit to the five steers, which the test's line covered before, is now the test link's
line (5 elements). So on the update-to-steer segment a merge saves 0.2-2.9 ns (section 1's bold units against the
=2 rows: 11.07 -> 8.19 xorshift, 9.01 -> 6.15 collatz, 9.92 -> 9.70 countloop), and the whole ring moves by that plus
or minus the re-placement of everything else.

## 5. What this does not show

- **Seeds.** One to three routes per kernel and switch value, not the four CLAUDE.md asks for a routed claim, and the
  pairing by seed is weak: the fused netlist is a different circuit, so seed S is an unrelated route of it. Route
  scatter on these kernels is +-1.5-2 ns (the baselines' own seeds: xorshift 20.4-23.6, collatz 19.0-26.7, countloop
  20.5-24.3, ipow 19.8-23.4 ns). The farm request out/ringfuse1.sh (8 seeds x 4 kernels with =2, and the v7 column
  where it is missing) is what turns these into a claim.
- **Baselines.** xorshift, collatz and countloop seeds 1-4 are flow v7 (nsearch1, norw1r2); ipow's is suite6, flow v6
  (no search phase): its comparison mixes two flows (the farm request adds ipow's v7 column).
- **Rule-clean.** Several routes on both sides end NOT CLEAN after 7 (the loop's phase 2 limit); they are judged by
  their draws (all pass), as the headline does, and kept apart in the table's rule column.
- **Simulation, not silicon**: the itercost stack's delay model, 4 draws per route, GATE_RUNTS=1 (report).
- **Not built:** BDC_MAX_FUSE_NODES=8 with the pass (collatz's whole body in one cell: {andi, cmpi, shrsi, shli,
  addi, addi, select, cmpi}; it emits, but was neither simulated nor routed); merging the mux or the steer (new cells);
  fusing `extui` / `trunci` (wires) so that memsum's refused merge becomes legal.
