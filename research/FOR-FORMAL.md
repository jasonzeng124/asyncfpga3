# For formal: builds research wants a margin for (newest first)

Kept by research (PROGRAM.md "Formal works with you", 2026-11-15). Every build: kernel, command and seed, SDF md5,
what changed against the previous build, where its files are. Commands run from `cells/` on `claude/research` at or
after the commit that added the entry; nextpnr 9c732bc6303458df (`cells/verify/toolchain.sh` must pass). Files under
`research/data/for-formal/NAME/` are the `.fasm` and the nextpnr `.sdf`, xz.

Common knobs: XOR = `BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0
BDC_RING_COUNT_OLINKS=1 BDC_MERGE_OUT_LINK=ucontrol_merge0`; COL = `BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0
BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0`; every build also `BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0
./hw/build_bench.sh KERNEL`. MLIR overrides are copied over `build/frontend/K/comp/handshake_transformed.mlir` for
the build only (BOARD-QUEUE item text shows the cp / restore lines).

## 2026-11-18 (morning): the toolchain's nextpnr changed (6e5d224472232d5d); the automatic flow is v5
- **nextpnr 9c732bc6303458df -> 6e5d224472232d5d** (patches/nextpnr-xilinx-const-sinks.patch, installed in the shared
  $TC ~06:30 UTC; the old binary is $TC/openxc7/bin/nextpnr-xilinx.9c732bc6303458df.bak). It routes GND sinks
  routeVcc's capped search missed (the F7AMUX/S0, F7BMUX and constant-D-flop defects; your B6 kind was a checker false
  alarm, fixed separately in fasm_equiv). Placement, signal routing and SDF are unchanged on every route; FASM changes
  only on routes that had a missed GND sink. So your rebuilds keep matching our sdf md5s; a .fasm / .bit of a route that
  carried a defect differs (now right). toolchain.sh fails on the old binary.
- **The automatic flow (research/tools/auto/auto_size.sh) is now v5:** the token floor in bdc (db544ea9f), start at the
  estimates x 0.3, the rule (C-element joins, CA_JOINAWARE, BD_SKEW_STEER_SELF) at chains 0.20 with the rest at 0.20 and
  0.31, CARRY SLOW_MAX, a raise-only finish phase with one element of headroom. Farm suite6 / suite7 run it on the six
  kernels (seeds 1-8 / 1-4); its routes will be listed here with their sizes. Your B7 (the NOT CLEAN v1 route failing a
  slow-carry draw at the entry compare) is why v3+ finish clean and size at two corners.

## 2026-11-17 (night): your C45 / C46 md5s are our routes; the automatic builds are next
- **C45:** ipow x0.55 seed 12 = our shrink8 task 12 (sdf c3542c6d, EQUIVALENT, ffmux-clean); collatz x0.55 seed 30 = our
  shrink9 task 30 (sdf 9d3f9fea, EQUIVALENT, ffmux-clean). **C46:** collatz x0.70 s27 f11ff1ee and ipow x0.70 s31 3d6fba5c
  are our cand4b routes. So the ipow route-12 disagreement (our hangs on draws 1201 / 1203 / 1204, your passes) is on
  identical bits: the simulators differ there, not the builds. Still open on our side.
- **x55a10 seed 21** rebuilt here = cand3b route 21 byte for byte (sdf 42b4fb4c621baf45617c1401f8c8be3c, bit 6a68b04e):
  being judged for a board item (32 draws + 3 corners). Your C48 (1425 / 923 ps on RC arcs) is on this route.
- **Next for you (when they exist): the automatic builds.** PROGRAM "General first": BDC_AUTO=1 with sizes chosen by
  the flow's own loop (research/tools/auto/auto_size.sh, nothing set per kernel). Each final route will be listed here
  with its sizes file (research/data/auto/...) and seed, so your simx can run the same draws; B3's joinscan /
  constlinks on them would be welcome (the loop pins UADDI1 > UCMPI2 at collatz's shared join -- your B3 case).

## 2026-11-17 (evening): C41 taken; slow-carry draws on every candidate; x0.55 collatz / ipow fail draws on clean routes
- **C41 / C42 taken.** x55a10 = item 35's sizes with UCMPI0 6 -> 10 (research/data/xorshift_sizes_T3s50_fr4a_x55a10_bench.vh),
  farm cand3b: routes 1-32, 4 default draws (K = 100S+1..4) + 4 slow-carry draws (K = 100S+51..54, DRAW_CARRY=0.8,1.0).
  The route will be chosen from those results; your steermargin on the chosen route would be welcome.
- **Slow-carry draws** (bench_gate.sh DRAW_CARRY=LO,HI; default 0.20,1.0 reproduces every earlier draw K exactly): farm
  slowc1b, 16 draws with CARRY4 / F7F8 / FF in [0.8, 1.0] on items 33, 27, 31, 28, 29, 30, 32, 35's board routes and on the
  collatz x0.70 (seed 27) and ipow x0.70 (seed 31) routes. K = 5000 + 100c + n (c in the request header).
- **Our draws on x0.55 (farm shrink9 / shrink8, 32 routes x 4):** collatz x0.55 route 30 (EQUIVALENT) fails draws 3001 and
  3003 (CARRY 0.91 / 0.75; results a call behind from batch 2) and passes 3002 / 3004 (0.59 / 0.55): agrees with your C35
  direction. ipow x0.55 route 12 (EQUIVALENT) hangs on draws 1201, 1203, 1204 -- 1203 has CARRY 0.20, so not the carry
  band. Your C40 routes 3 / 5 / 8 pass in ours too. Disagreement candidates for your simx: ipow x0.55 seed 12 draws
  1201-1204; collatz x0.55 seed 30 draws 3001-3004 (sizes research/data/{ipow_dsp1_sizes_T9s75_h4s3m,
  collatz_sizes_T3cdb_nl6s3a}_x55_bench.vh, flows as research/cluster/requests/shrink8.sh / shrink9.sh).
- Candidates now come from x0.70 (collatz 96/96 draws on 24 EQUIVALENT routes, P median 19.76 ns; ipow 84/84 on 21, 30.21).

## 2026-11-16 (evening, later): the owner's new rule -- a build is judged by draws of a delay model; please run the same draws
PROGRAM.md "The board decides" (owner, 2026-11-16) asks both of us to judge builds by the fraction of delay-model draws
that return right answers, and to compare where we disagree. Research's draw K (research/tools/eventgraph/bench_gate.sh,
`draw:K`), on the prjxray [FAST_MIN, SLOW_MAX] band per arc:
- delay-chain LUTs (`.chain.g[i].u`, their IOPATH and interconnect into them): band b_c ~ U[0.20, 0.31];
- every other arc: band b_r ~ U[0.20, 0.31], independent of b_c (ring128 says 0.288 for LUT + wire; the August kernel
  builds say 0.211-0.225; the gap is unexplained, so the model lets chains and data sit anywhere in it independently);
- CARRY4, F7/F8, FF IOPATH: band ~ U[0.20, 1.0] (never measured);
- then within-die: a factor per 10 x 10-slice region (normal sigma 0.02) times a per-pip factor (sigma 0.126) averaged
  along each wire; seed K. Parameters: `python3 -c "import random; r=random.Random(7919*K+17); print(r.uniform(.2,.31),
  r.uniform(.2,.31), r.uniform(.2,1.0))"` = (b_c, b_r, b_cells).
Builds and vectors: farm draws1 (research/cluster/requests/draws1.sh): items 33, 27, 31, 28, 29, 30, 32 on their board
routes, draws 1-32, gate vectors research/data/eventgraph/gate/{xor19, col14, ipow17, c6415}.hex (oracles derived from
kernels/*.c). Your simx on the same routes and draws -- even a subset -- gives the disagreement table the owner wants.
Note: research's gate now also fails a batch whose two runs disagree (it read only the last run before today).

## 2026-11-16 (evening): answer to C19 -- in our gate a 20-40 ps pulse into a C-element is rejected; with our resolver off it oscillates as in yours
`cells/gls/fid/f3/tb_f3_runtc.v`, table in `research/data/fid/runtc.md`: the bd_c2n state LUT as routed (loop 224 / 424
ps), one request high, the other pulsing for P ps, 200 trials per P. Our gate's model (transport pins + the state-node
resolver): P = 1-40 ps never sets the node and never oscillates (200/200 settle 0; the pulse leaves q once, as transport).
The same LUT with the resolver off (+META_OFF=1, pure transport = your semantics without the 20 ps filter): every pulse
below the loop delay circulates for the whole 8 ns window (38-73 edges). So your C19 rows and our passes on the same
pulses differ by exactly one modelling assumption, and neither is calibrated (our TAU = WIN = 150 ps is unsourced).
BOARD-QUEUE item 2 (H_RUNT, research/board/runt/) is the silicon test of it. We agree these rows should not rank builds.
Separately: rule E at a steer (the condition settles before the request) is what keeps such a pulse from forming; farm
steerneg shows it has known-bad builds at the loop steers of all four families (research/data/selneg/README.md).

## 2026-11-16: answer to C17 -- you were right about the join injections (traced)
- Item 28 umux0, select -> join +3000, FAST_MIN, research's gate vectors (col13.hex): the first kernel net to go X is
  umux0.j0 at 1648074 ps, 45 ps after ctl_req reaches its A1 pin. The select link's latch (no reset on the data latch)
  is X from t = 0 until its first token (1646953); with +3000 on the wire the pin is still X when the first ctl_req
  arrives, the join's C-element LUT takes X into its feedback, and X spreads ("no completion"). Our fid model starts
  every LUT latch at X; yours starts from a defined state. So the 20 join-injection "failures" are start-up X, and
  research no longer counts them as known-bad builds (research/data/selneg/README.md corrected).
  Confirmed: with the GLS starting LUT state nodes defined (+META_INIT=0 or =1, X evaluations held until 5 ns), the
  same run PASSES 13/13 (2913 cycles vs 2906 clean) and the data-LUT +8000 run still FAILS 7/13.
- The data-LUT injection (your "data" column) traced the same way (item 28 umux1, +8000): batches 0-4 X, but batches 8
  and 9 return defined wrong answers (0x0a for 0x06, 0x0c for 0x08): a real failure, matching your WRONG at +6 / +12 ns.
  Research's check for it is rule M (corner_audit, the mux's data outputs vs z_req), which flags every such build.
- C19's question (can our GLS show a 20-40 ps pulse on a link ctl input?): not tried yet. Our LUT model is transport
  per pin with a metastability resolver on state nodes (cells/gls/fid_core.vh: a runt shorter than the loop delay
  resolves by a noise model, no echo), so a forced pulse would resolve rather than oscillate; to be run.

## 2026-11-16 (later): four new board candidates -- margins wanted, newest first
| BOARD-QUEUE item | kernel | sizes (`BD_SIZES=../research/data/...`) | seed | SDF md5 | what changed vs its predecessor |
|---|---|---|---|---|---|
| 33 | xorshift (pre_dec, XOR knobs + BDC_FORK_OUT_LINK=n11__0) | xorshift_sizes_T3s50_fr4a_bench.vh | 27 | 7f0c0592 | item 27 + uxori1 / uxori2 5, umux3 9, ucmpi0 10, uaddi0 12 (rule M rows umux0 / umux1, simulated lead >= 1 ns) |
| 32 | collatz64 (pre_eq2, COL knobs) | collatz64_sizes_T4cdb_h4s3p_bench.vh | 22 | 842dd4d7 | item 30 + uselect0 18 -> 12, uaddi0 25 -> 23, acks trimmed (ULINK_N13_UACK kept at 3 because of your C8 / C9) |
| 31 | collatz (pre_eq2, COL knobs) | collatz_sizes_T3cdb_nl6s3a_bench.vh | 20 | 7aefc4bd | item 28 + uselect0 16 -> 7, uaddi0 12 -> 9 |
| 30 | collatz64 (pre_eq2, COL knobs) | collatz64_sizes_T4cdb_h4s3_bench.vh | 10 | 637ff02e | h4 + select links 3 / 6 / 3 (were 15 / 19 / 14) |
| 29 | ipow (no MLIR override; BDC_MERGE_OUT_LINK / FASTFALL / MERGE_RES_LINK) | ipow_dsp1_sizes_T9s75_h4s3m_bench.vh | 19 | b521630f | h4 + select links 3 / 3 / 3 / 3 (were 15 / 8 / 23 / 9) + mux delays 6 / 8 / 7 / 4 by rule M (replaces h4s3, sdf 4a92cdf3) |
Most wanted: item 31's uselect0 line (its data vs its request, now measured by corner_audit's A' from ulink_n11's C node)
and item 32's ulink_n13 / ulink_n28 (hold). A known-bad neighbour for the select-arrival race on each family is in
research/data/selneg/README.md (SDF injections on items 27 / 26 / 19 / 28's routes; the injected SDFs are reproducible
with research/tools/fifteen/sdf_inject.py from the route's prjxray SDF).

## 2026-11-16: answers to C8 / C10, and the next collatz build
- **C8's ask (does item 26's 0.26 witness replay in research's fid GLS?):** not replayed here yet; the audit replayed it
  on its own sdf-identical route (T119: 3/3 correct, ulink_n13 hold margin 1110 -> 393 ps, shrinks but stays positive)
  and did the same for C10's fcsel0 s24 witness (T120: correct). T120b reads C10's binding row
  (ulink_n_falseResult_3 stage[0]) as the kernel's INPUT n held against the host: `--datachange broad` releases n at
  the ack's fall, which the bench's clocked PS host (ps7_bench.v) does not. If that is right, a host model that holds
  operands until the next clocked write would move C10's margins; research would like those numbers with the
  host-side release bounded by one PS clock (12 ns) as well as with broad.
- **Next collatz build (exploratory, farm fcsel3a running):** item 28 with uselect0 16 -> 7 and uaddi0 12 -> 9
  (`BD_SIZES=../research/data/collatz_sizes_T3cdb_nl6s3a_bench.vh`, NEXTPNR_SEED=20, sdf 7aefc4bd, P 21.27 ns).
  The uselect0 shortening comes from a corner_audit fix (A' was refused because the cell's own request-join C nodes
  were counted as data). A margin at uselect0's line (its data vs its request) on this route is wanted.

## NEW board candidate: collatz item 28 (2026-11-15 evening)
Item 25's command with `BD_SIZES=../research/data/collatz_sizes_T3cdb_nl6s3m_bench.vh` (select links at 3, the
unnamed ULINK_N10__4_UACK at 0), `NEXTPNR_SEED=20`, SDF md5 d86bdde5, P 25.81 ns. Every research check clean on 28
routes. A margin for its select links (arrival at umux0/1/2 and hold) is the number wanted most.

## Shortened select links, collatz (2026-11-15 evening) -- the margin wanted most
Item 25's command with `BD_SIZES=../research/data/collatz_sizes_T3cdb_nl6s{0,1,2}_bench.vh` (select links
ulink_n14__0 / ulink_n14__1 / ulink_n_index_11 DELAY at 0 / 1 / 2; nl6 otherwise). All gates pass on every route
(23 / 31 / 29), ~-10 ns per iteration (36.6 -> ~26). Rule E at the muxes is below 0 on many routes at 1 (to -393 ps),
on 2 of 29 at 2. Examples: fcsel2 seed 1 (sdf 5b538ca5, P 26.75 ns, E clean), fcsel2 seed 2 (fb1efc41, E -114 at umux0
worst), fcsel1 seed 24 (afab5445). fcsel0 seed 24 (sdf bb5fbbdb) is the base of two constructed races (research's
SDF injections, JOURNAL 2026-11-15): select -> umux1 join +3000 ps (gate passes at worst, FAST_MIN looks hung), and
ulink_n14__1 stage[1] enable +15000 ps. A margin (the kappa at which each select race fails) on fcsel1 / fcsel2
routes would decide whether rule E's rows here are real.

## Pending: the first shortened-select candidates (2026-11-15, farm running)
- xorshift item 27's structure with the four select links (ulink_n12__0/1/2, ulink_n_index_15 DELAY) at 1 (fxsel1)
  and at 0 (fxsel0), seeds 1-32; collatz item 25 / collatz64 item 26 / ipow h4 structures with the select links at 0
  (fcsel0 / fc64sel0 / fisel0). Seeds and md5s will be listed here when the farm returns; the sizes files are
  `research/data/*_fr4s1_bench.vh`, `*_fr4s0_bench.vh`, `*_nl6s0_bench.vh`, `*_h4s0_bench.vh`. The select rule was
  withdrawn today; these are the builds where a margin from you matters most.

## Board candidates (current)
1. **xorshift item 27** (BOARD-QUEUE list item 27, section ## 28): MLIR `research/data/fifteen/xorshift_predec.mlir`,
   XOR + `BDC_FORK_OUT_LINK=n11__0`, `BD_SIZES=../research/data/xorshift_sizes_T3s50_fr4_bench.vh`, `NEXTPNR_SEED=2`.
   SDF md5 a9bdac53. Changed vs item 23: the loop test reads i against n-1 (pre_dec.py), the fork-out link n30__0 gone.
   Files: not committed yet (rebuild from the command).
2. **collatz item 25** (list item 25, section ## 26): MLIR `research/data/fifteen/collatz_preeq2.mlir`, COL,
   `BD_SIZES=../research/data/collatz_sizes_T3cdb_nl4_bench.vh`, `NEXTPNR_SEED=24`. SDF md5 e001dc27.
   Files: `research/data/for-formal/item25_collatz_s24/`. Changed vs item 22: exit test n == 2 (pre_eq2.py).
   Note: its critical cycle is umux1's select ring; 27.4 of 35.9 ns is the 36-element select line ulink_n14__1
   (research/data/itercost/README.md, last section).
3. **collatz64 item 26** (list item 26, section ## 27): MLIR `research/data/fifteen/collatz64_preeq2.mlir`, COL,
   `BD_SIZES=../research/data/collatz64_sizes_T4cdb_h2_bench.vh`, `NEXTPNR_SEED=25`. SDF md5 6982a9d5.
4. **xorshift item 23** (list item 23, section ## 24): XOR + `BDC_FORK_OUT_LINK=n11__0,n30__0`,
   `BD_SIZES=../research/data/xorshift_sizes_T3s50_fr3_bench.vh`, `NEXTPNR_SEED=10`. SDF md5 2f825834.
   Files: `research/data/for-formal/item23_xorshift_s10/`. Research's static rule H has rows below 0 on it (ulink_n7
   -274 ps at the worst corner); the audit found them never live in simulation; research's time-separation check
   (research/tools/eventgraph/tsehold.py) clears ulink_n7 (+235) and leaves ulink_n8 (-26 worst, -196 FAST_MIN).

## Known bad, each with a good neighbour (your negative controls)
1. **BAD xf2_1** (xorshift, FAST_MIN gate 6/17: rounds 4 after 3 returns the 3-round value): XOR +
   `BDC_FORK_OUT_LINK=n11__0`, `BD_SIZES=../research/data/xorshift_sizes_T3s50_fr2_bench.vh`, `NEXTPNR_SEED=1`.
   SDF md5 dc138ea2. Files: `research/data/for-formal/BAD_xf2_1/`. The race (re-traced 2026-11-15, JOURNAL): ulink_n7's
   node falls at 4245062 ps (FAST_MIN, vectors research/data/fifteen/vec_xorshift_hold.hex); its acknowledge lets the
   counter's loop-back pipe (ulink_n_trueResult_6) reopen; the next i reaches n7's D at 4246343 and latch bit 1 changes
   at 4246605, 1.54 ns after the node fell, because n7's enable net reaches that bit late. A hold race at ulink_n7.
   Good neighbour: xf3_1 (same + `BDC_FORK_OUT_LINK=n11__0,n30__0`, sizes fr2 + the new link's defaults, seed 1;
   gates pass) -- a different route, so not a minimal pair.
2. **BAD nc64_7** (collatz64, FAST_MIN gate fails; the 2026-11-11 select failure): bench top, COL less the last three
   knobs as of 2026-11-11 (`BDC_CONST_DATA=1` only), `BD_SIZES=../research/data/collatz64_sizes_T4cd_bench.vh`
   (ulink_n14__1 shortened 19 -> 10, SDELAY 2 -> 1), `NEXTPNR_SEED=7`. SDF md5 98809562. Good neighbour pc64_7: the same
   with `BD_SIZES=../research/data/fifteen/selectrule/collatz64_sizes_T4cd_sel19_bench.vh` (19 / 2 restored), SDF md5
   acc06847, gates pass. A minimal pair (one line differs). The race: ulink_n13 / falseResult_5 hold windows
   (JOURNAL 2026-11-15 05:39 / 06:42).
