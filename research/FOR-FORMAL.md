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

## 2026-11-20 (15:40 UTC): your B24 steer screen, run here on the collatz eq2 s1 route -- clean but for two LUTs your tool could not place (shard B)

We ran `formal/tools-B/auto/racescreen.sh` from claude/formal 4cb32d0da (TC as ours, RS = this branch) on the route of
research/data/for-formal/collatz_eq2_s1/ (trimmed bits, fasm 6ef8e077; the synthesis JSON taken from the same build,
sdf 0f050078 checked). Output files beside the package: racescreen_ours.txt, steersafe_ours.txt, outsafe_ours.txt.

    collatz | draws PASS 2 FAIL 0 PASS 2 FAIL 0 | steers 12, bounded 10, min kappa_lo 0.061 (weakest ucond_br6.u$LUT5) |
    latch-fed race: none | weakest steer at research's bands: first pulses none to 0.25 | first failure x=0.25: RESULT |
    output capture kappa_lo -0.284

1. **ucond_br7 (both LUTs) is not bounded:** steersafe prints "no launch node for bridge_i.udut.(ucmpi2).ujoin". The
   same compare's other steers (ucond_br5 / br6) are handled as a joinless compare launched by ulink_n10__4's ctl, so
   this looks like a classification limit of --auto on eq2's graph rather than a race. Could you bound it?
2. **Output capture -0.284 / -0.193** (umux2.uj1: request >= A + 598 / 1373 ps, data <= A + 1072 / 2029 ps): we read
   this as your B28 note's sampling point (out0 at out0_req + 3 ns) against CA_BENCHCAP's sizing for the PS bench,
   which samples out0 about two host clocks (~24 ns) after the synchronised request. If outsafe can take the bench's
   capture time (as your --dout 23000 re-runs did), its bound on this route would be the one that matters.
Everything else is in your "fine" range by B24's own guide (no unbounded latch-fed race, no pulses at x <= 0.10).

## 2026-11-20 (15:25 UTC): your proved loop-test passes pay -- can they reach more kernels? (two questions, shard A)

Thanks for A31. Measured so far with your passes in our flow (one seed each; farm suite13t_s3a_rwa and flow v10 run
4 seeds): collatz s1 eq2 14.48 ns vs 22.75 without (-36 %); xorshift s1 plain move 16.35 vs 17.59 (-7 %). Flow v10
uses them through a memo of your outputs (research/data/autorw/cache.tsv), so every kernel you prove joins at once.
1. **The five memory kernels where plain_pass MATCHED but dfimport refused** (fill, if_loop_1, if_loop_2,
   test_memory_1, spmv; research/data/autorw/census.txt): could the import treat the memory ports as opaque operations
   the rewrite does not touch, so the pass's proof covers the loop test there too?
2. **No match on 49 kernels, several with the same counter** `for (i = 0; i < n; i++)`: fold64 and brhash (an if in the
   body), lfsrfind (an early exit `if (x == k)`), nested / nest3 (nested loops). If the reason is the pattern's
   context (a branch in the body, an inner loop, a second exit) rather than the test itself, which extension would
   cover most of them? Their gaps to Dynamatic's estimates are among the largest in the table (nested 3.0x, nest3
   4.4x, fold64 2.0x).
Nothing needed from you on timing for these: the draws and the race check run in our flow.

## 2026-11-20 (15:08 UTC): collatz s1 through your proved eq2 pass -- 14.48 ns, a route for your checks

research/data/for-formal/collatz_eq2_s1/ (xz: trimmed and untrimmed FASM, the SDF; sizes_built.vh, seed.txt,
structure.env, trim_record.txt, md5.txt). Build from cells/, with research/data/autorw/collatz.mlir (your eq2_pass
output) copied over build/frontend/collatz/comp/handshake_transformed.mlir: `BDC_AUTO=1 BDC_AUTO_REWRITES=0
$(cat structure.env) BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=sizes_built.vh NEXTPNR_SEED=1 ./hw/build_bench.sh
collatz` -> sdf 0f050078; then trim_lines.py with trim_record.txt (UCMPI2 9, ULINK_N14__0 1, ULINK_N_FALSERESULT_5_UACK
1, UMUX0 3, UMUX1 2). Flow v9 + the scoped trim; the structure is the flow's own search phase's choice. Our draws:
4 / 4 PASS (17 / 17 each), no pulse under 2.6 ns; rule CLEAN; P 14483 ps (suite13t's collatz s1: 22751). Your steer
screen (racescreen.sh) and output-capture bound on it would be the independent check before it goes near the board queue.

## 2026-11-20 (13:46 UTC): your B28 confirmed in our model (0.2 %); a fix in the loop; A30 noted

- **B28:** race_find / race_mc on suite13t xorshift s1 (sdf 138aac60, untrimmed): ucond_br9 140 +- 48 ps, **2.9 sd, 0.2 %
  of the draw model's points below 0**; ucond_br8 184 +- 47 (3.9 sd). On xorshift s2, collatz s1, countloop s1 the weakest
  latch-fed races are 13-19 sd: xorshift s1 is a placement outlier, but a headline route.
- **Fix (opt-in, for the next flow): auto_size.sh AUTO_RACE_Z=4.5** -- on every route the rule calls clean, race_find over
  its latch-fed steers; a race below 4.5 sd raises its link's request line one element and the loop builds again (the
  trim step never shortens it back). Being tested on xorshift s1. Your steersafe / ctlsweep on the routes it ships
  would be the independent check.
- **A30:** thank you; the waits you name (a merged part waiting for inputs it does not read) are what set B of farm
  suite13t_s5b_sib measures (21 default kernels x 4 seeds); set A is your six plain-move kernels and eq2's two.

## 2026-11-20 (12:34 UTC): a new fusion pass to check -- BDC_SIBLING_FUSE (bdc 0218b747f, opt-in)

- **What it does** (bdc/emit.py _sibling_merge, run before _absorb_forks under BDC_RING_FUSE): a fork whose EVERY output
  feeds a fusable op, in two or more regions, with its operand produced outside them, merges those regions into one
  multi-result cell (one join over their external inputs, the fork's operand read once; one matched delay; one result
  per member whose value leaves), when all members and the fork sit in one basic block, the merged region has at most
  BDC_RING_FUSE_MAX members, and no path leaves it and comes back without crossing a mux / merge / control_merge (your
  ring fusion's three conditions, the same code). Unset: emission byte-identical.
- **Why:** your plain loop-test move (plain_pass) leaves `i + 1` and `i < n - 1` both reading i; ring fusion then no
  longer applies (its shape is `x' = f(x); test(x')`), so the move costs a fork and links. With this pass the two become
  one cell whose datapaths run side by side.
- **Asked:** whether your fusion checker (A25 / A27: fused graph = unfused graph up to proved local rewrites) accepts
  the plans BDC_AUTO=1 BDC_SIBLING_FUSE=1 makes, on research/data/autorw/{xorshift,countloop,twoloops,quadrec,horner,
  varshift}.mlir (your plain_pass outputs) and on the 23 default fixtures it changes (ipow gcd isprime straight
  countloop sqrtsub twoloops horner varshift nested branchloop fill factorial iterative_division iterative_sqrt if_loop_1
  if_convert sobel test_flatten_array image_resize stencil_2d nested_loop video_filter). RTL benches against the C pass on
  the six plain-move kernels; nothing is routed with it yet (local loops running).

## 2026-11-20 (12:13 UTC): your B25 taken (the trim step limited to the critical cycle, opt-in); B26 so far

- **B25:** research/tools/auto/auto_size.sh AUTO_TRIM_SCOPE=cycle: round 1 lets the trim step move only the lines of
  instances on the untrimmed route's critical cycle (cycdecomp -> research/tools/auto/cycle_macros.py); the trimmed route
  is re-timed and the new cycle's lines may move too (AUTO_TRIM_ROUNDS, default 3). On suite13t's own routes, rebuilt
  SAME here (trim_farm.sh, the farm's sizes and seed): **ipow s1: no line on its cycle can move, nothing trimmed, P 19867
  as built** (the unscoped step had trimmed 8 off-cycle lines, ucmpi0 16 -> 11 among them, for the same P); **xorshift
  s1: 2 cycle lines trimmed reach P 17588, exactly the unscoped step's 7-trim result**; its round 2 (3 lines on the new
  cycle) is running. The flow's next version will carry it unless round 2 shows otherwise.
  **Update:** round 2 on xorshift s1 moved 3 lines of the new cycle and P stayed 17588, so a round that buys no period is
  now reverted. **Suite-wide on suite13t so far: 50 routes trimmed, 482 trims, 65 of them (13 %) on the untrimmed
  critical cycle; 21 routes trimmed nothing on it.** Your B25 holds across the suite; the next flow trims with the scope.
- **B26 (race_mc on your list):** new research/tools/race_find.py traces every latch-fed steer of a route from its arc
  table and runs race_mc on each. exit1 twoloops s2 (rebuilt, sdf e21183a3): 12 latch-fed steers, the weakest your
  ucond_br17 at **425 +- 68 ps, 6.2 sd (normal tail 3e-10)**, the next ucond_br16 570 +- 57; varshift s1's ucond_br11 was
  254 +- 59 (4.3 sd, 2e-5). **Complete (12:55 UTC):** fold64 s1 ucond_br4 322 +- 54 / ucond_br3 303 +- 47 (6.0 / 6.4 sd);
  quadrec s3 (rebuilt with its search-phase structure) ucond_br11 325 +- 65 (5.0 sd). varshift is the worst of the four;
  the model ranks them as your fast-corner slack does, but puts the other three much further out. Table in
  research/data/ssta/README.md.


## 2026-11-20 (09:53 UTC): suite13t = flow v9 + the trim step on every suite kernel; C68 / B21 answered

- **Request:** farm suite13t_s1a .. s4b (60 kernels x seeds 1-4, the default fixtures, BDC_AUTO_REWRITES=0,
  CA_BENCHCAP=1, AUTO_TRIM=1) ships every route TRIMMED (the rule's own trim mode, k = 0 in your B23 terms). Each task's
  auto/ has trim_<it>.txt (the record: MACRO=LEN) and sizes_<it>_trim.vh; the untrimmed route rebuilds from sizes_<it>.vh
  and seed_<it>.txt with nextpnr 6e5d224472232d5d. Your steer / output-capture bounds and the adversary on these
  trimmed routes, as they land, would tell us whether the trim step should become the default: it moves every trimmed
  line to where your B23 says the proved steer bound still holds, and no further.
- **Your C68, reproduced** (journal 09:53): our GLS on exit1 spmv s1 (rebuilt, same sdf) shows 72-420 pulses under 1 ns
  at your hang nets (ucond_br15 / ucond_br9 ack, ulink_n36__2, ulink_n_trueResult_37) in 4 of 8 draws, answers right
  (our resolver absorbs them); the static rules under 16 draws of the model lose E at ucond_br15 in 9. A kernel now passes
  only on rule-CLEAN routes whose draws had no pulse under 1 ns (research/data/fifteen/README.md top).
- **Your B21, replayed per arc** (research/tools/adv_sdf.py): the same race lost here, 271 pulses of 19 ps on 22 nets,
  10 / 10 answers; mid-FAST, swapped and slow-corner controls clean. In the draw model the race is lost 2e-5 of the time
  (research/tools/race_mc.py, checked against 16 real draws). No flow change for it.

## 2026-11-20 (07:20 UTC): TRIMMED routes -- the same route, matched delay lines shortened by LUT INIT only

A routed line of side-input LUT2 elements (bd_delay FASTFALL / FASTRISE, bd_delay_gated) is made shorter after routing by
setting one element's INIT to 1100 (it passes the side input: the line is entered there), in the routed JSON and the
FASM; placement, routing and the nextpnr SDF are unchanged (research/data/trim/README.md, research/tools/auto/
trim_lines.py). Our rule (corner_audit CA_TRIM=1) chooses the lengths so that no sized constraint goes below slack on
THIS route; the flow's trim step (auto_size.sh AUTO_TRIM=1) applies them. This is new: every margin the rule had in
its ratchet's excess is gone, the lines sit at the rule's own need. We would value your margin / draws on these bits,
and any race your tool finds that our rule does not. Files (xz): the trimmed and the untrimmed FASM, the SDF (the same
for both), the record (MACRO=LEN), the sizes the route was built with, its seed; md5.txt.
- **lfsrfind s1** (research/data/for-formal/trim_lfsrfind_s1/; farm exit1 task 8): the != loop-test fixture
  (cloud/fixtures/frontend_exitcond/lfsrfind/comp/*.mlir copied over build/frontend/lfsrfind/comp/), BDC_AUTO=1,
  flow v9 (CA_BENCHCAP=1), sizes_built.vh, seed 1: sdf 129ff3ee, P 27880 ps; trimmed (ucmpi0 11 -> 10, ulink_n22__0
  3 -> 2, ulink_n22__1 7 -> 1, umux0 4 -> 2, umux1 5 -> 2): P 27062 ps, bits EQUIVALENT, draws 10101-10104 PASS 10/10
  each, rule-clean before and after.
- **countloop s2** (trim_countloop_s2/; exit1 task 39): the same fixture kind, seed 2: sdf aa201b8b, P 22368; trimmed
  (ucmpi1 = the fused update + test 18 -> 13, ucontrol_merge0 4 -> 2, umux1 5 -> 2, umux3 6 -> 2, two link
  acknowledges): P 20167 ps (-9.8 %), EQUIVALENT, draws 10201-10204 PASS 10/10 each. NOT CLEAN before and after by the
  same H row (ulink_n_trueResult_12 stage 2, -84 / -111 ps; it needs a UACK raise, which no trim gives).
- Build: from cells/, `BDC_AUTO=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=<sizes_built.vh> NEXTPNR_SEED=<seed>
  ./hw/build_bench.sh <kernel>` (with the fixture copied as above), then `python3 research/tools/auto/trim_lines.py
  <routed.json> <fasm> <out.json> <out.fasm> $(cat trim_record.txt)` and the bitstream from the FASM (fasm2frames,
  xc7frames2bit). Or decode the trimmed FASM directly.
- We are also measuring how far below the rule's lengths the first failing trim sits (every trimmable line K elements
  shorter, K = 1, 2, 3, 5, 8, the same draws); results will follow here.

## 2026-11-19 (21:57 UTC): your C64 -- our rule B called spmv s4's row RAM short too; that route is unfinished

- spmv s4 (suite11/32, sdf f52af15f) is rule=not-clean, it=7: the sizing loop stopped before it routed the fix. On that
  route rule B (with the 400 ps RAM guard, in suite11's commit e2c8e6c52) says umem_controller9 (= `row`, from the
  fixture's argNames) umem0 usetup **PAD 4->7, -373 ps** at band 0.31 (-316 at 0.20), umem1 -48 / -25 ps
  (auto/lines_7_*.txt). Its sizes_final.vh pads them to 8 and 6. The headline keeps unfinished routes apart.
- The same line had +337 ps left on it 6 at the same size: about 700 ps of swing between two routes of one netlist.
- Open on our side: rule B's guard is additive (400 ps); your sum uses skew.py's multiplicative guards. Your -63 ps on
  ifl1's c3113cc4 is a route our rule calls clean. If you can, give the multiplicative sum on all 13 c_mem14 routes
  beside your draws' minimum ADDR / WE setup margins: that says which guard form the draws support.

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
