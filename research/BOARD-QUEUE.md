# Board queue

Experiments that have passed every check possible without the board, most
valuable first. Each one: branch/commit, exact commands, pass criterion
(self-reporting, never "read the scope"), and what a failure would mean.

**2026-11-18: the toolchain's nextpnr is now 6e5d224472232d5d (patches/nextpnr-xilinx-const-sinks.patch).** It routes the
GND pins the old binary left unrouted (the F7-select and constant-D-flop defects below). Every item's route rebuilds
with the same sdf md5; on routes that had no such pin the .fasm is byte-identical too, so nothing below changes. Check
`cells/verify/toolchain.sh` (sha256 6e5d224472232d5d) before building.

**Before programming any build here: check its sdf md5 against the one the item names.** Two nextpnr defects (JOURNAL
2026-11-08) leave a constant site pin unrouted so the die reads its default instead: a 5FF D (collatz64 bench seed 4)
and an F7 select (ipow bench seed 7, wrong answers). Both are a deterministic function of the route, and every route
named here decodes EQUIVALENT (or only the benign GND-buffer kinds). If the md5 differs, the route was not gated: run
the full stack's equivalence on it before using the board (cells/gls/ps/build_ps.sh HWDIR WORK "" bit prints the
fasm_equiv VERDICT; refuse "not configured by the bits" and any "MUX/S0 json ('const', 0) bits ('const', 1)").

**2026-11-19 17:07 UTC: BDC_AUTO=1 now also fuses each loop's update with its test (BDC_RING_FUSE=2, flow v8).
Items 38-41 were built without it: their commands now say BDC_RING_FUSE=0, which rebuilds the same routes.**

**2026-11-18 20:00 UTC: items 39, 40 and 41 were built with bdc/auto.py's three md5-keyed MLIR rewrites (pre_dec /
pre_eq2), which BDC_AUTO=1 no longer applies by default (owner, auditor T156: the automatic path must not carry a list
of kernels). Their commands now say BDC_AUTO_REWRITES=1, which rebuilds the same routes. Item 38 (ipow) never used a
rewrite.**

**2026-11-19 03:50 UTC: items 38-41 have no narrow pulse on any kernel handshake net.** The gate's new runt monitor
(bench_gate.sh GATE_RUNTS=1, research/data/suite/steerrunt/README.md) counted pulses under 150 / 500 / 1000 ps on every
steer / mux / merge / C-element / link-enable / matched-delay output of the bits-decoded netlist: 0 under 1 ns on all
four items over 13 runs (item 38: worst, max, min, 2 draws; 39: worst, max, 1 draw; 40: worst; 41: worst, max, min, 1
draw); the narrowest pulse of any width was 1.54 ns. The same monitor flags the known-bad flow-v1 ipow route (1756
pulses under 1 ns on a draw the old gate passed). Not run: item 39 at FAST_MIN, item 40 at max / min / a draw.
**2026-11-19 05:29 UTC, re-judged under the strictest gate there is** (x in any run's result fails, any RAMB18 timing
event fails, GATE_RUNTS=fail: any pulse under 1 ns on a kernel handshake net fails; research/data/suite/board/
rejudge_2026-11-19_gate_strict.txt): items 38-41 at the worst corner and 3 fresh draws each (K 402xx / 406xx / 405xx /
408xx) -- every run PASS, 0 pulses under 1 ns, no x; narrowest pulse 2.1-4.1 ns.

## Run order now (2026-11-18 18:00 UTC; 3b-3d added 2026-11-21; each item below judges itself)
1. **Item 36** (the CARRY4 / MUXF7 band, research/board/carry/): the one delay band no kernel can pin; every draw model
   below assumes it uniform over [0.20, 1.0].
2. **Item 37** (xorshift x55a10 seed 21, 16.49 ns in simulation): the fastest xorshift, a hand recipe.
3. **Items 38 / 39 / 40 / 41** (ipow 22.71, collatz 18.99, collatz64 23.71, xorshift 20.11 ns in simulation): the
   automatic flow (BDC_AUTO=1, its own sizes, nothing set per kernel), each 35 or more judgments passing. A failure
   here, with its hand-item partner passing, is the most informative result this list can return.
3b. **Items 42 / 43** (2026-11-21: collatz 14.48 / xorshift 16.35 ns in simulation, flow v10 with formal's proved
   rewrites and the trim): each right after item 39 / 41, its judge's base.
3c. **Item 44** (2026-11-21: the whole automatic suite, 46 kernels, one self-judging loop; unattended, hours of
   rebuilds and minutes of board time): any time after item 36.
3d. **Optional for items 37-41 (2026-11-21, ~1 min each):** right after an item's build, before its loop_cost
   run, the same full-vector check items 42 / 43 have -- the kernel's own gate vectors through the gate's host program,
   judged by the gate's rules against the C. From cells/, with K and V = ipow / ipow17 (item 38), collatz / col18 (39),
   collatz64 / c6419 (40), xorshift / xor19 (37, 41):
       hw/board.sh ${XSDB:-/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab/bin/xsdb} hw/xsdb_bench_vec.tcl \
         build/hw/${K}_bench_gen/${K}_bench_gen.bit ../research/data/eventgraph/gate/$V.hex > build/hw/vec_$K.log 2>&1
       python3 ../research/tools/suite/board_vec_judge.py ../research/data/eventgraph/gate/$V.exp build/hw/vec_$K.log; echo "exit $?"
   Pass: `PASS n/n`, exit 0. (The GLS ran exactly these vectors on each of these routes: 35+ runs each, all PASS.)
4. Then the list "Board list, in order" further down (older items; several superseded by the ones above).
The simulation runs ~8 % slower per iteration than the August board (research/SIM-VS-BOARD.md), so expect each ns
figure above about 8 % lower on the board.

**Coming, not items yet (updated 2026-11-21 06:06 UTC):** collatz and xorshift with formal's proved rewrites are now
**items 42 and 43**. collatz64 v10 seed 1 (21.53 ns) is NOT coming: formal's screen puts pulses at a path error of
x = 0.08 on its loop-exit steer (research/JOURNAL.md 2026-11-21 04:17); built with a 10 % steer guard the same seed is
clean by that screen at +2 % P (research/data/guardx/; the farm's paired test, suite13t_s5g_g10, decides). The whole
suite on the board is **item 44**. Items 38-41 are unaffected by the latch-fed steer race formal found on a later
automatic xorshift route (B28): formal B22 cleared all four of it.

## 2026-11-17 (evening): item 36 -- the CARRY4 / MUXF7 band; the most useful board run now
No August latency can place the CARRY4 / F7 delay band (in bundled data the matched LUT chains set the cycle), yet the
fastest candidates' correctness depends on it: collatz x0.55 fails draws only with that band at 0.75-0.91, and item 35's
loop-entry race falls to ~0 ps near 0.9 (formal C38). Item 36 measures it directly; its answer replaces the draw model's
uniform [0.20, 1.0] for these cells. Simulation and construction checks only so far (fid GLS of the decoded bits within
30 ps of the prjxray walk on 96 points; both routes' bits EQUIVALENT; chains checked in the decoded bits; the fit's
negative control fails). Run it before the speed items.

36. **The CARRY4 / MUXF7 band (carry_ro_top): the one number no kernel can give** -- research/board/carry/ (two routes,
   s1 bit 40a85473, s2 bit 19ae3639; predictions committed before any run; cells/hw/carry_ring/README.md). 64 ring
   oscillators per bitstream on ro_many's JTAG harness: LUT-only rings (pin the LUT/wire band x again), rings through
   1 / 4 / 16 / 32 chained CARRY4 (CIN->CO3) and through 8 / 16 MUXF7 selects (S0->OUT), 8 placements of each. About
   2-3 minutes per bitstream (8 groups x 2 windows x 4 s). From cells/:

       for s in s1 s2; do
         hw/board.sh python3 hw/carry_ring/carry_measure.py ../research/board/carry/$s/carry_ro_top.bit \
           ../research/board/carry/$s/predicted.tsv build/hw/carry_ro_top_$s; echo "measure $s exit $?"
       done

   (xsdb / hw_server from VIVADO_LAB as for item 5; the script programs the device itself on the first group.)
   Pass: exit 0 and `=== PASS ===` on both routes. Exit 2 = the readback failed its own checks (constants, group
   echo, liveness, poison, overflow) or a ring is not the ring asked for: nothing is a measurement. Exit 1 = the
   band model does not explain these arcs (residual > 3%, C16 vs C32 or F8 vs F16 disagree, or the slope fit
   disagrees with the absolute fit); the line says which. The answer is the three lines before the verdict:
   `CARRY_BAND y=... +-...`, `F7_BAND y=... +-...`, `LUT_BAND x=...`; please paste them (and build/hw/carry_ro_top_s*/
   measured.tsv + raw/) back. Simulated: C32 is 11.1 ns at y = 0.2 and 15.5 ns at y = 1.0 (x 0.288), F16 16.2 / 21.3
   ns; at 1% ring scatter the fit resolves y to +-0.01-0.02. The two routes must agree with each other within their
   sigmas; if they do not, that is the finding.

## 2026-11-21: item 44 -- the automatic flow's whole suite on the board: 46 kernels, one route each, one self-judging loop
Flow v10 (BDC_AUTO=1, nothing set per kernel) judged 46 of the 62 suite kernels (so far: some of its tasks are still resuming) PASS on rule-CLEAN routes in
simulation (draws of the delay model, the runt monitor, the C's answers). This item puts one route of each of those
kernels on the board, with the SAME vectors and the SAME judging rules as the simulation gate: a silicon check of the
whole automatic column at once. research/data/suite/board/suite_v10/ holds one spec per kernel (its lowest-seed clean
route; every spec's route rebuilt here byte for byte: the farm's sdf reproduced, the trimmed fasm pinned).
research/tools/suite/board_suite.sh runs, per kernel: board_rebuild.sh (exit 1 on any mismatch) -> the expected
results from the C exactly as suite_one.sh derives them for the gate (its own vector / oracle choice, read from
suite_one.sh) -> cells/hw/xsdb_bench_vec.tcl (the gate's host program, register for register: FIXED mode, 2 runs per
call, FCLK0 83.33 MHz, arrays filled through the host port and read back after each call) -> board_vec_judge.py (the
gate's rules: every call's result = the C's, the runs agreed, every run completed, every array = the C's).

44. **The suite on the board** -- unattended: the rebuilds take ~5-10 min per kernel (several hours in all, no board
    needed); the board is locked (hw/board.sh) only for each kernel's vector run (seconds to a few minutes: memory
    kernels fill their arrays word by word over JTAG). From the repo root:

        cells/verify/toolchain.sh    # must pass (sha256 6e5d224472232d5d)
        research/tools/suite/board_suite.sh research/data/suite/board/suite_v10 2>&1 | tee ~/board_suite_v10.log; echo "exit $?"

    Pass: the last line `board_suite: 46 of 46 kernels PASS`, exit 0. Each kernel's line says PASS k/n, FAIL (which call,
    what the C says against what the board said), or NOT RUN (why: a rebuild that did not reproduce the route, an
    oracle that did not run). Please send ~/board_suite_v10.log and ~/runs/bq_suite/*/board.log back. Prediction: 46 of 46
    PASS. Two routes to watch: collatz64 (formal's steer screen puts its loop-exit steer's tolerance at a path error of
    8 %: research/data/suite/board/screen_v10/), and the memory kernels' RAM setup lines (formal C's draws pass them
    all, min RAM setup >= 442 ps). xsdb_bench_vec.tcl has run against a mock bench only (cells/hw/test_bench_vec.sh): an
    ERROR line, a LAYOUT MISMATCH or "NOTHING TO JUDGE" on every kernel is the script's failure, not the kernels' --
    stop and send the first log. Dry run here without a board (BQ_MOCK=1 BQ_SKIP_REBUILD=1: the mock bench answers with
    the C's own results and arrays): 46 of 46 PASS -- every kernel's vector file (both formats, 0-2 operand words, 8- and
    32-bit arrays), its C oracle and the judge work end to end; the same run with one result corrupted, or with an
    array-writing kernel left unchanged, FAILS.
    **What a failure would mean:** the routes span a steer path-error tolerance of x = 0.045-0.42 (research/data/suite/
    board/screen_v10/census.md; the flow guards 3 %, formal's guide asks 10 %). The thinnest: fill, collatz64, twoloops,
    if_loop_2, dot2, sqrtsub, lfsrfind (x < 0.07 by rule E; collatz64 / sqrtsub / lfsrfind thin in formal's simulation
    too). Failures concentrated there say the steers need the wider guard; a failure elsewhere is a different defect.

## 2026-11-21: item 43 -- flow v10's xorshift (formal's proved plain loop-test move, the post-route trim): 16.35 ns, one command to rebuild
Flow v10 on 4 seeds, every route rule-CLEAN and PASS 4 / 4 draws: **xorshift P 16.35 / 15.22 / 16.36 / 15.07 ns (seeds
1-4, mean 15.75)**; item 41 (flow v3) is 20.11, the hand recipe (item 37) 16.49. Rebuilt as item 42 (board_rebuild.sh,
see there); nextpnr 6e5d224472232d5d.

43. **xorshift at ~16.4 ns per iteration, flow v10 seed 1 (formal's plain loop-test move; A35: the exact graph this build
   uses, research/data/autorw/xorshift.mlir under the spec's knobs, is PROVED to compute xorshift's C, one theorem)** --
   farm suite13t_s5a_v10_1a task 1, rebuilt here byte for byte: sdf fd959b30, trimmed fasm 78aa6ac3, P 16.35 ns
   (untrimmed 17.12), EQUIVALENT, ffmux-clean; the slower of its two middle seeds. **Strict gate here (GATE_RUNTS=fail,
   any x / RAMB18 event fails): worst, SLOW_MAX, FAST_MIN 19/19 each and 32 / 32 draws (K 42201-42232, xor19): 35 / 35
   PASS, 0 pulses under 1 ns, narrowest 1.4 ns.** Formal's B24 steer screen (run here; research/data/suite/board/
   screen_v10/): 16 / 16 steers bounded, min kappa_lo 0.091; its latch-fed steer race (ucond_br7, the kind B28 found on
   an earlier xorshift route) at +597 / +1492 ps, the race-only adversary finds no failure to kappa 0.20 (the flow's
   race check: 17.07 sd); no pulses below a path error of x = 0.25. From the repo root:

       cells/verify/toolchain.sh    # must pass (sha256 6e5d224472232d5d)
       research/tools/suite/board_rebuild.sh research/data/suite/board/xorshift_v10_s1.spec; echo "exit $?"   # must be 0
       cd cells
       hw/board.sh ${XSDB:-/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab/bin/xsdb} hw/xsdb_bench_vec.tcl \
         build/hw/xorshift_bench_gen/xorshift_bench_gen.bit ../research/data/eventgraph/gate/xor19.hex > build/hw/vec_xor_v10.log 2>&1
       python3 ../research/tools/suite/board_vec_judge.py ../research/data/eventgraph/gate/xor19.exp build/hw/vec_xor_v10.log; echo "exit $?"
       CLK=0x00100C00 hw/loop_cost.sh xorshift && cp build/hw/loop_cost_xorshift.tsv build/hw/lc_xor_v10.tsv
       (item 41's commands for build/hw/lc_xor_auto.tsv, if not already run; AFTER the line above: item 41's build_bench.sh
        writes the same cells/build/hw/xorshift_bench_gen/)
       python3 ../research/tools/loop_cost_judge.py xorshift build/hw/lc_xor_v10.tsv build/hw/lc_xor_auto.tsv; echo "exit $?"

   Pass: board_vec_judge.py `PASS 19/19`, exit 0 (the gate's own 19 vectors against the C; an ERROR line or exit 2 is the
   new script's failure, not the kernel's: send the log) AND loop_cost_judge.py `=== PASS ... ===`, exit 0. Predicted
   ratio over item 41 ~1.23 (20.11 -> 16.35 ns in simulation); expect ~15.0 ns on the board (sim ~8 % slow), about the
   hand recipe's. A FAIL with item 41 passing: send both logs and build/hw/_loop_xorshift_*.log.

## 2026-11-21: item 42 -- flow v10's collatz (formal's proved n == 2 exit test, the post-route trim): 14.5 ns, one command to rebuild
Flow v10 (BDC_AUTO=1, the loop's own sizes, formal's PROVED loop-test rewrites applied from a memo, the post-route trim,
the latch-fed race check; nothing set per kernel) on 4 seeds, every route rule-CLEAN and PASS 4 / 4 draws: **collatz
P 14.48 / 15.58 / 15.84 / 16.42 ns (seeds 1-4, mean 15.58)**; item 39 (flow v3) is 18.99. The route is TRIMMED after
routing (LUT INITs only), so build_bench.sh alone does not make its bits: research/tools/suite/board_rebuild.sh SPEC
runs the flow's own build (research/tools/fifteen/lane2.sh: the proved MLIR, the loop's sizes / seed / search knobs),
checks the route's sdf, applies the recorded trims, checks the trimmed fasm, writes the bitstream and puts it where
loop_cost.sh reads it; any mismatch exits 1 and copies nothing (a wrong-seed spec is refused: checked). The .bit md5
varies by build (its header carries a path), so the check is on the fasm. nextpnr 6e5d224472232d5d.

42. **collatz at ~14.5 ns per iteration, flow v10 seed 1 (formal's n == 2 exit test; A24 / A26 / A31: the chain from the
   C to this build's token graph is proved, and A31 checked these very bits: only the recorded trims differ)** -- farm
   suite13t_s5a_v10_1a task 2, rebuilt here byte for byte: sdf 0f050078, trimmed fasm 6ef8e077, P 14.48 ns (untrimmed
   15.83), EQUIVALENT, ffmux-clean. The fastest of its four seeds (seed 1 is the one formal proved). **Strict gate here
   (GATE_RUNTS=fail, any x / RAMB18 event fails): worst, SLOW_MAX, FAST_MIN 17/17 each and 32 / 32 draws (K
   42101-42132, col18): 35 / 35 PASS, 0 pulses under 1 ns on any kernel handshake net, narrowest 1.9 ns.** Formal's
   B24 steer screen (claude/formal 36ba04ea34, run here; research/data/suite/board/screen_v10/): no latch-fed race, no
   pulses up to a path error of x = 0.25 (first failure at 0.25); **formal B29 (07:27): all 12 steers bounded** (their
   tool fixed for ucond_br7's latch-fed condition: kappa_lo 0.110; the weakest stays ucond_br6 at 0.061), and **formal
   rebuilt this route with board_rebuild.sh independently: the same sdf, trimmed fasm and bit**. From the repo root:

       cells/verify/toolchain.sh    # must pass (sha256 6e5d224472232d5d)
       research/tools/suite/board_rebuild.sh research/data/suite/board/collatz_v10_s1.spec; echo "exit $?"   # must be 0
       cd cells
       hw/board.sh ${XSDB:-/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab/bin/xsdb} hw/xsdb_bench_vec.tcl \
         build/hw/collatz_bench_gen/collatz_bench_gen.bit ../research/data/eventgraph/gate/col18.hex > build/hw/vec_col_v10.log 2>&1
       python3 ../research/tools/suite/board_vec_judge.py ../research/data/eventgraph/gate/col18.exp build/hw/vec_col_v10.log; echo "exit $?"
       CLK=0x00100C00 hw/loop_cost.sh collatz && cp build/hw/loop_cost_collatz.tsv build/hw/lc_col_v10.tsv
       (item 39's commands for build/hw/lc_col_auto.tsv, if not already run; run them AFTER the line above has been
        copied aside: item 39's build_bench.sh writes the same cells/build/hw/collatz_bench_gen/)
       python3 ../research/tools/loop_cost_judge.py collatz build/hw/lc_col_v10.tsv build/hw/lc_col_auto.tsv; echo "exit $?"

   Pass: board_vec_judge.py `PASS 17/17`, exit 0 (the gate's own 17 vectors, judged by the gate's rules against the
   C: the same stimulus the 35 simulated runs above passed; added 05:28 with cells/hw/xsdb_bench_vec.tcl, tested on a
   mock bench only -- an ERROR line or exit 2 from it is the script's failure, not the kernel's: send the log) AND
   loop_cost_judge.py `=== PASS ... ===`, exit 0 (every point's oracle derived from the C, on both builds). Predicted ratio over item
   39 ~1.31 (18.99 -> 14.48 ns in simulation); the simulation runs ~8 % slow per iteration against the August board
   (research/SIM-VS-BOARD.md), so expect ~13.3 ns. A FAIL with item 39 passing is the first silicon counterexample to
   the proved-rewrite + trim flow: send both logs and build/hw/_loop_collatz_*.log.

## 2026-11-18: items 40 and 41 -- automatic collatz64 and xorshift (BDC_AUTO=1, the loop's own sizes)

40. **collatz64 at ~23.7 ns per iteration, automatic (BDC_AUTO=1, sizes from auto_size.sh flow v3, seed 5)** -- farm
   suite4: 5 automatic collatz64 routes, 40 / 40 draws, P median 23.71 ns (21.50-27.86); this rule-CLEAN route (loop
   clean at it 7) is the median: sdf 9585dde4, P 23.71 ns, EQUIVALENT, ffmux-clean; SLOW_MAX / FAST_MIN / worst 18/18
   each and **32 / 32 draws** (K 30501-30532, c6419). bdc/auto.py applies the proven n == 2 exit test (pre_eq2, formal
   A6) by itself. Sizes: research/data/suite/board/collatz64_v3_s5_sizes.vh (the loop's sizes_final.vh, nothing
   edited). Hand: item 32, 31.4 ns; item 26 (full range), 36.2. Built on the farm with nextpnr 9c732bc6303458df; rebuilt
   on the cluster with 6e5d224472232d5d, the same sdf. From cells/:

       BDC_AUTO=1 BDC_AUTO_REWRITES=1 BDC_RING_FUSE=0 NEXTPNR_SEED=5 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/suite/board/collatz64_v3_s5_sizes.vh ./hw/build_bench.sh collatz64
       md5sum build/hw/collatz64_bench_gen/collatz64_bench_gen.sdf    # 9585dde4 = the route judged here
       python3 ../research/tools/ffmux_scan.py build/hw/collatz64_bench_gen/collatz64_bench_gen.fasm; echo "exit $?"   # must be 0
       CLK=0x00100C00 hw/loop_cost.sh collatz64 && cp build/hw/loop_cost_collatz64.tsv build/hw/lc_c64_auto.tsv
       (item 26: #27's commands for lc_c64_eq.tsv, if not already run)
       python3 ../research/tools/loop_cost_judge.py collatz64 build/hw/lc_c64_auto.tsv build/hw/lc_c64_eq.tsv; echo "exit $?"

   Pass: `=== PASS ... ===`, exit 0 (every point's derived oracle). Predicted ratio over item 26 ~1.53 (36.27 ns on its
   board route vs 23.71 here); the simulation runs ~8 % slow per iteration against the August board, so expect ~21.8 ns.
   A FAIL with item 26 passing is the automatic flow's silicon counterexample: send both logs.

41. **xorshift at ~20.1 ns per iteration, automatic (BDC_AUTO=1, sizes from auto_size.sh flow v3, seed 8)** -- farm
   suite4: 7 automatic xorshift routes, 56 / 56 draws, P median 20.11 ns (18.87-20.49); this rule-CLEAN route (loop clean
   at it 6) is the median, on the seed where flow v1 failed a draw (the zero-trip call; v3's entry compare is longer):
   sdf 3497ca67, P 20.11 ns, EQUIVALENT, ffmux-clean; SLOW_MAX / FAST_MIN / worst 19/19 each, **32 / 32 draws** (K
   30801-30832, xor19) and **8 / 8 slow-carry draws** (K 30851-30858, CARRY4 / F7F8 / FF at 0.8-1.0 of the band).
   bdc/auto.py applies the proven loop-test rewrite (pre_dec, formal A6) by itself. Sizes:
   research/data/suite/board/xorshift_v3_s8_sizes.vh (nothing edited). The hand recipe is faster on xorshift (item 37,
   16.49 ns): this item is here as the automatic flow's own xorshift, not as the fastest one. nextpnr as item 40. From cells/:

       BDC_AUTO=1 BDC_AUTO_REWRITES=1 BDC_RING_FUSE=0 NEXTPNR_SEED=8 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/suite/board/xorshift_v3_s8_sizes.vh ./hw/build_bench.sh xorshift
       md5sum build/hw/xorshift_bench_gen/xorshift_bench_gen.sdf    # 3497ca67 = the route judged here
       python3 ../research/tools/ffmux_scan.py build/hw/xorshift_bench_gen/xorshift_bench_gen.fasm; echo "exit $?"   # must be 0
       CLK=0x00100C00 hw/loop_cost.sh xorshift && cp build/hw/loop_cost_xorshift.tsv build/hw/lc_xor_auto.tsv
       (item 33: #34's commands for lc_xor_a.tsv, if not already run)
       python3 ../research/tools/loop_cost_judge.py xorshift build/hw/lc_xor_auto.tsv build/hw/lc_xor_a.tsv; echo "exit $?"

   Pass: `=== PASS ... ===`, exit 0. Predicted ratio over item 33 ~0.93 (18.71 ns on its board route vs 20.11 here: the
   automatic xorshift is slower than the hand recipe); expect ~18.5 ns on the board. A FAIL with item 33 passing is the
   automatic flow's silicon counterexample: send both logs.

## 2026-11-18: item 39 -- automatic collatz (BDC_AUTO=1, the loop's own sizes): 18.99 ns, faster than every hand collatz item

39. **collatz at ~19.0 ns per iteration, automatic (BDC_AUTO=1, sizes from auto_size.sh flow v3, seed 6)** -- farm suite4:
   7 automatic collatz routes, 56 / 56 draws, P median 18.98 ns (17.71-20.60); this rule-CLEAN route is the median:
   sdf c56def07, P 18.99 ns, EQUIVALENT, ffmux-clean; SLOW_MAX / FAST_MIN / worst 17/17 each and **32 / 32 draws**
   (K 30601-30632, col18). bdc/auto.py applies the proven n == 2 exit test (pre_eq2, formal A6) by itself. Sizes:
   research/data/suite/board/collatz_v3_s6_sizes.vh (the loop's sizes_final.vh, nothing edited). Hand: item 31, 21.5 ns.
   Built on the farm with nextpnr 9c732bc6303458df; rebuilt here with 6e5d224472232d5d, identical. From cells/:

       BDC_AUTO=1 BDC_AUTO_REWRITES=1 BDC_RING_FUSE=0 NEXTPNR_SEED=6 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/suite/board/collatz_v3_s6_sizes.vh ./hw/build_bench.sh collatz
       md5sum build/hw/collatz_bench_gen/collatz_bench_gen.sdf    # c56def07 = the route judged here
       python3 ../research/tools/ffmux_scan.py build/hw/collatz_bench_gen/collatz_bench_gen.fasm; echo "exit $?"   # must be 0
       CLK=0x00100C00 hw/loop_cost.sh collatz && cp build/hw/loop_cost_collatz.tsv build/hw/lc_col_auto.tsv
       (item 25: #26's commands for lc_col_eq.tsv, if not already run)
       python3 ../research/tools/loop_cost_judge.py collatz build/hw/lc_col_auto.tsv build/hw/lc_col_eq.tsv; echo "exit $?"

   Pass: `=== PASS ... ===`, exit 0. Predicted ratio over item 25 ~1.89 (35.92 ns on its route vs 18.99 here; the
   simulation runs ~8 % slow per iteration against the August board, so expect ~17.5 ns). A FAIL with item 25 passing is
   the automatic flow's silicon counterexample: send both logs.

## 2026-11-18: item 38 -- the FIRST AUTOMATIC build: ipow with BDC_AUTO=1 and the flow's own sizes (nothing set by hand)
PROGRAM "General first": one switch, no sizes chosen per kernel. This route came out of the automatic sizing loop
(research/tools/auto/auto_size.sh, flow v3) on the farm (suite4) and was rebuilt here byte for byte. It is faster than
every hand ipow item (item 29: 36.2 ns median; item 30's route 35.54).

38. **ipow at ~22.7 ns per iteration, automatic (BDC_AUTO=1, sizes from auto_size.sh flow v3, seed 2)** -- farm suite4:
   8 automatic ipow routes, 64 / 64 draws, P median 24.10 ns (21.47-25.00); this one is a rule-CLEAN route near the
   median: sdf 81bbe268, P 22.71 ns, EQUIVALENT, ffmux-clean; SLOW_MAX / FAST_MIN / worst 17/17 each and **32 / 32
   draws** (K 30201-30232, ipow17). Sizes: research/data/suite/board/ipow_v3_s2_sizes.vh (the loop's sizes_final.vh;
   nothing edited). nextpnr: built on the farm with 9c732bc6303458df; the rebuild with 6e5d224472232d5d is identical
   (no missed GND pin on this route). From cells/:

       BDC_AUTO=1 BDC_RING_FUSE=0 NEXTPNR_SEED=2 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/suite/board/ipow_v3_s2_sizes.vh ./hw/build_bench.sh ipow
       md5sum build/hw/ipow_bench_gen/ipow_bench_gen.sdf    # 81bbe268 = the route judged here
       python3 ../research/tools/ffmux_scan.py build/hw/ipow_bench_gen/ipow_bench_gen.fasm; echo "exit $?"   # must be 0
       CLK=0x00100C00 hw/loop_cost.sh ipow && cp build/hw/loop_cost_ipow.tsv build/hw/lc_ipow_auto.tsv
       (item 19: #20's commands for lc_ipow_r.tsv, if not already run)
       python3 ../research/tools/loop_cost_judge.py ipow build/hw/lc_ipow_auto.tsv build/hw/lc_ipow_r.tsv; echo "exit $?"

   Pass: `=== PASS ... ===`, exit 0 (every point's derived oracle). Predicted ratio over item 19 ~1.75 (39.78 ns on its
   route vs 22.71 here); the simulation runs ~8 % slow per iteration against the August board, so expect ~21 ns. A FAIL
   with item 19 passing is the automatic flow's first silicon counterexample: send both logs -- it is the most useful
   thing this list can return.

## 2026-11-18: item 37 -- xorshift x55a10 (item 35 with formal's entry-compare fix), the hand recipe's best; the automatic builds come next
Under PROGRAM "General first" this is the HAND column (per-kernel sizes chosen by draws). The automatic builds (BDC_AUTO=1,
sizes from the flow's own loop, research/data/suite/) are being judged on 8 seeds each (farm suite4 / suite5 / suite3);
the first of them goes here when its route has the same depth of evidence as this one (32 draws + 3 corners).

37. **xorshift x55a10 at ~16.5 ns per iteration: item 35's sizes with the entry compare UCMPI0 6 -> 10** (formal C41: at
   the slow end of the CARRY / F7 band item 35's loop-entry steer keeps ~0.2 ns; UCMPI0 10 keeps >= 0.9 ns, C48 / C49).
   research/data/xorshift_sizes_T3s50_fr4a_x55a10_bench.vh; flags as item 35; NEXTPNR_SEED=21; nextpnr 9c732bc6303458df.
   Farm cand3b: 28 EQUIVALENT routes, 200 / 200 draws (incl. 96 with CARRY / F7 / FF at 0.8-1.0), P median 16.76 ns
   (15.73-18.55). This route (rebuilt on the cluster = the farm's route 21 byte for byte): sdf 42b4fb4c, P 16.49 ns,
   EQUIVALENT, ffmux-clean; SLOW_MAX / FAST_MIN / worst 19/19 each and **32 / 32 draws** (K 2101-2132, xor19). Formal on
   this route (RC arcs): entry / loop-test settle >= 1425 / 923 ps at chains 0.20, rest 0.31, CARRY 1.0, no runts (C48);
   full-range runs with the counter preloaded pass (B5). From cells/:

       cp ../build/frontend/xorshift/comp/handshake_transformed.mlir /tmp/xor_hs_orig.mlir
       cp ../research/data/fifteen/xorshift_predec.mlir ../build/frontend/xorshift/comp/handshake_transformed.mlir
       BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 NEXTPNR_SEED=21 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/xorshift_sizes_T3s50_fr4a_x55a10_bench.vh ./hw/build_bench.sh xorshift
       cp /tmp/xor_hs_orig.mlir ../build/frontend/xorshift/comp/handshake_transformed.mlir
       md5sum build/hw/xorshift_bench_gen/xorshift_bench_gen.sdf    # 42b4fb4c = the route judged here (the .bit md5 varies by build time)
       python3 ../research/tools/ffmux_scan.py build/hw/xorshift_bench_gen/xorshift_bench_gen.fasm; echo "exit $?"   # must be 0
       CLK=0x00100C00 hw/loop_cost.sh xorshift && cp build/hw/loop_cost_xorshift.tsv build/hw/lc_xor_x55a10.tsv
       (item 33: #34's commands for lc_xor_a.tsv, if not already run)
       python3 ../research/tools/loop_cost_judge.py xorshift build/hw/lc_xor_x55a10.tsv build/hw/lc_xor_a.tsv; echo "exit $?"

   Pass: `=== PASS ... ===`, exit 0 (every point's derived oracle). Predicted ratio over item 33 ~1.13 (18.71 -> 16.49 on
   their board routes); the simulation runs ~8 % slow per iteration against the August board (SIM-VS-BOARD.md), so the
   board should show ~15.2 ns. Run it INSTEAD of item 35 (same structure, the entry compare made safe). A FAIL with
   item 33 passing means the draws' model is too generous on this die: send both logs.

## 2026-11-17: (withdrawn) hold on items 28, 31, 30, 32
A hold placed at 05:2x UTC is WITHDRAWN: the "wrong step counts" came from vectors above the bench's input mask
(collatz n is masked to 16 bits by gen_bench.py; the kernel returned collatz(n & 0xFFFF), which is right). Item 31's route
on the out-of-domain vectors returned exactly collatz(n & 0xFFFF) for all three. Farm regate3 re-gates the four families
with the highest-peak inputs INSIDE the mask (col18, c6419); the items stand on their earlier evidence meanwhile.

## 2026-11-16 (night): the board candidates judged by draws (PROGRAM "The board decides")
Each candidate's board route simulated over draws of the parametric delay model (bench_gate.sh draw:K: delay chains and
everything else each at a band drawn uniformly in [0.20, 0.31], CARRY4 / F7F8 / FF in [0.20, 1.0], setting M within-die
scatter), the bits-decoded netlist, the fixed verdict (every run of every batch right). Model error on the August
builds: the simulation at the ring band 0.288 runs 8-10% slower per iteration than the board (collatz, collatz64, ipow,
gcd; research/SIM-VS-BOARD.md), so the ns below are likely ~8% high. The model fails its known-bad build (a steer
condition 8 ns late) on 16 / 16 draws.

| item | kernel | ns / iteration (median of farm routes, sim at 0.288) | draws passing on the board route |
|---|---|---|---|
| 33 (fxa s27) | xorshift | 18.9 | 32 / 32 |
| 27 (fxd s2) | xorshift | 19.4 | 32 / 32 |
| 31 (fcsel3a s20) | collatz | 21.5 | 32 / 32 |
| 28 (fcsel3m s20) | collatz | 25.8 | 32 / 32 |
| 29 (fisel3m s19) | ipow | 36.2 | 24 / 24 |
| 30 (fc64sel3 s10) | collatz64 | 35 | 32 / 32 |
| 32 (fc64sel3p s22) | collatz64 | 31.4 | 32 / 32 |

| 35 (fr4a_x55a s21) | xorshift | 16.85 (32 routes, all draws passing: 128 / 128) | 32 / 32 + 6 / 6 corner gates |
| 37 (x55a10 s21) | xorshift | 16.76 (28 EQUIVALENT routes, 200 / 200 draws incl. 96 slow-carry) | 32 / 32 + 3 / 3 corners |
| 38 (AUTOMATIC, v3 s2) | ipow | 24.10 (8 automatic routes, 64 / 64 draws); this route 22.71 | 32 / 32 + 3 / 3 corners |
| 39 (AUTOMATIC, v3 s6) | collatz | 18.98 (7 automatic routes, 56 / 56 draws); this route 18.99 | 32 / 32 + 3 / 3 corners |

Item 35 is the first chosen by the draws (sizes shortened while every draw passes; first failure at x0.40a).

## 2026-11-16 (evening): the GLS gate checked only the LAST run of each batch -- every "gate N/N" before today is partial
bench_gate.sh judged a batch by its last run's odata and its completion count. The bench also latches whether the
batch's runs disagreed (mism_st bit 0, FIXED-mode repeatability); the gate never read it. A build whose result stream
falls one call behind (a stray token from a mis-steer) returns the previous call's answer on each batch's first run and
the right one on its second, and passed. Seen: a constructed late entry condition on xorshift (16 of 19 batches), and 5
farm steerneg runs judged PASS. Fixed (a disagreeing batch fails). The board script (xsdb_bench_gen.tcl) always
asserted it, so no board judge is affected. Re-gated with the fixed verdict: items 27 / 29 / 33 families (farm
regate1: fxa 168, fxd 168, fisel3m >= 78 gate runs, all PASS), items 28 / 31 / 30 / 32 (farm zt1): no mismatch on any
clean route. Items before 23 were judged by other harness scripts; not re-checked.

## 2026-11-16 (evening): the collatz / collatz64 gates never ran n = 1 (zero-trip) -- items 28, 31, 30, 32 re-gating
The gate vectors col13 / c6414 have no n = 1, so on every call the loop-entry test came out the same and the gate never
judged the loop-ENTRY steers (a late entry condition passed every gate on the farm, steerneg). collatz(1) = 0 is in the
full input range. New vectors col14 / c6415 (n = 1 second; oracle compiled from kernels/*.c, kernel_oracle.sh). Farm zt1
re-gated the four families (32 routes x 3 corners): **every clean route PASSES with n = 1, no run-to-run mismatch**
(the one failure is fcsel3a seed 10, the known 5FF-D defect route). The entry-steer control passes on the old vectors
and fails with n = 1 on items 28, 30, 32's board seeds: the gap was real, and is closed. xorshift
and ipow vectors do contain a zero-trip call (rounds 0 / e 0), but only as the FIRST call (see JOURNAL: an entry-steer
glitch at a loop-entering call leaves a stray token on the skip path that only a LATER zero-trip call would read).

## 2026-11-16: rule M (new) -- the bd_mux data outputs were never checked; items 27, 29, 30, 32 have misses
corner_audit now checks every bd_mux's 32 / 64 data outputs against its output request (rule M, the A rows marked
"peers no common source reaches"; JOURNAL 2026-11-16). Before, tighten's rule A paired the request with a trivial peer
and never measured the data outputs, so the mux delays (BD_SZ_*_UMUXn) were sized to nothing. On each board family's
32 routes: **collatz item 31: no miss** (28 too). **xorshift item 27**: umux0/1/2 on 23/29 routes, to -734 ps (board
seed 2: umux1 -13 nom / -117 worst). **ipow item 29**: umux2 on 15/19, to -780 (its first board seed 19: -279 / -382) -- FIXED 2026-11-16: item 29 is now fisel3m (mux delays sized by M), static-clean on 27/27.
**collatz64 items 30 / 32**: umux0 on 32/32, -0.6 to -2.4 ns (item 30's seed 10: -1231 / -1321). Every gate passes.
Measured in simulation on item 30's route (FAST_MIN): the data changes after the request on 352 of 458 tokens, by up to
155 ps; consumers are link latches, so the cost is a later Q downstream, which no check accounts for. Treat items
30, 32 (and 27 at its small margin) as provisional until either the downstream margins are shown to absorb the
measured lateness or the mux delay is padded (farm fc64sel3m: collatz64 with umux0 padded to M, running).
At the worst corner the same route shows 300 of 458 tokens late by up to 60 ps; item 31's route (M clean) shows none
(data leads z_req by >= 1.6 ns). Rule M's known-bad builds: SDF injections on the select -> data-LUT arcs give wrong
values / no completion at FAST_MIN on collatz, xorshift and ipow with M < 0 and rule E clean (farm mneg, JOURNAL).
Items 1-26 were never checked by rule M either; their mux delays mostly come from the same unchecked rounds.

## Full-input-range status (owner rule 2026-11-14; research/JOURNAL.md 2026-11-14)

**2026-11-15 (evening) CORRECTION: rule E rows on muxes and steers were never read.** eval_task.sh's static summary
matched the instance in field 3 of each report row; rule E rows put the cell type there (`E -255 bd_mux <inst>`), so
no E row of a bd_mux or bd_steer ever reached eval.txt since 2026-11-14. Every "static A / A' / E clean" below for
items 22-27 means A and A' only. Found on a select-shortened collatz route (umux0/1/2 E -87..-255 ps at worst).
Re-check of every item family's routes running on the farm (requests *S, report_rows_*.txt keep every row); until it
is back, the E status of items 19 and 22-27 is UNKNOWN.
Back so far: item 26 (fc64eq family) -- its board seed 25 has no E row; 2 of 30 routes have steer E rows (-191, -250 ps
worst). Item 24 (fc64nl family): no E row on 29 routes.
Item 25 (fceq family, nl4): no E row on 28 routes; nl6 (fceq2): none on 30; collatz64 h4 (fc64eq3): none on 32; item 22
(fcolsz2): none on 29. 
**2026-11-16: the re-check is complete.** Item 23 (fxf4 family): no E row on 29 routes. Item 27 (fxd family): one E row
on 32 routes (seed 27, steer ucond_br8 -118 ps at worst); its board seed 2 has none. Item 19 (ipowrh family): no E row
on 28 routes (its rule A rows are umux3's traced false path, as recorded); ipow h4: none on 32. So no board item's own
route has a rule E row; the E status of items 19 and 22-27 is now KNOWN and clean on each board seed.

**2026-11-15 (later): the hold rows are being closed by pad rounds on 32 routes per family.** Every route clean of H / I
rows (non-defect routes): collatz n == 2 with nl6 (fceq2, 30/30), ipow with h4 (fipowh4, 23/23), xorshift lever 8 with
fr6d (fxd3, 28/28; one uxori1 A -240 ps row on seed 22), collatz64 n == 2 with h4 (fc64eq3, 28/28, umux2's traced
false-path row aside; +0.42 ns vs h2). Board seeds of
items 25-27 are clean on their own routes already, and were re-checked locally with the default OR-join model.

**2026-11-15: hold / capture (rules H / I) NOT checked until now -- items 19, 22, 23, 24 are not statically clean.**
Rule H flagged the xf2_1 corruption (H ulink_n7 -439 ps at FAST_MIN) but no gate or summary read H / I rows. On item
23's own route (xorshift seed 10, worst corner): H -274 (ulink_n7), -107, -103, -1, I -85; similar rows on the
collatz64 and ipow routes. Their gates pass (the data has to move inside the window to corrupt), so they are not known
to fail; they are not shown safe. Re-gating with the pads (research/tools/fifteen/hold_pads.py): xorshift sizes fr4,
farm fxf5 / fxs5. Until then load these items only as "gate-clean, hold margin negative at nominal / worst".

A gate pass does not cover paths the vectors cannot reach (loop counters and their compares). The static check: rules
A / A' / E at nominal (uniform 0.288) and at the gate's worst corner, measured-residual guards (corner_audit.py).
- **Bench range only (fail the static check on the counter):** every x0.5 xorshift item -- list items 4, 11, 14, 17 (and
  18, on hold). On item 17's route the counter's i+1 (uaddi0, 6 elements) needs 13 at the worst corner (A' -752 ps on
  s1). They are correct for the board bench (rounds masked to 12 bits) as far as the gate shows, not for every rounds.
  The full-range version of item 17 is item 23 (#24).
- **ipow item 19 (route a6a2951b):** the loop variable e is spanned by the gate's vectors (e up to 2^31-1); the static
  check finds only umux3 (the result mux) rule A -1.7 ns at both corners, on data the gate toggles. Full range by the
  rule. The 1.7 ns is a false path, shown with a trace (JOURNAL 2026-11-14): the select latch's data is timed against a
  request that waits for the select link's own request (3.4 ns later); traced on 12 transactions with the select
  flipping, the output request rises >= 3.6 ns after the last data change. Hold check (2026-11-14): no violation once the tool measures a pipe stage's
  close at its C node (seed 8, the worst of the earlier readings: +782 ps; the earlier -1..-247 ps flags were the
  tool's error, JOURNAL).
- **collatz64 (6, 12, 16, 21) and the lever-5 candidate:** umux2 misses rule A by 1.3-2.5 ns at nominal on every
  route; shown to be the same select-latch false path by trace (JOURNAL 2026-11-14). Lever-5 candidate (fc64nl, farm):
  30 routes, median 45.21 ns, gate 90/90; otherwise statically clean. Not yet a board item (gcd's counters next).
- **gcd (#5's route, 2026-11-14):** rules A' / E clean at nominal; at worst only ushrsi4 A' -359 ps, a shift of a / b,
  which the 1000 random 32-bit vectors span; no counter in gcd. Full range by the rule (items 1-3 share the structure).
- **Not yet checked:** ipow (7, 13), collatz (9, 15, 20) -- older items superseded by 19 and 22. Collatz item 22 (#23) is full
  range (static clean on 27/27 routes). Until checked,
  read each as bench range only.

## Board list, in order (owner, 2026-11-04: best first; each item judges itself)
1. **gcd_ps with the 1000 vectors** (item #4 below): `hw/board.sh xsdb hw/xsdb_gcd.tcl ../research/board/gcd_ps_e6bb4aec.bit
   ../research/board/gcd_ps_vec1000.hex; echo "exit $?"`. Pass: `=== PASS 1000/1000 ===` and exit 0. Also gives
   per-call latency directly comparable with the full stack's (research/data/gcd_ps/cost_model_vs_board.tsv).
2. **The short-pulse C-element test (H_RUNT)**: research/board/runt/ (runt_top, bit 08529a39; predictions committed
   before any run; README there). 96 C-element loops forced by episodes of routed width -427..+1542 ps against their own
   211-633 ps loops, plus NEG/LONG/PULSE controls. From cells/:

       mkdir -p build/hw/runt_top && cp ../research/board/runt/runt_top.bit ../research/board/runt/instances.tsv build/hw/runt_top/ && \
         xz -dc ../research/board/runt/runt_top_routed.json.xz > build/hw/runt_top/runt_top_routed.json && \
         python3 hw/runt_measure.py; echo "measure exit $?"
       python3 ../research/tools/runt_judge.py build/hw/runt_top/runt_measured.tsv ../research/board/runt/predicted.tsv; echo "judge exit $?"

   Pass: measure prints `=== RIG OK ===` and exits 0 (every control in every trial: NEG never captures, LONG always,
   PULSE k=3 counts an edge every trial), and the judge prints `=== PASS: ... ===`, exit 0 (a capture threshold w* can
   be named). The answer is in the lines after: `=== RUNT CIRCULATES ===` (any TEST cell with >= 2 rising edges in a
   trial) or not, and w* - loop. RIG FAIL means the rig, not the fabric, and nothing else is read.
   **What it decides now (2026-11-20):** the races our routes lose in simulation put 19-60 ps pulses into C-elements
   (formal B21 replayed here: 271 pulses of 19 ps; formal C68's spmv route: 72-420 pulses of >= 56 ps in 4 of 8 of our
   draws). Our GLS absorbs them and answers right; formal's simulator lets them through and hangs. A capture threshold
   w* below ~60 ps means such routes hang on silicon. Every route counted as passing has none (research/data/fifteen/
   README.md top), so the answer changes no claim, only which simulator is the board's.
3. **The fastest gcd the sim accepts**: #5 below (gcd_hw R5 sizes x0.75 + link fast fall, PROGRAM item 3): the
   combined worst-case gate (matched-delay chains 0.21, CARRY4/F7F8/FF SLOW_MAX, the rest 0.288, + the measured residual
   as scatter) 8/8 routes, and SLOW_MAX and FAST_MIN 16/16 runs, every run 16/16 errs=0 (research/data/item3/
   s75ff_worstcase.tsv, s75ff_corners.tsv). Worst-case laps 1.13x #2's on the same 8 routes, 1.08x #3's. Fallback: #3
   (BQ#3), then #2. Commands and criteria under #5.
4. **xorshift with every matched delay halved (x0.5), on the kernel bench**: #6 below. Both builds (x0.5 and its T3
   base) through the full stack on the bench top itself (netlist from each .bit, PS7 host model): 48/48 runs pass,
   8 routes x SLOW_MAX/FAST_MIN/worst case each, 17/17 vectors every run. Predicted 1.28-1.52x per round (1.47-1.49
   on the route the board builds). One judge:
   `python3 ../research/tools/xorshift_bench_judge.py build/hw/xorshift_cost_s50.tsv build/hw/xorshift_cost_t3.tsv`.
5. **A ring set on a second route (band transfer)**: research/board/ro_many_2/ (today's ro_many_top, bit 8dc4f1ac,
   predictions committed before any run). From cells/:

       mkdir -p build/hw/ro_many_top && cp ../research/board/ro_many_2/ro_many_top.bit build/hw/ro_many_top/ && \
         for f in ro_many_top_routed.json ro_many_top.sdf; do xz -dc ../research/board/ro_many_2/$f.xz > build/hw/ro_many_top/$f; done && \
         RO_MEAS_TSV=build/hw/ro_many_top/measured.tsv python3 hw/ro_many_measure.py; echo "measure exit $?"
       python3 ../research/tools/ring2_judge.py build/hw/ro_many_top/measured.tsv ../research/board/ro_many_2/predicted.tsv; echo "judge exit $?"

   Pass: measure exit 0 (the readback's own checks) and the judge's `=== PASS ===`, exit 0 (median and per-length
   median error of the 0.288 prediction within +/-5%, every ring inside its FAST_MIN..SLOW_MAX). The judge was
   checked on the first route's data: 0.288 PASS, 0.38 FAIL. A FAIL with every ring inside the corners means the band
   does not transfer between routes (the judge prints this route's own x).
6. **collatz64 with every matched delay at x0.75, on the kernel bench**: #7 below. 24/24 full-stack runs on 8 bench
   routes (3 corners, 14/14 vectors), predicted 1.17x per iteration (1.07-1.22 over 7 paired routes; 1.17-1.19 on the
   route the board builds). One judge: `python3 ../research/tools/loop_cost_judge.py collatz64 build/hw/lc_s75.tsv
   build/hw/lc_t4.tsv`.
7. **ipow with every matched delay at x0.75, on the kernel bench**: #8 below. 48/48 full-stack runs (both builds, 8 good
   routes x 3 corners, 17/17 vectors; 2 of 18 routes carry the F7-select defect), predicted 1.16-1.18x per iteration
   (1.08-1.26). Judge: `python3 ../research/tools/
   loop_cost_judge.py ipow build/hw/lc_ipow_s75.tsv build/hw/lc_ipow_t9.tsv`.
8. **[ON HOLD 2026-11-11: its per-cell sizes shorten umux1/umux0 select paths (ulink_n14__0 18->11, ulink_n14__1 36->18, umux0 6->1), the class that failed collatz64; item 9 replaces it]** **collatz with per-cell sizes, on the kernel bench**: #9 below. 48/48 full-stack runs (both builds, 8 routes x 3
   corners, 13/13 vectors), predicted 1.19-1.21x per iteration (1.12-1.33). Judge: `python3 ../research/tools/
   loop_cost_judge.py collatz build/hw/lc_collatz_cs.tsv build/hw/lc_collatz_t3.tsv`.
9. **collatz with the shift-by-one read as a literal (BDC_CONST_DATA=1), select-safe per-cell sizes, on the kernel bench**:
   #10 below. 24/24 full-stack runs (8 routes x 3 corners, 13/13 vectors), predicted 1.17-1.19x per iteration over
   T3 (1.13-1.25). Replaces the earlier T3cd version (held: shortened select links). Judge: `python3 ../research/tools/
   loop_cost_judge.py collatz build/hw/lc_collatz_cd.tsv build/hw/lc_collatz_t3.tsv`.
10. **[WITHDRAWN 2026-11-11: the select-safe re-gate (24/24, research/data/ipow_cde_bench) is 1.16-1.19x over T9 but 0.99-1.02x of item 7, so it adds nothing to the list]** **ipow with the shift-by-one read as a literal (BDC_CONST_DATA=1) + its per-cell sizes, on the kernel bench**:
   #11 below. 24/24 full-stack runs (8 routes x 3 corners, 17/17 vectors), predicted 1.24-1.27x per iteration over
   T9 (1.20-1.31) and 1.06-1.10x over item 7. Judge: `python3 ../research/tools/loop_cost_judge.py ipow
   build/hw/lc_ipow_cd.tsv build/hw/lc_ipow_t9.tsv`.
11. **xorshift x0.5 with a second latch at umux1's and the merge's handshake couplings, on the kernel bench**: #12
   below. Full gate: soak top 24/24 on 8 routes; bench top 23/24 + the 24th traced to the harness at 100 MHz and
   passing at 83.3. Predicted 1.25-1.27x per round over item 4's x0.5 (1.18-1.36). Judge: `python3 ../research/tools/
   loop_cost_judge.py xorshift build/hw/lc_xor_p8mo.tsv build/hw/lc_xor_s50.tsv`.
12. **collatz64 with the shift-by-one read as a literal (BDC_CONST_DATA=1), select-safe per-cell sizes, on the kernel
   bench**: #13 below. 24/24 full-stack runs, predicted 1.22-1.23x per iteration over T4 (1.14-1.35) and 1.03-1.05x
   over item 6. Judge: `python3 ../research/tools/loop_cost_judge.py collatz64 build/hw/lc_cd.tsv build/hw/lc_t4.tsv`.
13. **ipow x0.75 + link fast fall + a latch on the merge's output (BDC_LINK_FASTFALL=1, BDC_MERGE_OUT_LINK=ucontrol_merge0),
   chosen by the event graph (research/data/eventgraph), on the kernel bench**: #14 below. Full gate 24/24 on 8 good
   bench routes. Predicted 1.18-1.19x per iteration over item 7 on this route (1.15-1.20 over 4). Judge: `python3
   ../research/tools/loop_cost_judge.py ipow build/hw/lc_ipow_fm.tsv build/hw/lc_ipow_s75.tsv`.
14. **xorshift x0.5 + the second latch (item 11's knobs) + link fast fall (BDC_LINK_FASTFALL=1), chosen by the event
   graph, on the kernel bench**: #15 below. Full gate 24/24 on 8 good bench routes. Predicted 1.34x per round over item
   4's x0.5 on this route (1.22-1.45 over 8 routes) and ~1.07x over item 11. Judge: `python3 ../research/tools/
   loop_cost_judge.py xorshift build/hw/lc_xor_pmf.tsv build/hw/lc_xor_s50.tsv`.
15. **collatz with the shift read as a literal + select-safe per-cell sizes (item 9) + link fast fall + a latch on the
   merge's output (BDC_LINK_FASTFALL=1, BDC_MERGE_OUT_LINK=ucontrol_merge0), chosen by the event graph, on the kernel
   bench**: #16 below. Full gate 24/24 on 8 bench routes. Predicted 1.13x per iteration over item 9 on this route
   (1.13-1.23 over 8). Judge: `python3 ../research/tools/loop_cost_judge.py collatz build/hw/lc_col_fm.tsv
   build/hw/lc_col_cdb.tsv`.
16. **collatz64 item 12 + link fast fall + a latch on the merge's output (BDC_LINK_FASTFALL=1, BDC_MERGE_OUT_LINK=
   ucontrol_merge0), chosen by the event graph, on the kernel bench**: #17 below. Full gate 24/24 on 8 bench routes.
   Predicted 1.20x per iteration over item 12 on this route (1.13-1.21 over 8). Judge: `python3 ../research/tools/
   loop_cost_judge.py collatz64 build/hw/lc_c64_fm.tsv build/hw/lc_cd.tsv`.
17. **xorshift at ~20.6 ns per iteration: item 14 + three new opt-in bdc knobs (BDC_MERGE_RES_LINK, BDC_RING_COUNT_OLINKS,
   BDC_FORK_OUT_LINK), the 15 ns lead's levers 1-3 (research/data/fifteen), on the kernel bench**: #18 below. Full gate
   24/24 on 8 bench routes. Predicted 1.47x per round over item 14 on this route (1.33-1.55 over 8), 1.97x over item 4.
   Judge: `python3 ../research/tools/loop_cost_judge.py xorshift build/hw/lc_xor_l3.tsv build/hw/lc_xor_s50.tsv`.
18. **[ON HOLD 2026-11-13: static bundling violation the gate cannot exercise -- rule E at the loop-exit steer ucond_br6 is
   -4.65 ns RAW at the nominal nextpnr SDF (item 17's route: +1.70), -3.2 ns at the worst corner with the measured-residual
   guards (corner_audit). Without ulink_n30__1 the steer's select is the add+compare carry path from ulink_n7, longer than
   the matched add+compare delay when the counter carries far; the gate's vectors run <= 1000 rounds (carries <= 10 bits).
   rounds above ~1024 are not covered by any check. Do not run until fixed; item 17 is the xorshift board candidate.]**
   **xorshift at ~18.7 ns per iteration: item 17 + the rule-1 link between the loop increment and the compare dropped
   (BDC_NO_LINK=ulink_n30__1), the 15 ns lead's lever 5, on the kernel bench**: #19 below. Full gate 24/24 on 8 bench
   routes. Predicted 2.12x per round over item 4 on this route (1.92-2.25 over 8), ~1.08x over item 17. Judge: `python3
   ../research/tools/loop_cost_judge.py xorshift build/hw/lc_xor_l5.tsv build/hw/lc_xor_s50.tsv`.
19. **ipow item 13 + a latch on the merge fork's result branch (BDC_MERGE_RES_LINK=ucontrol_merge0), the 15 ns lead's
   lever 1 carried to ipow by the event-graph search, on the kernel bench**: #20 below. Full gate 24/24 on 8 bench routes.
   Predicted 1.18x per iteration over item 13 on this route (1.13-1.21 over 8). Judge: `python3 ../research/tools/
   loop_cost_judge.py ipow build/hw/lc_ipow_r.tsv build/hw/lc_ipow_fm.tsv`.
20. **collatz item 15 + a latch on the merge fork's result branch (BDC_MERGE_RES_LINK=ucontrol_merge0), the 15 ns
   lead's lever 1 carried to collatz by the event-graph search, on the kernel bench**: #21 below. Full gate 24/24 on 8
   bench routes. Predicted 1.25x per iteration over item 15 on this route (1.18-1.25 over 8). Judge: `python3 ../research/
   tools/loop_cost_judge.py collatz build/hw/lc_col_r.tsv build/hw/lc_col_fm.tsv`.
21. **collatz64 item 16 + a latch on the merge fork's result branch (BDC_MERGE_RES_LINK=ucontrol_merge0), lever 1
   carried to collatz64, on the kernel bench**: #22 below. Full gate 24/24 on 8 bench routes. Predicted 1.17x per
   iteration over item 16 on this route (1.11-1.21 over 8). Judge: `python3 ../research/tools/loop_cost_judge.py
   collatz64 build/hw/lc_c64_r.tsv build/hw/lc_c64_fm.tsv`.
22. **collatz at ~41 ns per iteration, FULL INPUT RANGE: item 20 + the rule-1 link between uselect0 and the compare dropped
   (BDC_NO_LINK=ulink_n28__1) + per-cell sizes from 8 routes at both corners (collatz_sizes_T3cdb_nl2_bench.vh)**: #23
   below. Farm, 32 seeds (fcolsz2): median 41.15 ns (38.85-43.26) vs item 20 48.86; gate 81/81; static check (rules A /
   A' / E at nominal and worst) CLEAN on every evaluated route. Board seed 26 (sdf bc2fe0c8, 41.10 ns, the median).
23. **xorshift at ~23.5 ns per iteration, FULL INPUT RANGE: item 17's structure + a latch on the adder's steer branch
   (BDC_FORK_OUT_LINK=n11__0,n30__0) + full-range sizes (xorshift_sizes_T3s50_fr3_bench.vh)**: #24 below. Farm, 32 seeds
   (fxf4): median 23.49 ns (21.00-24.75); gate 87/87; static check clean on 28/30 (one spanned datapath miss, one
   incomplete); trace-measured hold check clean. Board seed 10 (sdf 2f825834, 23.31 ns). Item 17 (20.60 ns) holds only
   for the bench's 12-bit rounds.
24. **collatz64 at ~45 ns per iteration, FULL INPUT RANGE: item 21 + the rule-1 link between uselect0 and the compare dropped
   (BDC_NO_LINK=ulink_n30__1)**: #25 below. Farm, 32 seeds (fc64nl / fc64nlh): median 45.23 ns (42.46-47.09) vs item 21
   47.64; gate 90/90; static check: only umux2's rule-A row, shown by trace to be a false path; hold check clean.
   Board seed 17 (sdf 3a370768, 45.19 ns).
25. **collatz at ~36 ns per iteration, FULL INPUT RANGE, hold-checked: the exit test n' == 1 rewritten to n == 2
   (research/tools/fifteen/pre_eq2.py, exact on every input) on item 22's structure with round-2 hold pads (nl4)**: #26
   below. Farm, 32 seeds (fceq): median 35.82 ns (33.38-38.51) vs 41.24 for the same sizes without the rewrite (fcol4,
   paired on 31 seeds: -5.28 ns, 31/31 faster, 1.15x); gate 96/96; static A / A' / E clean 32/32 at both corners;
   rules H / I clean on 31/32 (seed 5: I -12 ps); trace hold checks clean on all 32. Board seed 24 (sdf e001dc27,
   35.92 ns, every row clean). Dynamatic 14.05.
26. **collatz64 at ~36 ns per iteration, FULL INPUT RANGE: the same n == 2 exit test (pre_eq2.py) on item 24's
   structure with round-2 hold pads (h2)**: #27 below. Farm, 32 seeds (fc64eq): 30 routes, median 36.23 ns
   (34.38-38.15) vs 45.28 for the same sizes without the rewrite (fc64h2, paired on 31 seeds: -9.02 ns, 31/31
   faster, 1.25x); gate 90/90 on every route but seed 32 (an ffmux-gap route, excluded with seed 5). Static: umux2's traced
   false-path row on every route as for item 24; besides it umux0 rule A -45..-135 ps on 3 routes and ucmpi2 -29 on one
   (sizes h3 pad both, farm fc64eq2 running); H / I clean on 29/30. Board seed 25 (sdf 6982a9d5, 36.27 ns): every
   row clean but umux2's. Dynamatic 17.84.
27. **xorshift at ~19.4 ns per iteration, FULL INPUT RANGE: the loop test reads i against n-1 (pre_dec.py, n-1 computed
   once before the loop; exact on every reachable state) on item 23's structure with fr4 sizes**: #28 below. Farm, 32
   seeds (fxd): 31 routes, period median 19.39 ns (18.98-21.16) vs 23.47 for fr4 without it (fxf5; latency paired on
   28 seeds: -3.76 ns per iteration, 27/28 faster, ~1.21x); gate 93/93; static A / A' / E clean on 29/31 (seeds 6, 27:
   -12 / -13 ps at worst); H / I / F rows on 11/31 (to -355 ps; pad round fr5d / farm fxd2 running); trace hold checks
   clean on all. Board seed 2 (sdf a9bdac53, latency 417 = the median): every row clean. Dynamatic 12.73.

28. **collatz at ~25.8 ns per iteration, FULL INPUT RANGE, select links sized by their checks (the select rule withdrawn)**:
   #29 below. Item 25's structure with nl6 sizes, the three select links (ulink_n14__0, ulink_n14__1, ulink_n_index_11)
   at 3 elements instead of 18 / 36 / 15, and ULINK_N10__4_UACK at 0 (the line was missing from sizes.vh). Farm fcsel3m:
   28 of 32 routes back, period median 25.81 ns (24.63-27.55) vs 36.60 (fceq2); latency paired on 26 seeds -10.94 ns per
   iteration (26/26 faster, ~1.42x). On EVERY route: gate 13/13 at SLOW_MAX / FAST_MIN / worst+M, static A / A' / E clean
   at nominal and worst (corrected summary: E rows read), H / I clean, hold_bits clean, TSE clean at FAST_MIN and worst.
   Board seed 20 (sdf d86bdde5, latency 566 = the median). Dynamatic 14.05.
   2026-11-16: audit T117 CONFIRMED the board seed (own build, 3 corners, its pin-level select-arrival monitor 0 late,
   own rules E / H clean); fcsel3m_la's 30 routes are all static-clean. Select negative controls: JOURNAL 2026-11-16.

29. **ipow at ~36 ns per iteration, select links sized by rule E and mux delays by rule M -- every static row clean**:
   #30 below. ipow h4 (item 19's knobs, T9s75 sizes + h4 hold pads) with the four select links (ulink_n17__0/1/2,
   ulink_n_index_15) at 3 instead of 15 / 8 / 23 / 9 (rule E), and the mux delays umux0 / 1 / 2 / 3 at 6 / 8 / 7 / 4
   instead of 8 / 9 / 2 / 3 (rule M, the mux data outputs, new 2026-11-16; A' at umux3, whose old -1.4 ns rule-A row
   was the traced false path). Farm fisel3m, 32 seeds: 27 routes (5 with the known ffmux / F7 bitstream defects),
   period median 36.20 ns; latency paired vs fipowh4 on 19 seeds -2.71 ns per iteration (17/19 faster), the same as the
   first version (fisel3, without the mux sizing). Gate 81/81; rule A / A' / E / M clean at nominal and worst on
   27/27 -- the first ipow family with no static row; TSE / hold_bits clean; H rows on 2 routes (-25, -83).
   Board seed 19 (sdf b521630f, latency 97 = the median): every row clean. (2026-11-16 first version: h4s3, sdf
   4a92cdf3, superseded because rule M found umux2 -382 ps there.)
30. **collatz64 at ~35 ns per iteration, select links sized by rule E**: #31 below. collatz64 h4 (item 26's structure
   with the h4 pads) with the select links ulink_n14__0 / ulink_n14__1 / ulink_n_index_11 at 3 / 6 / 3 instead of
   15 / 19 / 14 (at 0, E was -850 / -1761 / -511 ps). Farm fc64sel3: 29 routes (24 with no known defect for the
   pairing), period median 34.94 ns; latency paired vs fc64eq3 (h4) on 27 seeds -1.56 ns per iteration (25/27 faster).
   On every route: gate 3 x 14/14, rule E clean, H / I clean, hold_bits clean; TSE -120 ps on one route (seed 1);
   umux2's traced false-path A row. Board seed 10 (sdf 637ff02e, latency 763 = the median): every row clean but umux2's.
31. **collatz at ~21.5 ns per iteration, FULL INPUT RANGE: item 28 + uselect0 16 -> 7 and uaddi0 12 -> 9**: #32
   below. The uselect0 line had been sized by tighten's bundled pairing because corner_audit refused the
   upstream-link measurement (A') there: the cell's own request-join C nodes were counted as data, so the reset flop
   and the folded constant's request into the join looked like foreign data launches (a tool bug, fixed 2026-11-16).
   With A', the line needs 7. Farm fcsel3a, 32 seeds: 31 routes (one ffmux-flagged), period median 21.48 ns
   (20.43-23.05) vs 25.81 (item 28); latency paired vs fcsel3m on 30 seeds -3.93 ns per iteration (30/30 faster, ~1.18x).
   On every route: gate 13/13 at SLOW_MAX / FAST_MIN / worst+M, rule A / A' / E clean at nominal and worst, TSE and
   hold_bits clean; two routes carry one hold-side row each (F -213 ucontrol_merge1 flush on s2, I -236 falseResult_9 on
   s3). Board seed 20 (sdf 7aefc4bd, latency 468, near the median 471; item 28's seed, so the two are a minimal pair by
   sizes): every row clean, re-checked locally. Dynamatic 14.05.
32. **collatz64 at ~31.4 ns per iteration: item 30 + corner_audit's proposal round with the A' fix (uselect0 18 -> 12,
   uaddi0 25 -> 23, ack lines trimmed)**: #33 below. Farm fc64sel3p, 32 seeds: 30 routes, period median 31.39 ns
   (29.00-34.10) vs 34.94 (item 30); latency paired vs fc64sel3 on 30 seeds -3.52 ns per iteration (30/30 faster).
   Gate 90/90; rule E clean everywhere; rule A rows only umux2's traced false path; TSE hold rows at ulink_n28 on 9/30
   routes (to -295 ps at FAST_MIN; the round trimmed ULINK_N28_UACK 3 -> 1; fc64sel3q restores it, running) and small H
   rows on 3. Board seed 22 (sdf 842dd4d7, latency 685, near the median 687): every row clean but umux2's, TSE / hold
   clean. Dynamatic 17.84.
33. **xorshift at ~18.9 ns per iteration, FULL INPUT RANGE: item 27 + seed 2's own corner_audit proposal on the datapath
   lines (uxori1 / uxori2 7 -> 5, umux3 14 -> 9, ucmpi0 12 -> 10, uaddi0 13 -> 12)**: #34 below. Farm fxa, 32 seeds: 31
   routes, period median 18.91 ns (17.97-20.86) vs 19.39 (item 27); latency paired vs fxd on 30 seeds -0.40 ns per
   iteration (22/30 faster). Gate 93/93. Static: rule M rows at umux0 / umux1 on most routes (as on item 27's own
   family under the same corner_audit), H rows on a few, steer E rows on 2. Board seed 27 (sdf 7f0c0592, latency 404 =
   the median): its only rows are rule M, umux1 -113 nom / -192 worst and umux0 -71 worst; in simulation (mux_settle.py,
   512 loop tokens) the mux data LEADS z_req by >= 1042 ps (FAST_MIN) / >= 1469 ps (worst) on every token, so these
   rows are the check's pessimism on this route. Everything else clean (TSE, hold_bits, E, A'). Dynamatic 12.73.

## 1. gcd_hw, fusion on, cloud toolchain, v4 placement, converged select pads -- 16/16 in routed GLS on 8 seeds
**Rule J (verify/arb_fork.py, added 2026-10-26) on this route: pass, worst guarded +463 ps**
(8 seeds: worst +272, raw >= +718). That counts the part of A0's route its branches share as
common, and that part is an ESTIMATE (pip-count fraction; the routed JSON has no per-pip delays).
Without that credit, 3 of 8 routes came out short. See JOURNAL 2026-10-25 "rule J".

Branch claude/research. Bitstream: `research/board/gcd_hw_03e82630.bit`
(sha256 03e82630dcf5c453b40121cdaf86eae0cc79c6c65a69ba1bfa0c83e402141196; the route with
build_hw.sh's default seed; sdf md5 6f8b99e6 (routed.json 1c6a1fb9 on the original build only: it embeds
absolute paths and does not reproduce, audit bq1-repro.md -- compare the sdf); toolchain in the
`.toolchain.txt` beside it: nextpnr 9c732bc6303458df, patches 789a7120c912d393, yosys v0.62,
fasm via prjxray's textX parser).

Use the committed bitstream, not a local rebuild: the local yosys may map a different netlist
(it did for soak_top, see JOURNAL 2026-10-25 19:21), and this bitstream is the one that was
GLS'd. To rebuild the same route in the cloud: `cd cells && BDC_SELECT_PADS=$PWD/hw/gcd_hw_pads.json
BD_RLOC=v4 ./hw/build_hw.sh gcd_hw`.

    cd cells
    mkdir -p ../build/hw/gcd_hw && cp ../research/board/gcd_hw_03e82630.bit ../build/hw/gcd_hw/gcd_hw.bit
    hw/board.sh python3 hw/gcd_measure.py --program
    sleep 60
    hw/board.sh python3 hw/gcd_measure.py; echo "exit $?"

Pass (self-reporting): the second command prints `PASS -- all vectors correct,
err_sticky=0x0000, ok_sticky=0xFFFF.` and exits 0. Anything else is a FAIL. It also refuses to
judge a die that is not running gcd_hw (scan-alignment check).

What it would mean:
- PASS: the first compiled kernel built entirely in the cloud (fusion on) is correct on silicon,
  including vectors 5/6/7/8/11/12/13 that the August builds failed. It also validates the cloud
  bitstream path end to end (yosys 0.62 + textX fasm parser), which nothing has checked yet.
- FAIL with err bits set: a wrong answer that routed GLS on 4 routes did not show. Send
  `gcd_measure.py`'s full output (errv/absn/abss); GLS of this exact route is reproducible from
  the md5s above.
- FAIL "never checked" on some vectors: a livelock or deadlock on silicon, the August failure
  shape. Compare the mask with 5, 6, 7, 8, 11, 12, 13.
- Refused / scan misaligned: a bitstream generation problem (the fasm or frames path), not the
  design.

Evidence update 2026-10-26: same pads on seeds d and 2-8, rules A/E/H/I/J clean and routed GLS
16/16 errs=0 on all 8; x0.9 and x1.1 corners 16/16 on seeds d, 5, 6, 7, 8 (JOURNAL 2026-10-26 04:13).

Evidence (all in JOURNAL 2026-10-25 19:21): rule E 0/118 violated on all 4 routes; tighten rules
A/H/I 0 violations (rule D 38 = the documented screen); GLS gate ANNOTATE_DONE with 0 SDF
warnings/errors on each; 16/16 vectors, errs=0, laps 19-2719 per 150 us window on each.

Board-fidelity full stack, 8 seeds x 2 corners (2026-10-31, resolver 055edd7; research/data/fid/bq1_fullstack_8seed.tsv;
default-seed sdf 6f8b99e6 reproduced): 16/16 errs=0 and bits EQUIVALENT on all 16 runs; laps vec 6 SLOW_MAX mean
15.9 (15-16), FAST_MIN 45.9 (44-48). #2 on the same stack: SLOW_MAX ~32, FAST_MIN ~88 (the ~1.9-2x of the
nominal GLS holds at both corners). Within-die scatter 1x (band 0.38 + region 0.16 + wire 0.126, draw 1): 8/8 seeds
PASS (vec 6 laps 23-29).
Log-normal (bounded) within-die scatter 1.5x (region 0.24 + wire 0.189), draw 2: 8/8 seeds PASS (vec 6 laps 24-32).
Log-normal 3x (region 0.48 + wire 0.378), draw 2, all 8 seeds: 8/8 PASS 16/16 errs 0 (vec 6 laps 20-32;
research/data/fid/bq1_logn3x_draw2.tsv); draw 3, all 8 seeds: 8/8 PASS 16/16 errs 0 (vec 6 laps 20-30;
research/data/fid/bq1_logn3x_draw3.tsv). The default lengths carry far more scatter margin than R5 (#2/#3 fail at 1.5-2x).

## 2. gcd_hw with route-measured matched-delay sizes (R5) -- ~1.9x laps in routed GLS; every audit and routed GLS (nominal + corners) clean on 8 routes
Same rig, pads and placement as #1, plus per-cell matched-delay sizes `research/data/gcd_hw_sizes_R5.vh`
(220 sizes). History: R2 passed every audit on 8 seeds until rule E learned to launch from the select's
feeding-link C node (69ee32b), which flagged R2 on 2 seeds; R3/R4 padded the asks route by route; R5 adds
`skew.py --slack 500` asks over R4's 8 routes, i.e. every select link with less than +500 ps guarded on any
route was padded to reach it.
Branch claude/research. No bitstream is committed (owner, 2026-10-25); build it in the cloud toolchain
(nextpnr 9c732bc6303458df, patches 789a7120c912d393, yosys v0.62). The default-seed build's sdf md5 is
a9c4e265; check yours with md5sum before trusting the run. Compare the SDF only: the .bit md5 is not reproducible
(header date bytes), and the routed.json md5 recorded earlier (7be3c1cf) was not reproduced by the independent
audit's clean rebuild (b398103e, same sdf) -- a different routed.json md5 is NOT a reason to distrust the build:

    cd cells
    BD_SIZES=../research/data/gcd_hw_sizes_R5.vh BDC_SELECT_PADS=$PWD/hw/gcd_hw_pads.json BD_RLOC=v4 ./hw/build_hw.sh gcd_hw
    md5sum build/hw/gcd_hw/gcd_hw.bit build/hw/gcd_hw/gcd_hw_routed.json build/hw/gcd_hw/gcd_hw.sdf
    hw/board.sh python3 hw/gcd_measure.py --program
    sleep 60
    hw/board.sh python3 hw/gcd_measure.py; echo "exit $?"

Pass (self-reporting): `PASS -- all vectors correct, err_sticky=0x0000, ok_sticky=0xFFFF.` and exit 0.
Speed (secondary, only meaningful after a PASS): gcd_measure.py's per-vector latency in housekeeping
cycles per completed gcd; run #1's bitstream the same way and compare. Routed GLS predicts R5 at about
0.5x of #1's latency on the loop vectors (6, 12, 13). The housekeeping ring is placed per route, so
compare ratios across vectors, not absolute cycles.

What it would mean:
- PASS and ~2x: route-measured sizing of a compiled kernel's matched delays is safe and pays on silicon.
- PASS with no speedup: the matched delays are not on silicon's critical cycle; still safe.
- FAIL while #1 passes: a too-short delay that rules A/E/H/I/J and corner GLS did not see -- the most
  important possible result; send the full gcd_measure.py output.

Evidence (JOURNAL 2026-10-26 04:13 session): rules E (with C-node launches)/A/H/I/J 0 violations on
seeds d, 3, 4, 5, 6, 7, 8, 9 (seed 2 did not place: nextpnr post-placement validity check); routed GLS
16/16 errs=0 at nominal, x0.9 and x1.1 on ALL 8 placed routes d, 3-9 (vec 6 nominal: 47 / 42 / 45 / 49 /
50 / 48 / 49 / 48 laps, mean 47.3, vs 24-26 unsized), gate clean on each. Per-arc scatter on R5 seeds 3 and 4: 8.5%
(seed 4), 17%, 25% x2 all 16/16. Its predecessor R2 (same compute sizes, fewer select pads) passed
nominal/corner GLS on 8 seeds and per-arc scatter to 25% (wire mode to 35%) on two routes.

Board-fidelity full stack (bits-decoded netlist + prjxray SDF + fid primitives), 8 seeds x 2 corners: seeds
d,3,4,5 (2026-10-29 early session, old resolver) and 6,7,8,9 (2026-10-29 14:41 session, resolver 055edd7;
research/data/fid/bq2_fullstack_s6-9.tsv): 16/16 errs=0 and bits EQUIVALENT on all 16 runs. Laps vec 6 SLOW_MAX
28-33 (6-9: 31-33), FAST_MIN 77-93 (6-9: 86-93). The resolver change reproduced seed 6 SLOW_MAX exactly (33/27/39).
Arbiter near-tie round trips (research/data/fid/arbtie.md): 0 of 18 ack C-elements below the model's requirement on
seeds 6-9, worst margin 878 ps.
Within-die scatter (band 0.38, draw 1, 2026-10-30/31): 1x (region 0.16 + wire 0.126) PASS on seeds 6, 7, 8, 9; 2x
(0.32 + 0.252) PASS on seeds 7, 8, 9 and FAILS on seed 6 (vectors 7, 8, 12: one lap with an x compare, then stall).
Cause, confirmed by intervention: uori3's matched delay (chain X12-13 Y53-55, region factor 0.49 in this draw)
tracks a datapath at X0-5 Y56-76 (factors 1.56/1.54); with only that chain's arcs and wires scaled back x2.03,
all three vectors pass (39/175/146 laps, errs 0). Same mechanism as #3's seed-9 uori2 failure, beyond what the
ring data supports, so #2 stays queued; if the board fails vectors 7, 8, 12 with the rest passing, suspect uori3.
Log-normal within-die scatter (GLS_SCATTER_LOGN=1, bounded speed-ups, 2026-11-01): 1.5x (region 0.24 + wire 0.189),
draw 2: PASS on seeds 6, 7, 8, 9 (the routes on disk). Seed 6's failing scale on draw 1: between 1.5x and 1.75x.
Fresh seeds (2026-11-03): R5 on seeds 10, 11, 14 every audit clean; seed 13 rule E 6 violations, all one link
(ulink_n106__1 feeding ucond_br34/35/36: raw +3837 ps, guarded -119 ps, fix +1 element); seed 12 does not place (nextpnr
"post-placement validity check failed ... A5FF (no cell)", third time seen). So build #2 with the default seed as
written (that route is the one audited and simulated); another seed can come out rule-E short by one element.

## 3. gcd_hw R5 sizes + link fast fall (BDC_LINK_FASTFALL=1) -- ~6% more laps than #2 (same 8 routes), every audit and routed GLS clean on 8 routes
Run only after #2 passes: it is #2 plus one opt-in change (bd_link's request delay and bd_mux's output delay fall
in one hop; cells/rtl/bd_link.v RFAST, bd_mux.v FASTFALL, committed fdfe098 with tighten.py rule F, which audits
that a fast-fall line drains before its input can rise again). Same rig, pads, placement, sizes.
Toolchain as #2. Default-seed md5s: sdf 61e14755 (compare this one), routed.json f9c4597d (reproduced by the audit, but routed.json
md5s are not portable in general), bit f9fb4b19 (not reproducible):

    cd cells
    BD_SIZES=../research/data/gcd_hw_sizes_R5.vh BDC_SELECT_PADS=$PWD/hw/gcd_hw_pads.json BD_RLOC=v4 BDC_LINK_FASTFALL=1 ./hw/build_hw.sh gcd_hw
    md5sum build/hw/gcd_hw/gcd_hw_routed.json build/hw/gcd_hw/gcd_hw.sdf
    hw/board.sh python3 hw/gcd_measure.py --program
    sleep 60
    hw/board.sh python3 hw/gcd_measure.py; echo "exit $?"

Pass: the same PASS line and exit 0 as #1/#2. Speed: compare gcd_measure.py's per-vector latency with #2's; routed
GLS predicts ~0.92x of #2 on the loop vectors.
What it would mean: PASS = the fast request fall is safe on silicon; FAIL while #2 passes = a fall-path hazard that
rules A/E/F/H/I/J and corner/scatter GLS did not see (send the full output).
Evidence (JOURNAL 2026-10-26/27): seeds d, 3-9: rules A/E/F/H/I/J 0, fasm_audit PASS, gate clean, routed GLS 16/16
errs=0 at nominal on all 8 and at x0.9/x1.1 on d, 3, 6, 7, 8, 9; 17% scatter on d and 3. Laps vec 6 mean 50.0
(46-52, 8 routes) vs #2's 47.25 on the same 8 routes (+5.8%; vec 12 +6.0%, vec 13 +5.8%; the earlier "~9%" compared
8 routes with #2's 4, corrected per audit research-stats.md); vec 12 40.4, vec 13 58.6. Rule F worst +888 ps (an existing line).
Reproduction (2026-10-27): an independent rebuild of the default-seed route gives the same routed.json
(f9c4597d) and sdf (61e14755) md5s; on it rules A/E/H/I/J 0, gate clean, GLS 16/16 at nominal, x0.9, x1.1 and
wire scatter 25% (1 draw) and 35% (2 draws).
Board-fidelity full stack (2026-10-27 session 10:12; research/data/fid/fullstack.md): this route, simulated from the
netlist decoded from its own .bit, with prjxray RC-tree delays and the fid primitives: 16/16 errs=0 at FAST_MIN,
SLOW_MAX and band 0.38 (laps vec 6 91 / 33 / 55). At band 0.38 (where the five measured rings sit) the stack predicts
vec 6 ~55 laps per 150 us window. The same stack fails the unpatched lut-pinmap bitstream on an August-shaped route
(vectors 5-8, 11-13 never complete), so it can fail. 
8 seeds (2026-10-29, research/data/fid/bq3_fullstack_8seed.tsv): seeds d,3-9, each simulated from its own .bit
(fid model 78de9c2 + decoder fix 54f2ce6): 16/16 errs=0 at FAST_MIN on 8/8 (laps vec 6 mean 89.6, 83-94) and at
SLOW_MAX on 8/8 (vec 6 mean 32.8, worst seed 4: 31); band 0.38 with region 0.16 + wire 0.126 scatter (the measured
8.5% median ring scatter): 8/8 seeds pass, vec 6 47-54; with 2x that: 7/8 pass, and seed 9 FAILS (draw 1: six
vectors give one lap with an X in the result compare, then stall). Root cause (JOURNAL 2026-10-29): uori2's matched
delay sits ~30 slice rows from the comparator it tracks; the failing draw makes their regions differ ~2.8x in
speed at its threshold (~1.33x the calibrated scatter). Beyond what the ring data supports, so #3 stays queued;
if the board fails vectors 2,3,9,11,13,15 with the rest passing, suspect this bundle first.
Re-run on the 055edd7 resolver (2026-10-30, research/data/fid/bq3_fullstack_newresolver.tsv; audit r16's
follow-pulse fix): all 16 corner runs PASS 16/16, EQUIVALENT, every laps triple identical to the old-resolver
table (vec 6 SLOW_MAX mean 32.75, FAST_MIN 89.6); the seed-9 2x-scatter failure reproduces exactly (same six
vectors). Arbiter near-tie round trips (research/data/fid/arbtie.md): 0 of 18 ack C-elements below the model's
requirement on all 8 routes, worst margin 691 ps (seed d).
Log-normal within-die scatter (GLS_SCATTER_LOGN=1, bounded speed-ups, 2026-11-01): 1.5x the calibrated scatter
(region 0.24 + wire 0.189), draw 2: PASS on all 8 seeds (vec 6 laps 44-56). Seed 9's failing scale on draw 1:
between 1.75x and 2x (linear factors: ~1.33x).
The board's vec 6 should land between the FAST_MIN and SLOW_MAX numbers; ~50-55 laps per 150 us is the band
prediction.

## 4. gcd_ps: the same kernel, 32-bit operands from the PS (no vector table), P1 pad-only sizes -- every audit and the full-stack fid GLS (24/24, both corners) clean on 8 seeds
The owner's lead of 690f156. The kernel, bdc flags, pads (`gcd_hw_pads.json`) and placement (v4) are BQ#1's; the
harness is `cells/hw/gcd_ps.v` (AXI3 register slave on M_AXI_GP0, operands from the host, no vector table). With
full-width operands one bundle needs more delay than BQ#1's: `bridge_i.udut.umux21` violated rule A on 3 of 4 unsized
seeds (-1567/-154/-464 ps), so P1 lengthens it alone, 12 -> 16 links (`research/data/gcd_ps/gcd_ps_sizes_P1.vh`,
research/tools/pad_sizes.py: only rule-A violators lengthened, nothing shortened).

**Formal target**: seed `d` (build_hw.sh's default seed) of this build.
- `research/board/gcd_ps_e6bb4aec.bit`: md5 aa83c8b7a5e6b68e69729131e984c0f4,
  sha256 e6bb4aec70f31fa7579a482d94ec168162656dabf74e833ed57d1a516b809798
- `research/board/gcd_ps_e6bb4aec.fasm.gz`: the .fasm, gzip -n; md5 of the uncompressed .fasm
  2dbf962dbcf01dcd9bd6ad6f7870ca27
- `research/board/gcd_ps_e6bb4aec.boundary.tsv`: the kernel's boundary in this route (the kernel has no pins in
  the bitstream; its ports are internal nets), from research/tools/boundary_map.py on the routed JSON: in =
  a_data[31:0] (bridge_i.a_data_reg FF Q), b_data[31:0] (b_data_reg), rst (SLICE_X2Y29/DFF/Q, ctrl_rst), the ONE
  request net a_req = b_req = start_req (SLICE_X3Y30/C5FF/Q, the req_core FDCE; yosys named it bridge_i.p_end_req),
  out0_ack (SLICE_X4Y34/A6LUT/O6 = ctrl_o_ack & o_req, named n_index_97_ack), p_end_ack; out = a_ack, b_ack,
  start_ack, out0_req (SLICE_X5Y31/C6LUT/O6, core_o_req), out0_data[31:0] (o_data_pl).
- same route: sdf md5 cbdbea3a7416b56010e8ef0aec0331d4, prjxray SDF (xray_delay.py) 8afd5cce25bbc4187cb11808fae1d5a4;
  toolchain in `gcd_ps_e6bb4aec.toolchain.txt` (nextpnr 9c732bc6303458df, all patches ok, yosys 0.62, textX fasm
  parser). Branch claude/research.
Use the committed bitstream (as for #1). To rebuild the same route in the cloud:

    cd cells && BDC_SELECT_PADS=$PWD/hw/gcd_hw_pads.json BD_RLOC=v4 \
        BD_SIZES=../research/data/gcd_ps/gcd_ps_sizes_P1.vh ./hw/build_hw.sh gcd_ps

Board run (from cells/; the first is the 16 golden vectors, the second 1000 vectors outside them):

    hw/board.sh xsdb hw/xsdb_gcd.tcl ../research/board/gcd_ps_e6bb4aec.bit; echo "exit $?"
    hw/board.sh xsdb hw/xsdb_gcd.tcl ../research/board/gcd_ps_e6bb4aec.bit ../research/board/gcd_ps_vec1000.hex; echo "exit $?"

`gcd_ps_vec1000.hex` comes from `cells/gls/ps/gen_vectors.py --n 1000 --seed 1`: operands in [0, 2^31), none of
gcd_rig's 16 pairs, expected from bdc/simcheck.py's `ref_gcd` (the transcription of gcd.c) and asserted equal to
math.gcd; none is 0. Its first 24 lines are the vectors the GLS below ran.

Pass (self-reporting): each run prints `liveness pre-check PASS`, then `=== PASS 16/16 ===` (first) and
`=== PASS 1000/1000 ===` (second), and exits 0. Any `MISMATCH`, `TIMEOUT`, a `FAIL:` line or a non-zero exit is a
FAIL. The script programs the PL and re-runs the SLCR bring-up itself (FCLK0 100 MHz).
The script's verdict was checked offline (`tclsh cells/hw/mock_xsdb_gcd.tcl FAULT -- <bit> [vecfile]`, a fake
board with gcd_ps's register map and an independent Euclid gcd): clean, PASS 16/16 and 1000/1000, exit 0 (so the
vector file's ref_gcd answers agree with Euclid on all 1000); one wrong answer or one missing o_req, `PASS 999/1000`
plus `FAIL: 1/1000`, exit 1; A_DATA reading back 0, the liveness pre-check refuses, exit 1. Note `=== PASS k/n ===`
is printed on a failing run too: only `n/n` with exit 0 is a pass.

What it would mean:
- PASS: the compiled kernel computes gcd on full 32-bit operands from outside the die, on 1000 vectors nobody
  chose to suit the route, on silicon. That is the claim the formal work's target is about.
- MISMATCH on some vectors: a wrong answer the full-stack GLS did not show. Send the full output (a, b, got).
- TIMEOUT "o_req rise": a missing answer (livelock or deadlock), the August shape. Note which vectors.
- `A_DATA readback FAILED` or a TIMEOUT on "i_ack rise" for every vector: the AXI bridge or the PS bring-up, not
  the kernel.
- The harness is sequential on purpose (one call completes before the next is offered). formal/FOR-RESEARCH.md
  section 2: the kernel reorders overlapped calls, so a host that overlaps them is not testing this.

Evidence (JOURNAL 2026-11-01 17:31-19:57):
- Audits, P1 seeds d,3-9 (`research/data/gcd_ps/p1_audit_8seed.tsv`): rule A 0 on all 8 (umux21 margin mean 1456 ps,
  range 358-1889, guardband applied), rule D 38 (the screen, as on #1), E 0, J ok, build_hw PASS incl. fasm_audit.
  nextpnr's fclk0 estimate 343-447 MHz against the 100 MHz FCLK0 (build_hw.sh passes no --freq for gcd_ps, so its
  "PASS at 12.00 MHz" line means nothing; the estimate is the number).
- Full stack (`research/data/gcd_ps/p1_fullstack.tsv`): each seed's netlist decoded from its own .bit with the PS7
  (fasm2net --ps7), prjxray SDF, fid primitives, a behavioural PS7 running the host sequence above over the 24
  vectors: seeds d,3-9 x SLOW_MAX/FAST_MIN: 24/24 ok, 0 err, 0 hang, fasm_equiv EQUIVALENT on all 16 runs; gate
  ANNOTATE_DONE with 0 SDF warnings on all 16. (0x7fffffff, 0x7ffffffe), the longest vector: 15.0 us mean
  (14.6-15.4) from i_ack to o_req at SLOW_MAX, 5.3 us (5.2-5.45) at FAST_MIN.
- Within-die scatter 1x (band 0.38 + region 0.16 + wire 0.126, the measured 8.5% median ring scatter; draw 1):
  8/8 seeds 24/24, EQUIVALENT (`research/data/gcd_ps/p1_scatter1x.tsv`; out0 margin on 6-9 +5.96..+7.41 ns).
  Log-normal 1.5x (region 0.24 + wire 0.189, draw 2), all 8 seeds: 24/24, EQUIVALENT, out0 margin +5.93..+9.07
  ns, no late change (`research/data/gcd_ps/p1_logn15.tsv`); draw 3, all 8 seeds: 24/24, out0 margin +6.19..+9.95 ns
  (`p1_logn15_draw3.tsv`). BQ#4 now has BQ#1's scatter coverage. Beyond it (draw 2): log-normal 2x 8/8 and 3x 8/8
  seeds 24/24 (out0 margin >= +5.07 ns), 5x on seed d 24/24 (`p1_logn2x.tsv`, `p1_logn3x.tsv`): no scatter level tried
  breaks this design (P1 keeps default lengths; the tightened R5 of #2/#3 fails at 1.5-2x).
- **Every vector the board run uses, pre-simulated on the formal target itself**: all 1000 of gcd_ps_vec1000.hex on
  the netlist decoded from gcd_ps_e6bb4aec.bit, full stack, SLOW_MAX and FAST_MIN: 1000/1000 ok, 0 err, 0 hang at
  both corners, out0 margin >= +12.0 / +4.1 ns, no late change; and at band 0.38 + 1x within-die scatter (the
  board-like point) 1000/1000, margin >= +7.3 ns (`research/data/gcd_ps/p1_vec1000_target.tsv`).
  So a board MISMATCH or TIMEOUT on any of them is a disagreement with this model, vector by vector.
- The harness can fail: the same netlist with two expected values corrupted gives ok=1 err=2.
- umux21 drives out0, and the PS reads O_DATA >= 2 synchronizer clocks after out0_req, so this harness cannot see
  an out0 bundling violation (umux21 cut to 1 link: still 24/24). Measured instead at the kernel boundary with an
  out0 bundling monitor (`research/data/gcd_ps/p1_out0_bundle_8seed.tsv`): P1 on all 8 seeds, SLOW_MAX mean +12.3 ns
  (worst +11.3, seed 5), FAST_MIN mean +4.2 ns (worst +3.98, seed 5) between the last out0_data change and out0_req,
  no late change; seed d with 64 vectors 64/64 at both corners, same margins; the monitor's negative control
  (umux21's data LUTs 20x slower) shows 23-24 late changes up to 10 ns after the request while the harness still
  says 24/24. On this bundle rule A over-charges: even 1 link measures +0.57 ns at FAST_MIN where rule A asks
  for 13. P1 is kept (a delay that is too long only costs time; this one is on the exit path, once per call).
- CDC (read in gcd_ps.v): STATUS.i_ack and STATUS.o_req reach the PS clock through 2-flop synchronizers; the
  kernel-facing request is a flop cleared asynchronously by the kernel's own i_ack (the pulse adapter), so a host
  holding CTRL.i_req for milliseconds over JTAG cannot wedge the kernel; A/B are written before the CTRL write that
  raises the request and stay unchanged until the result is read.

## 5. gcd_hw R5 sizes x0.75 + link fast fall -- the PROGRAM item 3 step; every full-stack run clean on 8 routes
Run after #3 passes (it is #3 with every matched delay ceil(0.75*n) links: research/data/gcd_hw_sizes_R5s75.vh, made
by research/tools/shrink_sizes.py from gcd_hw_sizes_R5.vh). Same rig, pads, v4 placement, BDC_LINK_FASTFALL=1.
Toolchain: nextpnr 9c732bc6303458df (cells/verify/toolchain.sh must pass). The gated routes are NEXTPNR_SEED 6, 7, 8, 9,
10, 11, 13, 14; build seed 6 (its md5s here: gcd_hw.sdf 39d30709, routed.json 72d6256d (not portable in general),
bit c1d9b764 (not reproducible)):

    cd cells
    NEXTPNR_SEED=6 BD_SIZES=../research/data/gcd_hw_sizes_R5s75.vh BDC_SELECT_PADS=$PWD/hw/gcd_hw_pads.json BD_RLOC=v4 BDC_LINK_FASTFALL=1 ./hw/build_hw.sh gcd_hw
    md5sum build/hw/gcd_hw/gcd_hw.sdf
    hw/board.sh python3 hw/gcd_measure.py --program
    sleep 60
    hw/board.sh python3 hw/gcd_measure.py; echo "exit $?"

Pass: the same PASS line and exit 0 as #1-#3. If the sdf md5 differs from 39d30709 the route is not the one gated here:
still a valid test of the recipe (8/8 seeds pass), but say so. Speed: gcd_measure.py's per-vector latency against #3's.
Full stack seed 6: vec 6 laps 35 (SLOW_MAX) / 95 (FAST_MIN) / 67 (combined worst case); the board's should fall
between the two corners.
What it would mean: PASS = the shrunk delays (25% off every matched delay) hold on silicon at this route; FAIL while #3
passes = a bundling margin the full stack mis-predicts at x0.75: send the full output; the first suspects are the
vectors whose loops run longest (6, 12, 13).
Evidence: research/data/item3/README.md, JOURNAL 2026-11-06/07. Rules A/E are informational under PROGRAM item 1 (the
sim is the gate). Seed 10's bits-vs-JSON check reads NOT_EQUIVALENT: four F7 inputs fed by $PACKER_GND_NET buffer LUTs
(constant 0 on both sides), the benign class seen on BQ#1 seed 8.

## 6. xorshift x0.5 on the kernel bench -- every matched delay ceil(0.5*n); 48/48 full-stack runs on 8 bench routes
PROGRAM item 3's xorshift step (8/8 soak routes, 1.42x worst case) rebuilt on the board's own top (cells/hw/
build_bench.sh, hw/gen_bench.py) and run through the full stack there, with its T3 base on the same seeds for the
speed comparison (research/data/xorshift_bench/results.tsv). The sizes are the soak files re-keyed for the bench
(research/data/xorshift_sizes_T3{,s50}_bench.vh: BD_SZ_UUT_ -> BD_SZ_BRIDGE_I_UDUT_; the unkeyed files are now refused
by build_bench.sh). Rule A fails 12-23 cells on every bench route of BOTH builds (the base too); under PROGRAM item 1
it is informational, so the build sets BD_SIZES_GATE=0 -- the full stack is the gate here. Toolchain: nextpnr
9c732bc6303458df (cells/verify/toolchain.sh must pass). From cells/:

    NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/xorshift_sizes_T3s50_bench.vh ./hw/build_bench.sh xorshift
    md5sum build/hw/xorshift_bench_gen/xorshift_bench_gen.sdf      # c5b8ca02 = the route gated here
    cp build/hw/xorshift_bench_gen/xorshift_bench_gen.bit build/hw/xorshift_s50.bit
    NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/xorshift_sizes_T3_bench.vh ./hw/build_bench.sh xorshift
    md5sum build/hw/xorshift_bench_gen/xorshift_bench_gen.sdf      # e3024283
    cp build/hw/xorshift_bench_gen/xorshift_bench_gen.bit build/hw/xorshift_t3.bit
    CLK=0x00100C00 BIT=build/hw/xorshift_s50.bit OUT=build/hw/xorshift_cost_s50.tsv hw/xorshift_cost.sh
    CLK=0x00100C00 BIT=build/hw/xorshift_t3.bit  OUT=build/hw/xorshift_cost_t3.tsv  hw/xorshift_cost.sh
    python3 ../research/tools/xorshift_bench_judge.py build/hw/xorshift_cost_s50.tsv build/hw/xorshift_cost_t3.tsv; echo "exit $?"

CLK=0x00100C00 (83.3 MHz) is the clock build_bench.sh closes the harness for; xorshift_cost.sh's default 0x00100A00
(100 MHz) is above it, and the full stack at 100 MHz SLOW_MAX showed the harness's latency register capturing a wrong
value (bit 7 dropped, 2 of 748 readings, one route) -- the kernel's answers were right. The judge reports ns.
Pass: the judge prints `=== PASS ... ===` and exits 0: both builds give the oracle's answer at all 17 round counts
(xorshift_cost.sh asserts each one and drops a point that fails). Checked both ways on synthetic files (a missing
point -> FAIL, exit 1). If an sdf md5 differs, the route is not the one gated here; still a test of the recipe, but say so.
Then the speed lines: per-round cost of each build, its place between the full stack's corners (the August kernels
sat at x = 0.21-0.23), and the ratio (predicted 1.47-1.49 on this route, 1.28-1.52 over 8; ~37 vs ~55 ns/round at
x = 0.21).
What it would mean: PASS = halving every matched delay is safe on silicon for this kernel and buys ~1.5x; x0.5 FAIL
with T3 PASS = a bundling margin the full stack mis-predicts at x0.5 (send both logs); both FAIL = the rig or the
re-keyed sizes, not x0.5.
Evidence: research/data/xorshift_bench/results.tsv (48 rows: bits vs JSON EQUIVALENT except 5 routes' single benign
GND-buffer F7/CARRY4 input, gate clean, 17/17 every run); research/data/item3/README.md (8 soak routes); JOURNAL 2026-11-07.

## 7. collatz64 x0.75 on the kernel bench -- every matched delay ceil(0.75*n); 24/24 full-stack runs on 8 bench routes
PROGRAM item 3's collatz64 step (8/8 soak routes, 1.18x) on the board's own top, with its T4 base on the same seeds
(research/data/collatz64_bench/results.tsv). Sizes re-keyed for the bench (research/data/collatz64_sizes_T4{,s75}
_bench.vh). Rule A fails 12-17 cells on every bench route of both builds (informational, PROGRAM item 1:
BD_SIZES_GATE=0). nextpnr 9c732bc6303458df. The T4 base on seed 4 could not be simulated: its bits leave a 5FF D mux
unconfigured (a nextpnr gap, JOURNAL 2026-11-08) -- any board build must show EQUIVALENT in fasm_equiv. From cells/:

    NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/collatz64_sizes_T4s75_bench.vh ./hw/build_bench.sh collatz64
    md5sum build/hw/collatz64_bench_gen/collatz64_bench_gen.sdf    # 412bd505 = the route gated here
    CLK=0x00100C00 hw/loop_cost.sh collatz64 && cp build/hw/loop_cost_collatz64.tsv build/hw/lc_s75.tsv
    NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/collatz64_sizes_T4_bench.vh ./hw/build_bench.sh collatz64
    md5sum build/hw/collatz64_bench_gen/collatz64_bench_gen.sdf    # ebb49f83
    CLK=0x00100C00 hw/loop_cost.sh collatz64 && cp build/hw/loop_cost_collatz64.tsv build/hw/lc_t4.tsv
    python3 ../research/tools/loop_cost_judge.py collatz64 build/hw/lc_s75.tsv build/hw/lc_t4.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0 (both builds answered all 10 of loop_cost.sh's points; it asserts each and drops a
failing one). Checked both ways on synthetic files. Then the per-iteration ratio, predicted 1.17-1.19 on this route.
What it would mean: as #6 (xorshift), at a gentler shrink.

## 8. ipow x0.75 on the kernel bench -- every matched delay ceil(0.75*n); 48/48 full-stack runs on 8 good bench routes per build
PROGRAM item 3's ipow step (8/8 soak routes, 1.13x) on the board's own top, with its T9 base on the same seeds
(research/data/ipow_bench/results.tsv, NEXTPNR_SEED 1-9; sizes research/data/ipow_dsp1_sizes_T9{,s75}_bench.vh; rule A
6-17 cells per route on both builds, informational). Base seed 7 and x0.75 seed 9 are the F7-select bitstream defect
(wrong answers at every corner; the header's md5 rule keeps them off the board); the other 16 routes pass 17/17 at
max, min and worst. nextpnr 9c732bc6303458df. From cells/:

    NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/ipow_dsp1_sizes_T9s75_bench.vh ./hw/build_bench.sh ipow
    md5sum build/hw/ipow_bench_gen/ipow_bench_gen.sdf    # 95a362ff = the route gated here
    CLK=0x00100C00 hw/loop_cost.sh ipow && cp build/hw/loop_cost_ipow.tsv build/hw/lc_ipow_s75.tsv
    NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/ipow_dsp1_sizes_T9_bench.vh ./hw/build_bench.sh ipow
    md5sum build/hw/ipow_bench_gen/ipow_bench_gen.sdf    # b6f11872
    CLK=0x00100C00 hw/loop_cost.sh ipow && cp build/hw/loop_cost_ipow.tsv build/hw/lc_ipow_t9.tsv
    python3 ../research/tools/loop_cost_judge.py ipow build/hw/lc_ipow_s75.tsv build/hw/lc_ipow_t9.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0 (all 11 of loop_cost.sh's ipow points answered by both builds). The ratio is
information: predicted 1.08-1.13 on this route (1.08-1.26 over 7 pairs; mean 1.16-1.18 by corner). Same meaning as #6/#7.

## 9. collatz per-cell sizes on the kernel bench -- 48/48 full-stack runs on 8 bench routes
**ON HOLD (2026-11-11).** These per-cell sizes shorten umux1/umux0 select paths: ulink_n14__0 18->11, ulink_n14__1 36->18 with SDELAY 3->1, and umux0 6->1. That is the class that failed collatz64 on one route at FAST_MIN (traced). Item 9 (#10) replaces it. This section's T3 build is still the base for #10.

PROGRAM item 3's collatz step (per-cell corner_audit sizes, 8/8 soak routes, 1.155x) on the board's own top, with its
T3 base on the same seeds (research/data/collatz_bench/results.tsv; sizes research/data/collatz_sizes_T3{,cs}_bench.vh;
rule A 4-9 cells per route on both builds, informational). nextpnr 9c732bc6303458df. From cells/:

    NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/collatz_sizes_T3cs_bench.vh ./hw/build_bench.sh collatz
    md5sum build/hw/collatz_bench_gen/collatz_bench_gen.sdf    # 1ab39716 = the route gated here
    CLK=0x00100C00 hw/loop_cost.sh collatz && cp build/hw/loop_cost_collatz.tsv build/hw/lc_collatz_cs.tsv
    NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/collatz_sizes_T3_bench.vh ./hw/build_bench.sh collatz
    md5sum build/hw/collatz_bench_gen/collatz_bench_gen.sdf    # 6134880a
    CLK=0x00100C00 hw/loop_cost.sh collatz && cp build/hw/loop_cost_collatz.tsv build/hw/lc_collatz_t3.tsv
    python3 ../research/tools/loop_cost_judge.py collatz build/hw/lc_collatz_cs.tsv build/hw/lc_collatz_t3.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0 (all 9 of loop_cost.sh's collatz points on both builds). Ratio predicted 1.12-1.15 on
this route (1.12-1.33 over 8; mean 1.19-1.21 by corner).

## 10. collatz BDC_CONST_DATA=1 + select-safe per-cell sizes on the kernel bench -- 24/24 full-stack runs on 8 bench routes
collatz's 3n+1 and n>>1 shifted by a constant that arrived as a data channel, which made them barrel shifters.
bdc/emit.py BDC_CONST_DATA=1 reads that channel's data as the literal it always carries; the channel, its link and
its handshake stay. Sizes are research/data/collatz_sizes_T3cdb.vh: corner_audit's per-cell proposal, with every mux
delay and every linked select channel (ulink_n14__0, ulink_n14__1, ulink_n_index_11) at max(proposal, T3). The
first version (T3cd) shortened those, the class that failed collatz64 on one route (JOURNAL 2026-11-11); it was
withdrawn. Bench top: research/data/collatz_cdb_bench/results.tsv, 24/24, decodes EQUIVALENT except seeds 4 and 8
(benign GND-buffer kind, checked). The T3 base is #9's second build. nextpnr 9c732bc6303458df. From cells/, on a
checkout with BDC_CONST_DATA (83cd6c77 or later):

    BDC_CONST_DATA=1 NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/collatz_sizes_T3cdb_bench.vh ./hw/build_bench.sh collatz
    grep -c "<< 32'h1" build/gen/collatz_kernel_bench.v    # must be >= 1: the flag took effect
    md5sum build/hw/collatz_bench_gen/collatz_bench_gen.sdf    # a7882dfa = the route gated here
    CLK=0x00100C00 hw/loop_cost.sh collatz && cp build/hw/loop_cost_collatz.tsv build/hw/lc_collatz_cd.tsv
    (T3 base: #9's commands for lc_collatz_t3.tsv, sdf 6134880a, if not already run)
    python3 ../research/tools/loop_cost_judge.py collatz build/hw/lc_collatz_cd.tsv build/hw/lc_collatz_t3.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0 (all 9 of loop_cost.sh's collatz points on both builds). Ratio predicted 1.15-1.17 on
this route (1.13-1.25 over 8).

## 11. ipow BDC_CONST_DATA=1 + per-cell sizes on the kernel bench -- 24/24 full-stack runs on 8 bench routes
**WITHDRAWN (2026-11-11).** The commands below are the held T9cdd version. They shorten ipow's select links (ulink_n17__*, ulink_n_index_15) and its mux delays. Re-gated select-safe (ipow_dsp1_sizes_T9cde, max(candidate, T9)), the build passes 24/24 on 8 bench routes, all EQUIVALENT. But it is no faster than item 7 (x0.75): 0.99-1.02x by corner. Kept for the record; not to be run.

**ON HOLD (2026-11-11).** The collatz64 build made the same way (BDC_CONST_DATA + corner_audit sizes) failed one bench route at FAST_MIN. The cause, traced: umux1's select link, shortened by corner_audit from 19 to 10 links, let a new token into the step counter inside its hold window. This item's sizes shorten the same select links: ulink_n14__0/n14__1/n_index_11 here, ulink_n17__*/n_index_15 for ipow. It passed 8 routes, but that hazard is route-dependent. It is being re-gated with every select link and mux delay kept at max(candidate, base) (`*_T3cdb` / `*_T9cde`). Do not run it until it is replaced.

ipow's ushrsi0 (`e >>= 1`) shifted by a constant 1 that arrived as a data channel, so it was a 32-bit barrel shifter
(and the home of the 76 constant-select F7 muxes behind the F7-select bitstream defect; the flag's routes have none).
Soak top: ipow_dsp1_sizes_T9cdd.vh 24/24 on 8 routes, 8/8 EQUIVALENT, 1.26-1.29x over T9. corner_audit's own
candidate (T9cd, umux3 1) FAILS: once the exit decision is fast, umux3's select arrives before the result and 1 link
does not cover the result's latch-to-mux path (traced, JOURNAL 2026-11-09); T9cdd keeps umux3 at T9's 4. Bench top:
research/data/ipow_cd_bench/results.tsv (sizes research/data/ipow_dsp1_sizes_T9cdd_bench.vh; rule A 12-19 cells per
route, informational; seeds 1 and 5 decode NOT_EQUIVALENT of the benign GND-buffer kind only). The T9 base is #8's
second build. nextpnr 9c732bc6303458df. From cells/, on a checkout with BDC_CONST_DATA (83cd6c77 or later):

    BDC_CONST_DATA=1 NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/ipow_dsp1_sizes_T9cdd_bench.vh ./hw/build_bench.sh ipow
    grep -c ">>> 32'h1" build/gen/ipow_kernel_bench.v    # must be >= 1: the flag took effect
    md5sum build/hw/ipow_bench_gen/ipow_bench_gen.sdf    # f0af6ff8 = the route gated here
    CLK=0x00100C00 hw/loop_cost.sh ipow && cp build/hw/loop_cost_ipow.tsv build/hw/lc_ipow_cd.tsv
    (T9 base: #8's commands for lc_ipow_t9.tsv, sdf b6f11872, if not already run)
    python3 ../research/tools/loop_cost_judge.py ipow build/hw/lc_ipow_cd.tsv build/hw/lc_ipow_t9.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0 (all 11 of loop_cost.sh's ipow points on both builds). Ratio predicted 1.20-1.22 on
this route (1.20-1.31 over 7 pairs; mean 1.24-1.27 by corner).

## 12. xorshift x0.5 + second latch (BDC_LINK_DEPTHS=ulink_n_trueResult_8=2, BDC_MERGE_OUT_LINK=ucontrol_merge0)
The owner's second-latch lead (research/data/itercost/second_latch): an extra latch at the two handshake couplings
that set the iteration's critical cycle. Measured on the full stack: 1.25-1.27x per round over x0.5 on 8 bench
routes; soak-top gate 24/24, 8/8 EQUIVALENT. Both knobs are measurement options in bdc/emit.py (off by default); the
two new stages keep bdc's default delays (unsized, long side). nextpnr 9c732bc6303458df. From cells/, on a checkout
with BDC_MERGE_OUT_LINK (5a4176cd or later):

    BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_MERGE_OUT_LINK=ucontrol_merge0 NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/xorshift_sizes_T3s50_bench.vh ./hw/build_bench.sh xorshift
    grep -c ucontrol_merge0_olink build/gen/xorshift_kernel_bench.v    # must be 1: the knobs took effect
    md5sum build/hw/xorshift_bench_gen/xorshift_bench_gen.sdf    # 1e51be7e = the route gated here
    CLK=0x00100C00 hw/loop_cost.sh xorshift && cp build/hw/loop_cost_xorshift.tsv build/hw/lc_xor_p8mo.tsv
    NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/xorshift_sizes_T3s50_bench.vh ./hw/build_bench.sh xorshift
    md5sum build/hw/xorshift_bench_gen/xorshift_bench_gen.sdf    # c5b8ca02 (item 4's x0.5 route)
    CLK=0x00100C00 hw/loop_cost.sh xorshift && cp build/hw/loop_cost_xorshift.tsv build/hw/lc_xor_s50.tsv
    python3 ../research/tools/loop_cost_judge.py xorshift build/hw/lc_xor_p8mo.tsv build/hw/lc_xor_s50.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0 (all 9 of loop_cost.sh's xorshift points on both builds). CLK=0x00100C00 (83.3 MHz)
matters here: at 100 MHz this route's harness operand register misses timing at the slow corner (traced, JOURNAL
2026-11-10). Ratio predicted 1.23-1.27 on this route (1.18-1.36 over 8).

## 13. collatz64 BDC_CONST_DATA=1 + select-safe per-cell sizes on the kernel bench -- 24/24 on 8 bench routes
The same change as #10 on the 64-bit kernel: two 64-bit barrel shifters removed. Sizes are research/data/collatz64_sizes_T4cdb.vh: corner_audit's per-cell proposal over 4 soak routes, with every mux delay and select link (ulink_n14__0/n14__1/n_index_11) at max(proposal, T4).
- Soak top: T4cd 24/24 and 8/8 EQUIVALENT, 1.23-1.24x.
- Bench top: T4cd was 23/24, and the failure traced to umux1's shortened select link; T4cdb is 24/24.
- Results: research/data/collatz64_cdb_bench/results.tsv. Seed 5 decodes NOT_EQUIVALENT of the benign GND-buffer kind (checked).
- The T4 base is #7's second build. nextpnr 9c732bc6303458df.

From cells/:

    BDC_CONST_DATA=1 NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/collatz64_sizes_T4cdb_bench.vh ./hw/build_bench.sh collatz64
    grep -c "<< 64'h1" build/gen/collatz64_kernel_bench.v    # must be >= 1
    md5sum build/hw/collatz64_bench_gen/collatz64_bench_gen.sdf    # b883dcb5 = the route gated here
    CLK=0x00100C00 hw/loop_cost.sh collatz64 && cp build/hw/loop_cost_collatz64.tsv build/hw/lc_cd.tsv
    (T4 base: #7's commands for lc_t4.tsv, sdf ebb49f83, if not already run)
    python3 ../research/tools/loop_cost_judge.py collatz64 build/hw/lc_cd.tsv build/hw/lc_t4.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0 (all 10 of loop_cost.sh's collatz64 points on both builds). Ratio predicted 1.15-1.17
on this route (1.14-1.35 over 7 pairs).


## 14. ipow x0.75 + BDC_LINK_FASTFALL=1 + BDC_MERGE_OUT_LINK=ucontrol_merge0 on the kernel bench -- 24/24 on 8 bench routes
The PROGRAM FIRST item's step 4 for ipow: research/tools/eventgraph/search.py, run on the timed event graph of item 7's
routes, picked these two existing bdc knobs on every seed (predicted 46.09 / 44.92 / 45.06 / 44.08 ns per iteration;
measured on the itercost stack 46.84 / 45.02 / 46.04 / 45.24, i.e. 1.185 / 1.152 / 1.179 / 1.199x over x0.75).
- Full gate (research/tools/eventgraph/bench_gate.sh; research/data/eventgraph/gate/): seeds 1-6, 8, 9 x SLOW_MAX /
  FAST_MIN / worst (chains 0.21, CARRY4/F7F8/FF 1, rest 0.288, + M) -> 24/24 PASS 17/17 (b = 3 at e = 2^k-1 for 11 k, and
  6 mixed-sign vectors; oracle from kernels/ipow/ipow.c). Seeds 5, 6, 9 decode NOT_EQUIVALENT of the benign GND-buffer
  F7/CARRY4 kinds (checked). Seed 7 excluded: its bitstream leaves a constant-D harness flop without BFFMUX (the nextpnr
  gap; research/tools/ffmux_scan.py).
- Sizes are item 7's (ipow_dsp1_sizes_T9s75_bench.vh); the new link keeps bdc's defaults (SELECT_PAD 4 / ACK_PAD 6).
  nextpnr 9c732bc6303458df. From cells/:

    BDC_LINK_FASTFALL=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/ipow_dsp1_sizes_T9s75_bench.vh ./hw/build_bench.sh ipow
    grep -c ucontrol_merge0_olink build/gen/ipow_kernel_bench.v    # must be 1: the knob took effect
    md5sum build/hw/ipow_bench_gen/ipow_bench_gen.sdf    # e5000e23 = the route gated here
    python3 ../research/tools/ffmux_scan.py build/hw/ipow_bench_gen/ipow_bench_gen.fasm; echo "exit $?"   # must be 0
    CLK=0x00100C00 hw/loop_cost.sh ipow && cp build/hw/loop_cost_ipow.tsv build/hw/lc_ipow_fm.tsv
    NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/ipow_dsp1_sizes_T9s75_bench.vh ./hw/build_bench.sh ipow
    md5sum build/hw/ipow_bench_gen/ipow_bench_gen.sdf    # 95a362ff (item 7's route)
    CLK=0x00100C00 hw/loop_cost.sh ipow && cp build/hw/loop_cost_ipow.tsv build/hw/lc_ipow_s75.tsv
    python3 ../research/tools/loop_cost_judge.py ipow build/hw/lc_ipow_fm.tsv build/hw/lc_ipow_s75.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0 (all 11 of loop_cost.sh's ipow points on both builds give the oracle's answer). Ratio
predicted 1.18-1.19 on this route. What it would mean: PASS with the ratio = fast fall and the merge-output latch are
safe on silicon and the event graph's choice carries; FAIL of the new build only = fast fall (RFAST) or the extra
latch has a margin the full stack does not see (send both logs).


## 15. xorshift x0.5 + BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 + BDC_MERGE_OUT_LINK=ucontrol_merge0 + BDC_LINK_FASTFALL=1 -- 24/24 on 8 bench routes
Item 11's two latches plus link fast fall: the set research/tools/eventgraph/search.py picks on all five x0.5 base
graphs (research/data/eventgraph). Itercost-stack period per iteration, seeds 1, 3-9: 29.14 / 29.54 / 32.42 / 28.46 /
29.14 / 30.28 / 31.10 / 29.86 ns (mean 30.0; x0.5 39.5, item 11's p8mo 31.8 on seeds 1-4).
- Full gate (bench_gate.sh, 17 vectors, oracle from kernels/xorshift/xorshift.c incl. 200 and 1000 rounds): seeds 1, 3-9
  x SLOW_MAX / FAST_MIN / worst+M -> 24/24 PASS 17/17; 7/8 EQUIVALENT, seed 1 the benign GND-buffer F7 kind (checked).
  Seed 2 excluded: AFF without AFFMUX (the nextpnr constant-D flop gap; ffmux_scan.py).
- New stages keep bdc's defaults (inner SDELAY 3, merge link SELECT_PAD 4 / ACK_PAD 6). nextpnr 9c732bc6303458df.
  From cells/:

    BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/xorshift_sizes_T3s50_bench.vh ./hw/build_bench.sh xorshift
    grep -c ucontrol_merge0_olink build/gen/xorshift_kernel_bench.v    # must be 1
    grep -c "RFAST(1)" build/gen/xorshift_kernel_bench.v               # must be 8: fast fall took effect
    md5sum build/hw/xorshift_bench_gen/xorshift_bench_gen.sdf    # 169ce4d6 = the route gated here
    python3 ../research/tools/ffmux_scan.py build/hw/xorshift_bench_gen/xorshift_bench_gen.fasm; echo "exit $?"   # must be 0
    CLK=0x00100C00 hw/loop_cost.sh xorshift && cp build/hw/loop_cost_xorshift.tsv build/hw/lc_xor_pmf.tsv
    (x0.5 base: #12's commands for lc_xor_s50.tsv, sdf c5b8ca02, if not already run)
    python3 ../research/tools/loop_cost_judge.py xorshift build/hw/lc_xor_pmf.tsv build/hw/lc_xor_s50.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0. Ratio predicted 1.33-1.35 on this route. Run item 11 (#12) too if the board time
allows: pmf / p8mo isolates fast fall (predicted 1.07 on seed 1).


## 16. collatz BDC_CONST_DATA=1 + T3cdb sizes + BDC_LINK_FASTFALL=1 + BDC_MERGE_OUT_LINK=ucontrol_merge0 -- 24/24 on 8 bench routes
Item 9's design with the two knobs research/tools/eventgraph/search.py picks on all four of its base graphs (predicted
1.19x; measured on the itercost stack, seeds 1-8: 1.132 / 1.164 / 1.231 / 1.150 / 1.174 / 1.210 / 1.157 / 1.126, mean
1.17x; periods 56.3-60.7 ns against 67.1-69.5).
- Full gate (bench_gate.sh, 13 vectors: n = 27, 97, 871, 6171, 703 and 2^k; oracle from kernels/collatz/collatz.c):
  seeds 1-8 x SLOW_MAX / FAST_MIN / worst+M -> 24/24 PASS 13/13; 7/8 EQUIVALENT, seed 8 the benign GND-buffer F7 kind
  (checked); ffmux_scan.py clean on all 8. The select paths keep item 9's (select-safe) sizes; fast fall acts on link
  rdlys and 2-input mux udlys only (the rising edges keep the full matched delays).
- nextpnr 9c732bc6303458df. From cells/:

    BDC_CONST_DATA=1 BDC_LINK_FASTFALL=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/collatz_sizes_T3cdb_bench.vh ./hw/build_bench.sh collatz
    grep -c ucontrol_merge0_olink build/gen/collatz_kernel_bench.v    # must be 1
    md5sum build/hw/collatz_bench_gen/collatz_bench_gen.sdf    # e20325f3 = the route gated here
    python3 ../research/tools/ffmux_scan.py build/hw/collatz_bench_gen/collatz_bench_gen.fasm; echo "exit $?"   # must be 0
    CLK=0x00100C00 hw/loop_cost.sh collatz && cp build/hw/loop_cost_collatz.tsv build/hw/lc_col_fm.tsv
    BDC_CONST_DATA=1 NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/collatz_sizes_T3cdb_bench.vh ./hw/build_bench.sh collatz
    md5sum build/hw/collatz_bench_gen/collatz_bench_gen.sdf    # a7882dfa (item 9's route)
    CLK=0x00100C00 hw/loop_cost.sh collatz && cp build/hw/loop_cost_collatz.tsv build/hw/lc_col_cdb.tsv
    python3 ../research/tools/loop_cost_judge.py collatz build/hw/lc_col_fm.tsv build/hw/lc_col_cdb.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0. Ratio predicted 1.13 on this route (1.13-1.23 over 8).


## 17. collatz64 BDC_CONST_DATA=1 + T4cdb + BDC_LINK_FASTFALL=1 + BDC_MERGE_OUT_LINK=ucontrol_merge0 -- 24/24 on 8 bench routes
Item 12's design with the two knobs research/tools/eventgraph/search.py picks on its base graphs (predicted 1.15-1.17x;
itercost periods seeds 1, 2, 4-9: 54.85 / 56.16 / 57.54 / 57.33 / 54.99 / 57.14 / 55.65 / 58.05 ns against item 12's
60.8-66.1).
- Full gate (bench_gate.sh, 14 vectors, n up to 63728127 = 949 steps, oracle from kernels/collatz/collatz.c): seeds 1,
  2, 4-9 x SLOW_MAX / FAST_MIN / worst+M -> 24/24 PASS 14/14; 6/8 EQUIVALENT, seeds 5 and 9 the benign GND-buffer F7
  kind (checked). Seed 3 excluded: C5FF without C5FFMUX (the nextpnr constant-D flop gap; ffmux_scan.py).
- nextpnr 9c732bc6303458df. From cells/:

    BDC_CONST_DATA=1 BDC_LINK_FASTFALL=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/collatz64_sizes_T4cdb_bench.vh ./hw/build_bench.sh collatz64
    grep -c ucontrol_merge0_olink build/gen/collatz64_kernel_bench.v    # must be 1
    md5sum build/hw/collatz64_bench_gen/collatz64_bench_gen.sdf    # 2c06cd36 = the route gated here
    python3 ../research/tools/ffmux_scan.py build/hw/collatz64_bench_gen/collatz64_bench_gen.fasm; echo "exit $?"   # must be 0
    CLK=0x00100C00 hw/loop_cost.sh collatz64 && cp build/hw/loop_cost_collatz64.tsv build/hw/lc_c64_fm.tsv
    (item 12's base: #13's commands for lc_cd.tsv, sdf b883dcb5, if not already run)
    python3 ../research/tools/loop_cost_judge.py collatz64 build/hw/lc_c64_fm.tsv build/hw/lc_cd.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0. Ratio predicted ~1.20 on this route.

## 18. xorshift item 14 + BDC_MERGE_RES_LINK + BDC_RING_COUNT_OLINKS + BDC_FORK_OUT_LINK=n11__0 -- 24/24 on 8 bench routes
The 15 ns lead's levers 1-3 (research/data/fifteen/README.md): a latch on the result branch of the merge-output fork, the
ring floor counting the merge's new latches (the counter ring's 3-stage pipe becomes one stage), and a latch on the
rounds fork's steer branch. Each found by the timed event graph: both rings closed through a fork whose acknowledge waited
on a loop steer that waits for the loop compare. Itercost periods seeds 1, 3-9: 19.86 / 20.64 / 20.91 / 21.36 / 19.58 /
21.36 / 20.39 / 20.70 ns (mean 20.60; item 14 30.0, x0.5 39.5).
- Full gate (bench_gate.sh, 17 vectors incl. 200 and 1000 rounds, oracle from kernels/xorshift/xorshift.c): seeds 1, 3-9
  x SLOW_MAX / FAST_MIN / worst+M -> 24/24 PASS 17/17; 7/8 EQUIVALENT, seed 6 the benign GND-buffer F7 kind (checked);
  ffmux_scan clean on all 8. The three knobs are opt-in (default output byte-identical on all six kernels).
- nextpnr 9c732bc6303458df. From cells/, on a checkout with the three knobs (922fca2b and later):

    BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/xorshift_sizes_T3s50_bench.vh ./hw/build_bench.sh xorshift
    grep -c "ucontrol_merge0_rlink\|ulink_n11__0_folink" build/gen/xorshift_kernel_bench.v    # must be 2 (instances)
    md5sum build/hw/xorshift_bench_gen/xorshift_bench_gen.sdf    # e88b0712 = the route gated here
    python3 ../research/tools/ffmux_scan.py build/hw/xorshift_bench_gen/xorshift_bench_gen.fasm; echo "exit $?"   # must be 0
    CLK=0x00100C00 hw/loop_cost.sh xorshift && cp build/hw/loop_cost_xorshift.tsv build/hw/lc_xor_l3.tsv
    (x0.5 base: #12's commands for lc_xor_s50.tsv, sdf c5b8ca02, if not already run)
    python3 ../research/tools/loop_cost_judge.py xorshift build/hw/lc_xor_l3.tsv build/hw/lc_xor_s50.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0. Ratio predicted ~1.97 over x0.5 on this route (1.85-1.97 over 8). If board time
allows, also run item 14 (#15): l3 / item 14 isolates the three new latches (predicted 1.47 on seed 1).


## 19. xorshift item 17 + BDC_NO_LINK=ulink_n30__1 -- 24/24 on 8 bench routes
**ON HOLD 2026-11-13** (see list item 18): rule E -4.65 ns raw at ucond_br6 on this route (sdf c6519c91) at the nominal
SDF; the gate cannot exercise long counter carries. Kept for the record.
Lever 5 of research/data/fifteen: without the rule-1 (measurability) link between the i+1 adder and the compare, the
compare reads the adder's output directly. ring_depths() still enforces every ring's floor (nothing else changed in the
emitted kernel). tighten.py loses that start point; the full gate decided correctness instead. Itercost periods seeds 1,
3-9: 18.45 / 17.64 / 18.71 / 20.15 / 18.72 / 17.37 / 17.95 / 20.53 ns (mean 18.69; item 17 20.60, item 14 30.0).
- Full gate (bench_gate.sh, 17 vectors incl. 200 and 1000 rounds): seeds 1, 3-9 x SLOW_MAX / FAST_MIN / worst+M ->
  24/24 PASS 17/17; 6/8 EQUIVALENT, seeds 3 and 6 the benign GND-buffer F7 kind (checked); ffmux_scan clean.
- nextpnr 9c732bc6303458df. From cells/, on a checkout with BDC_NO_LINK (7d9af285 or later):

    BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_NO_LINK=ulink_n30__1 NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/xorshift_sizes_T3s50_bench.vh ./hw/build_bench.sh xorshift
    grep -c "ulink_n30__1 (" build/gen/xorshift_kernel_bench.v    # must be 0: the link is gone
    md5sum build/hw/xorshift_bench_gen/xorshift_bench_gen.sdf    # c6519c91 = the route gated here
    python3 ../research/tools/ffmux_scan.py build/hw/xorshift_bench_gen/xorshift_bench_gen.fasm; echo "exit $?"   # must be 0
    CLK=0x00100C00 hw/loop_cost.sh xorshift && cp build/hw/loop_cost_xorshift.tsv build/hw/lc_xor_l5.tsv
    (x0.5 base: #12's commands for lc_xor_s50.tsv, sdf c5b8ca02, if not already run)
    python3 ../research/tools/loop_cost_judge.py xorshift build/hw/lc_xor_l5.tsv build/hw/lc_xor_s50.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0. Ratio predicted ~2.12 over x0.5 on this route. What it would mean: PASS = the
measurability link is not needed for correctness on silicon either; FAIL with item 17 passing = it was (send both logs).


## 20. ipow x0.75 + BDC_LINK_FASTFALL=1 + BDC_MERGE_OUT_LINK + BDC_MERGE_RES_LINK=ucontrol_merge0 -- 24/24 on 8 bench routes
Item 13 plus the result-branch latch (research/data/fifteen, lever 1): the merge-output fork's acknowledge no longer
waits for the loop-control join. Itercost periods seeds 1-8: 39.78 / 39.97 / 38.78 / 38.07 / 37.96 / 39.74 / 38.22 /
40.62 ns, mean 39.14 (item 13 ~45.8: 1.17x; predicted 1.16-1.21x per seed).
- Full gate (bench_gate.sh, 17 vectors, oracle from kernels/ipow/ipow.c): seeds 1-8 x SLOW_MAX / FAST_MIN / worst+M ->
  24/24 PASS 17/17; 4/8 EQUIVALENT, seeds 3, 4, 6, 7 the benign GND-buffer F7/CARRY4 kinds; ffmux_scan clean.
- nextpnr 9c732bc6303458df. From cells/, on a checkout with BDC_MERGE_RES_LINK (922fca2b or later):

    BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/ipow_dsp1_sizes_T9s75_bench.vh ./hw/build_bench.sh ipow
    grep -c "ucontrol_merge0_rlink (" build/gen/ipow_kernel_bench.v    # must be 1
    md5sum build/hw/ipow_bench_gen/ipow_bench_gen.sdf    # a6a2951b = the route gated here
    python3 ../research/tools/ffmux_scan.py build/hw/ipow_bench_gen/ipow_bench_gen.fasm; echo "exit $?"   # must be 0
    CLK=0x00100C00 hw/loop_cost.sh ipow && cp build/hw/loop_cost_ipow.tsv build/hw/lc_ipow_r.tsv
    (item 13: #14's commands for lc_ipow_fm.tsv, sdf e5000e23, if not already run)
    python3 ../research/tools/loop_cost_judge.py ipow build/hw/lc_ipow_r.tsv build/hw/lc_ipow_fm.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0. Ratio predicted ~1.18 on this route.


## 21. collatz item 15 + BDC_MERGE_RES_LINK=ucontrol_merge0 -- 24/24 on 8 bench routes
Item 15 plus the result-branch latch (research/data/fifteen, lever 1). Itercost periods seeds 1-8: 47.56 / 47.84 /
48.10 / 48.47 / 49.08 / 49.17 / 49.17 / 51.46 ns, mean 48.86 (item 15 58.49: 1.20x). Dynamatic 14.05.
- Full gate (bench_gate.sh, 13 vectors, oracle from kernels/collatz/collatz.c): seeds 1-8 x SLOW_MAX / FAST_MIN /
  worst+M -> 24/24 PASS 13/13; 5/8 EQUIVALENT, seeds 3, 7, 8 the benign GND-buffer F7 kind; ffmux_scan clean.
- nextpnr 9c732bc6303458df. From cells/, on a checkout with BDC_MERGE_RES_LINK (922fca2b or later):

    BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/collatz_sizes_T3cdb_bench.vh ./hw/build_bench.sh collatz
    grep -c "ucontrol_merge0_rlink (" build/gen/collatz_kernel_bench.v    # must be 1
    md5sum build/hw/collatz_bench_gen/collatz_bench_gen.sdf    # 44536c3c = the route gated here
    python3 ../research/tools/ffmux_scan.py build/hw/collatz_bench_gen/collatz_bench_gen.fasm; echo "exit $?"   # must be 0
    CLK=0x00100C00 hw/loop_cost.sh collatz && cp build/hw/loop_cost_collatz.tsv build/hw/lc_col_r.tsv
    (item 15: #16's commands for lc_col_fm.tsv, sdf e20325f3, if not already run)
    python3 ../research/tools/loop_cost_judge.py collatz build/hw/lc_col_r.tsv build/hw/lc_col_fm.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0. Ratio predicted ~1.25 on this route.


## 22. collatz64 item 16 + BDC_MERGE_RES_LINK=ucontrol_merge0 -- 24/24 on 8 bench routes
Item 16 plus the result-branch latch (research/data/fifteen, lever 1). Itercost periods seeds 1, 2, 4-9: 46.95 / 46.37 /
46.01 / 47.75 / 46.88 / 51.23 / 47.98 / 47.95 ns, mean 47.64 (item 16 56.46: 1.19x). Dynamatic 17.84.
- Full gate (bench_gate.sh, 14 vectors up to 949 steps): seeds 1, 2, 4-9 x SLOW_MAX / FAST_MIN / worst+M -> 24/24 PASS
  14/14; 6/8 EQUIVALENT, seeds 5 and 9 the benign GND-buffer CARRY4/F7 kinds; ffmux_scan clean. (Seed 3 is excluded for
  every collatz64 build of this family: item 16's seed 3 route had the C5FF gap.)
- nextpnr 9c732bc6303458df. From cells/, on a checkout with BDC_MERGE_RES_LINK (922fca2b or later):

    BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/collatz64_sizes_T4cdb_bench.vh ./hw/build_bench.sh collatz64
    grep -c "ucontrol_merge0_rlink (" build/gen/collatz64_kernel_bench.v    # must be 1
    md5sum build/hw/collatz64_bench_gen/collatz64_bench_gen.sdf    # 29655e86 = the route gated here
    python3 ../research/tools/ffmux_scan.py build/hw/collatz64_bench_gen/collatz64_bench_gen.fasm; echo "exit $?"   # must be 0
    CLK=0x00100C00 hw/loop_cost.sh collatz64 && cp build/hw/loop_cost_collatz64.tsv build/hw/lc_c64_r.tsv
    (item 16: #17's commands for lc_c64_fm.tsv, sdf 2c06cd36, if not already run)
    python3 ../research/tools/loop_cost_judge.py collatz64 build/hw/lc_c64_r.tsv build/hw/lc_c64_fm.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0. Ratio predicted ~1.17 on this route.

## 23. collatz item 20 + BDC_NO_LINK=ulink_n28__1 + per-cell full-range sizes (T3cdb_nl2) -- 81/81 gate, static clean, 28 routes
research/data/fifteen (2026-11-14). The rule-1 link between uselect0 and ucmpi2 removed (lever 5; statically checked,
rule E raw +1.9..+2.3 ns at nominal on the collatz routes); then corner_audit at nominal and worst on 8 routes, per-cell
max, select paths never shortened, merges kept at 2 (at 1 they missed rule A on 7 of 31 fresh routes). Farm request
fcolsz2: 28 routes built, period median 41.15 ns, mean 41.22, 38.85-43.26 (item 20: 48.86, 1.19x); gate 81/81 PASS
(SLOW_MAX / FAST_MIN / worst+M, 13/13 each); static CLEAN at both corners on all 27 evaluated routes. Full input range
under the owner's rule. Dynamatic 14.05. Hold check (trace-measured, FAST_MIN, select-flipping vectors; farm fcolsz2h,
31 routes): no violation (the two old-tool flags re-measured clean, ulink_n_index_11 +1047 ps on seed 6).
- nextpnr 9c732bc6303458df. From cells/:

    BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_NO_LINK=ulink_n28__1 NEXTPNR_SEED=26 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/collatz_sizes_T3cdb_nl2_bench.vh ./hw/build_bench.sh collatz
    grep -c "ulink_n28__1 (" build/gen/collatz_kernel_bench.v    # must be 0
    md5sum build/hw/collatz_bench_gen/collatz_bench_gen.sdf    # bc2fe0c8 = the route gated here
    python3 ../research/tools/ffmux_scan.py build/hw/collatz_bench_gen/collatz_bench_gen.fasm; echo "exit $?"   # must be 0
    CLK=0x00100C00 hw/loop_cost.sh collatz && cp build/hw/loop_cost_collatz.tsv build/hw/lc_col_sz.tsv
    (item 20: #21's commands for lc_col_r.tsv, if not already run)
    python3 ../research/tools/loop_cost_judge.py collatz build/hw/lc_col_sz.tsv build/hw/lc_col_r.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0. Ratio predicted ~1.19 over item 20 on this route.

## 24. xorshift item 17 + latch on the adder's steer branch + full-range sizes (fr3) -- 87/87 gate, static and hold checked, 30 routes
research/data/fifteen (2026-11-14). The full-range re-baseline of item 17 under the owner's rule: the counter's add and
the datapath sized by the static check at nominal and worst on 5 + 8 routes (uaddi0 6 -> 13, umux0 / umux2 1 -> 2,
uxori1 2 -> 7, uxori2 3 -> 7, umux3 1 -> 14, merges 2). The latch on the adder fork's steer branch removes the hold race
that failed xf2 seed 1 at FAST_MIN (the counter's loop-back pipe was fed by the adder through a steer; JOURNAL). Farm
fxf4: 30 routes built (30: harness < 83 MHz; 9: ffmux_scan flag, excluded); period median 23.49 ns, mean 23.30,
21.00-24.75; gate 87/87 (SLOW_MAX / FAST_MIN / worst+M, 17/17 each); static check CLEAN at both corners on 28 (seed 18:
uxori1 -81 ps at worst, the datapath, spanned by the vectors; seed 13 incomplete); hold check (hold_trace, FAST_MIN,
rounds 3 / 4 / 8 / 5 in sequence) no violation on any route; locally re-checked seeds 1, 4, 7 with the corrected tool,
tightest +715 ps. Correct for any 32-bit rounds as far as the static check and the gate show. Dynamatic 12.73.
- nextpnr 9c732bc6303458df. From cells/:

    BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0,n30__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 NEXTPNR_SEED=10 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/xorshift_sizes_T3s50_fr3_bench.vh ./hw/build_bench.sh xorshift
    grep -c "ulink_n30__0_folink (" build/gen/xorshift_kernel_bench.v    # must be 1
    md5sum build/hw/xorshift_bench_gen/xorshift_bench_gen.sdf    # 2f825834 = the route gated here
    python3 ../research/tools/ffmux_scan.py build/hw/xorshift_bench_gen/xorshift_bench_gen.fasm; echo "exit $?"   # must be 0
    CLK=0x00100C00 hw/loop_cost.sh xorshift && cp build/hw/loop_cost_xorshift.tsv build/hw/lc_xor_fr.tsv
    (x0.5 base: #12's commands for lc_xor_s50.tsv, sdf c5b8ca02, if not already run)
    python3 ../research/tools/loop_cost_judge.py xorshift build/hw/lc_xor_fr.tsv build/hw/lc_xor_s50.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0. Ratio predicted ~1.66 over x0.5 on this route (39.06 / 23.5).

## 25. collatz64 item 21 + BDC_NO_LINK=ulink_n30__1 -- 90/90 gate, static and hold checked, 30 routes
research/data/fifteen (2026-11-14). Lever 5 on collatz64: the rule-1 link between uselect0 and ucmpi2 removed; rule E
from the removed link's source checked statically (raw +1.5..+1.8 ns at nominal), so the full-range rule's concern on
xorshift's lever 5 does not apply here. Farm fc64nl / fc64nlh: 30 routes built (7: farm task gave no
eval; 11: no build); period median 45.23 ns, mean 45.23, 42.46-47.09 (item 21: 47.64 over 8 routes);
gate 90/90 (SLOW_MAX / FAST_MIN / worst+M, 14/14 each). Static check: on every route only umux2's tighten row (-1.3 to
-2.5 ns at nominal), the select-latch pairing shown by trace to be a false path (JOURNAL 2026-11-14: select data
settles >= 5.9 ns before the request on 12 transactions with 7 select flips). Hold check (trace, FAST_MIN): clean
(seed 3, the worst old-tool reading, re-measured +734 ps). Dynamatic 17.84.
- nextpnr 9c732bc6303458df. From cells/:

    BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_NO_LINK=ulink_n30__1 NEXTPNR_SEED=17 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/collatz64_sizes_T4cdb_bench.vh ./hw/build_bench.sh collatz64
    grep -c "ulink_n30__1 (" build/gen/collatz64_kernel_bench.v    # must be 0
    md5sum build/hw/collatz64_bench_gen/collatz64_bench_gen.sdf    # 3a370768 = the route gated here
    python3 ../research/tools/ffmux_scan.py build/hw/collatz64_bench_gen/collatz64_bench_gen.fasm; echo "exit $?"   # must be 0
    CLK=0x00100C00 hw/loop_cost.sh collatz64 && cp build/hw/loop_cost_collatz64.tsv build/hw/lc_c64_nl.tsv
    (item 21: #22's commands for lc_c64_r.tsv, if not already run)
    python3 ../research/tools/loop_cost_judge.py collatz64 build/hw/lc_c64_nl.tsv build/hw/lc_c64_r.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0. Ratio predicted ~1.05 over item 21 on this route.

## 26. collatz item 22's structure + pre_eq2 (exit test n == 2) + nl4 hold pads -- 96/96 gate, static and hold clean, 32 routes
research/JOURNAL.md 2026-11-15. collatz's loop computes n' = even ? n >> 1 : 3n + 1 and exits when n' == 1. In w-bit
two's complement that is n == 2 (n even: n >> 1 == 1 iff n == 2; n odd: 3n + 1 == 1 iff 3n == 0 mod 2^w iff n == 0, not
odd). pre_eq2.py rewrites the handshake MLIR's cmpi2 to read the loop's n against a constant 2, so the compare runs with
the update instead of after it (bdc unchanged; simcheck PASS incl. n = 1, 2, 3). The rule-1 link between the select
and the compare that item 22 dropped no longer exists (the select's fork is gone). Farm fceq: 32 routes, period
median 35.82 ns, mean 35.84, 33.38-38.51; gate 96/96 (SLOW_MAX / FAST_MIN / worst+M, 13/13 each); static check
(corner_audit, nominal and worst, measured-residual guards, C-element joins) A / A' / E clean on 32/32; hold / close
(H / I) clean on 31/32 (seed 5 I -12 ps); hold_trace and hold_bits (FAST_MIN, select-flipping vectors) clean on 32/32;
fasm_equiv EQUIVALENT on 29, the benign constant-LUT -> F7 kind on 3 (10, 27, 29); ffmux clean on 32. Board seed 24:
every check clean.
- nextpnr 9c732bc6303458df. From cells/, on claude/research at or after this commit:

    cp ../build/frontend/collatz/comp/handshake_transformed.mlir /tmp/collatz_hs_orig.mlir
    cp ../research/data/fifteen/collatz_preeq2.mlir ../build/frontend/collatz/comp/handshake_transformed.mlir
    BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 NEXTPNR_SEED=24 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/collatz_sizes_T3cdb_nl4_bench.vh ./hw/build_bench.sh collatz
    cp /tmp/collatz_hs_orig.mlir ../build/frontend/collatz/comp/handshake_transformed.mlir
    grep -c "usinkeq2" build/gen/collatz_kernel_bench.v    # must be 1: the rewrite is in (the freed constant-1 output's sink)
    md5sum build/hw/collatz_bench_gen/collatz_bench_gen.sdf    # e001dc27 = the route gated here
    python3 ../research/tools/ffmux_scan.py build/hw/collatz_bench_gen/collatz_bench_gen.fasm; echo "exit $?"   # must be 0
    CLK=0x00100C00 hw/loop_cost.sh collatz && cp build/hw/loop_cost_collatz.tsv build/hw/lc_col_eq.tsv
    (item 22: #23's commands for lc_col_sz.tsv, if not already run)
    python3 ../research/tools/loop_cost_judge.py collatz build/hw/lc_col_eq.tsv build/hw/lc_col_sz.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0. Ratio predicted ~1.14 over item 22 (41.10 ns on its route vs 35.92 here). A FAIL with
item 22 passing would mean the rewrite or its sizes do not hold on silicon (send both logs).

## 27. collatz64 item 24's structure + pre_eq2 (exit test n == 2) + h2 hold pads -- 90/90 gate on 30 routes
research/JOURNAL.md 2026-11-15. The same rewrite as #26 at 64 bits (n == 2 iff n' == 1 in 64-bit two's complement;
simcheck PASS incl. n = 1, 27, 113383). Farm fc64eq: 30 routes built, median 36.23 ns, mean 36.15, 34.38-38.15;
paired with fc64h (round-1 pads, same knobs otherwise) -9.0 ns on 30/30. Gate 14/14 at SLOW_MAX / FAST_MIN / worst+M
on 29 routes; seed 32 fails 0/14 at SLOW_MAX and worst on the bits-decoded netlist and is flagged by ffmux_scan and by
fasm_equiv ("cell in routed JSON, not configured by the bits": a dfflegalize flop, the nextpnr FASM gap of
2026-11-08) -- excluded, like seed 5 (same flag). Static check (corner_audit, C-element joins): umux2 rule A -1.7..-2.1 ns
at both corners on every route, the select-latch false path traced 2026-11-14 for items 21 / 24; umux0 A -45..-135 on
seeds 4, 7, 15; ucmpi2 A -29 at worst on seed 31; H / I clean but seed 13 (H -305). hold_trace / hold_bits clean on 30.
fasm_equiv: EQUIVALENT or the benign constant-LUT -> F7 / CARRY4-DI kind on the 28 others. Board seed 25: EQUIVALENT,
ffmux clean, gate 3 x 14/14, only umux2's row, hold checks clean.
- nextpnr 9c732bc6303458df. From cells/:

    cp ../build/frontend/collatz64/comp/handshake_transformed.mlir /tmp/c64_hs_orig.mlir
    cp ../research/data/fifteen/collatz64_preeq2.mlir ../build/frontend/collatz64/comp/handshake_transformed.mlir
    BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 NEXTPNR_SEED=25 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/collatz64_sizes_T4cdb_h2_bench.vh ./hw/build_bench.sh collatz64
    cp /tmp/c64_hs_orig.mlir ../build/frontend/collatz64/comp/handshake_transformed.mlir
    grep -c "usinkeq2" build/gen/collatz64_kernel_bench.v    # must be 1: the rewrite is in
    md5sum build/hw/collatz64_bench_gen/collatz64_bench_gen.sdf    # 6982a9d5 = the route gated here
    python3 ../research/tools/ffmux_scan.py build/hw/collatz64_bench_gen/collatz64_bench_gen.fasm; echo "exit $?"   # must be 0
    CLK=0x00100C00 hw/loop_cost.sh collatz64 && cp build/hw/loop_cost_collatz64.tsv build/hw/lc_c64_eq.tsv
    (item 24: #25's commands for its loop_cost tsv, if not already run)
    python3 ../research/tools/loop_cost_judge.py collatz64 build/hw/lc_c64_eq.tsv build/hw/lc_c64_nl.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0. Ratio predicted ~1.25 over item 24 (45.19 ns on its route vs 36.27 here).

## 28. xorshift item 23's structure + pre_dec (loop test i < n-1) + fr4 sizes -- 93/93 gate, 31 routes
research/JOURNAL.md 2026-11-15. The loop test `i + 1 < n` (n round the rounds ring) becomes `i < m`, m = n - 1 computed
once before the loop and carried round the ring instead of n. Exact on every reachable state: the loop is entered only
when n > 0 (cmpi0), so m does not wrap; inside, i + 1 <= n <= INT_MAX. The compare starts with the add instead of after
it (simcheck PASS incl. rounds 0, 1, -1, INT_MIN). Farm fxd: 31 routes; the itercost period alternates between two
values on many routes (seed 10: 18924 / 19382 ps), so the single-period P exists on some routes only: median 19.39 ns
over those; latency median 417 cycles (394-457) vs fxf5 499-class. Gate 93/93 (17/17 x 3 corners); static A / A' / E
clean at nominal and worst (C-element joins) on 29/31; tighten's unsized bundled "a" row on ucmpi1 as on every
xorshift route; H / I / F rows on 11 routes (falseResult_9, ulink_n25, trueResult_8 stage rows, -6..-355 ps; uxori1.udly
F -109 on seed 11); hold_trace / hold_bits clean on 31; ffmux clean on 31; fasm_equiv EQUIVALENT or the benign
constant-LUT -> F7 / CARRY4-DI kind on 8. Board seed 2: every row clean.
- nextpnr 9c732bc6303458df. From cells/:

    cp ../build/frontend/xorshift/comp/handshake_transformed.mlir /tmp/xor_hs_orig.mlir
    cp ../research/data/fifteen/xorshift_predec.mlir ../build/frontend/xorshift/comp/handshake_transformed.mlir
    BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 NEXTPNR_SEED=2 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/xorshift_sizes_T3s50_fr4_bench.vh ./hw/build_bench.sh xorshift
    cp /tmp/xor_hs_orig.mlir ../build/frontend/xorshift/comp/handshake_transformed.mlir
    grep -c "uforkdec0 (" build/gen/xorshift_kernel_bench.v    # must be 1: the rewrite is in
    md5sum build/hw/xorshift_bench_gen/xorshift_bench_gen.sdf    # a9bdac53 = the route gated here
    python3 ../research/tools/ffmux_scan.py build/hw/xorshift_bench_gen/xorshift_bench_gen.fasm; echo "exit $?"   # must be 0
    CLK=0x00100C00 hw/loop_cost.sh xorshift && cp build/hw/loop_cost_xorshift.tsv build/hw/lc_xor_dec.tsv
    (item 23: #24's commands for lc_xor_fr.tsv, if not already run)
    python3 ../research/tools/loop_cost_judge.py xorshift build/hw/lc_xor_dec.tsv build/hw/lc_xor_fr.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0. Ratio predicted ~1.2 over item 23 (23.31 ns on its route). The bench masks rounds to 12
bits; the full range rests on the static check (pre_dec's identity holds for every rounds the C allows).

## 29. collatz item 25's structure + select links at 3 (fcsel3m) -- 28 routes, every check clean on every route
research/JOURNAL.md 2026-11-15 (evening). The select links were 18 / 36 / 15 elements under the withdrawn select rule;
line_account.py showed ulink_n14__1's 36 elements were 27.4 of item 25's 35.9 ns iteration. At 0 the gate passes but
rule E fails at the muxes (to -393 ps at 1); at 2 on 2 of 29 routes; at 3 on none of 28. Farm fcsel3m, nextpnr
9c732bc6303458df. fasm_equiv: EQUIVALENT on 25, the benign constant-LUT -> F7 / CARRY4-DI kind on 3 (12, 14, 19).
- From cells/, on claude/research at or after this commit:

    cp ../build/frontend/collatz/comp/handshake_transformed.mlir /tmp/collatz_hs_orig.mlir
    cp ../research/data/fifteen/collatz_preeq2.mlir ../build/frontend/collatz/comp/handshake_transformed.mlir
    BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 NEXTPNR_SEED=20 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/collatz_sizes_T3cdb_nl6s3m_bench.vh ./hw/build_bench.sh collatz
    cp /tmp/collatz_hs_orig.mlir ../build/frontend/collatz/comp/handshake_transformed.mlir
    grep -c "usinkeq2" build/gen/collatz_kernel_bench.v    # must be 1: the rewrite is in
    md5sum build/hw/collatz_bench_gen/collatz_bench_gen.sdf    # d86bdde5 = the route gated here
    python3 ../research/tools/ffmux_scan.py build/hw/collatz_bench_gen/collatz_bench_gen.fasm; echo "exit $?"   # must be 0
    CLK=0x00100C00 hw/loop_cost.sh collatz && cp build/hw/loop_cost_collatz.tsv build/hw/lc_col_sel3.tsv
    (item 25: #26's commands for lc_col_eq.tsv, if not already run)
    python3 ../research/tools/loop_cost_judge.py collatz build/hw/lc_col_sel3.tsv build/hw/lc_col_eq.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0. Ratio predicted ~1.39 over item 25 (35.92 ns on its route vs 25.81 here). A FAIL with
item 25 passing is a select race on silicon that the checks missed: send both logs.

## 30. ipow h4 + select links at 3 + mux delays by rule M (fisel3m) -- 27 routes, gate 81/81, every static row clean
research/JOURNAL.md 2026-11-16. nextpnr 9c732bc6303458df. From cells/, on claude/research at or after this commit:

    BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 NEXTPNR_SEED=19 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/ipow_dsp1_sizes_T9s75_h4s3m_bench.vh ./hw/build_bench.sh ipow
    md5sum build/hw/ipow_bench_gen/ipow_bench_gen.sdf    # b521630f = the route gated here
    python3 ../research/tools/ffmux_scan.py build/hw/ipow_bench_gen/ipow_bench_gen.fasm; echo "exit $?"   # must be 0
    CLK=0x00100C00 hw/loop_cost.sh ipow && cp build/hw/loop_cost_ipow.tsv build/hw/lc_ipow_sel3m.tsv
    (item 19: #20's commands for lc_ipow_r.tsv, if not already run)
    python3 ../research/tools/loop_cost_judge.py ipow build/hw/lc_ipow_sel3m.tsv build/hw/lc_ipow_r.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0. Ratio predicted ~1.12 over item 19 (39.78 ns on its route vs 35.54 here). A FAIL with
item 19 passing is a select or mux race the checks missed: send both logs.

## 31. collatz64 h4 + select links at 3 / 6 / 3 (fc64sel3) -- 29 routes, gate 87/87, rule E clean on every route
research/JOURNAL.md 2026-11-16. nextpnr 9c732bc6303458df. From cells/:

    cp ../build/frontend/collatz64/comp/handshake_transformed.mlir /tmp/c64_hs_orig.mlir
    cp ../research/data/fifteen/collatz64_preeq2.mlir ../build/frontend/collatz64/comp/handshake_transformed.mlir
    BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 NEXTPNR_SEED=10 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/collatz64_sizes_T4cdb_h4s3_bench.vh ./hw/build_bench.sh collatz64
    cp /tmp/c64_hs_orig.mlir ../build/frontend/collatz64/comp/handshake_transformed.mlir
    grep -c "usinkeq2" build/gen/collatz64_kernel_bench.v    # must be 1: the rewrite is in
    md5sum build/hw/collatz64_bench_gen/collatz64_bench_gen.sdf    # 637ff02e = the route gated here
    python3 ../research/tools/ffmux_scan.py build/hw/collatz64_bench_gen/collatz64_bench_gen.fasm; echo "exit $?"   # must be 0
    CLK=0x00100C00 hw/loop_cost.sh collatz64 && cp build/hw/loop_cost_collatz64.tsv build/hw/lc_c64_sel3.tsv
    (item 26: #27's commands for lc_c64_eq.tsv, if not already run)
    python3 ../research/tools/loop_cost_judge.py collatz64 build/hw/lc_c64_sel3.tsv build/hw/lc_c64_eq.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0. Ratio predicted ~1.04 over item 26 (36.27 ns on its route vs 34.94 here).

## 32. collatz item 28 + uselect0 7 / uaddi0 9 (fcsel3a) -- 31 routes, gate 93/93, every static row clean on every route
research/JOURNAL.md 2026-11-16. nextpnr 9c732bc6303458df. From cells/, on claude/research at or after this commit:

    cp ../build/frontend/collatz/comp/handshake_transformed.mlir /tmp/collatz_hs_orig.mlir
    cp ../research/data/fifteen/collatz_preeq2.mlir ../build/frontend/collatz/comp/handshake_transformed.mlir
    BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 NEXTPNR_SEED=20 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/collatz_sizes_T3cdb_nl6s3a_bench.vh ./hw/build_bench.sh collatz
    cp /tmp/collatz_hs_orig.mlir ../build/frontend/collatz/comp/handshake_transformed.mlir
    grep -c "usinkeq2" build/gen/collatz_kernel_bench.v    # must be 1: the rewrite is in
    md5sum build/hw/collatz_bench_gen/collatz_bench_gen.sdf    # 7aefc4bd = the route gated here
    python3 ../research/tools/ffmux_scan.py build/hw/collatz_bench_gen/collatz_bench_gen.fasm; echo "exit $?"   # must be 0
    CLK=0x00100C00 hw/loop_cost.sh collatz && cp build/hw/loop_cost_collatz.tsv build/hw/lc_col_sel3a.tsv
    (item 28: #29's commands for lc_col_sel3.tsv, if not already run)
    python3 ../research/tools/loop_cost_judge.py collatz build/hw/lc_col_sel3a.tsv build/hw/lc_col_sel3.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0. Ratio predicted ~1.21 over item 28 (25.81 ns vs 21.27 on seed 20). A FAIL with item 28
passing is a uselect0 bundling race the checks missed (its line is the only large change): send both logs.

## 33. collatz64 item 30 + proposal round (fc64sel3p, sizes h4s3p) -- 30 routes, gate 90/90
research/JOURNAL.md 2026-11-16. nextpnr 9c732bc6303458df. From cells/:

    cp ../build/frontend/collatz64/comp/handshake_transformed.mlir /tmp/c64_hs_orig.mlir
    cp ../research/data/fifteen/collatz64_preeq2.mlir ../build/frontend/collatz64/comp/handshake_transformed.mlir
    BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 NEXTPNR_SEED=22 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/collatz64_sizes_T4cdb_h4s3p_bench.vh ./hw/build_bench.sh collatz64
    cp /tmp/c64_hs_orig.mlir ../build/frontend/collatz64/comp/handshake_transformed.mlir
    grep -c "usinkeq2" build/gen/collatz64_kernel_bench.v    # must be 1: the rewrite is in
    md5sum build/hw/collatz64_bench_gen/collatz64_bench_gen.sdf    # 842dd4d7 = the route gated here
    python3 ../research/tools/ffmux_scan.py build/hw/collatz64_bench_gen/collatz64_bench_gen.fasm; echo "exit $?"   # must be 0
    CLK=0x00100C00 hw/loop_cost.sh collatz64 && cp build/hw/loop_cost_collatz64.tsv build/hw/lc_c64_sel3p.tsv
    (item 30: #31's commands for lc_c64_sel3.tsv, if not already run)
    python3 ../research/tools/loop_cost_judge.py collatz64 build/hw/lc_c64_sel3p.tsv build/hw/lc_c64_sel3.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0. Ratio predicted ~1.11 over item 30 (34.94 ns vs 31.32 on seed 22's route).

## 34. xorshift item 27 + seed 2's datapath proposal (fxa, sizes fr4a) -- 31 routes, gate 93/93
research/JOURNAL.md 2026-11-16. nextpnr 9c732bc6303458df. From cells/:

    cp ../build/frontend/xorshift/comp/handshake_transformed.mlir /tmp/xor_hs_orig.mlir
    cp ../research/data/fifteen/xorshift_predec.mlir ../build/frontend/xorshift/comp/handshake_transformed.mlir
    BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 NEXTPNR_SEED=27 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/xorshift_sizes_T3s50_fr4a_bench.vh ./hw/build_bench.sh xorshift
    cp /tmp/xor_hs_orig.mlir ../build/frontend/xorshift/comp/handshake_transformed.mlir
    grep -c "uforkdec0 (" build/gen/xorshift_kernel_bench.v    # must be 1: the rewrite is in
    md5sum build/hw/xorshift_bench_gen/xorshift_bench_gen.sdf    # 7f0c0592 = the route gated here
    python3 ../research/tools/ffmux_scan.py build/hw/xorshift_bench_gen/xorshift_bench_gen.fasm; echo "exit $?"   # must be 0
    CLK=0x00100C00 hw/loop_cost.sh xorshift && cp build/hw/loop_cost_xorshift.tsv build/hw/lc_xor_a.tsv
    (item 27: #28's commands for lc_xor_dec.tsv, if not already run)
    python3 ../research/tools/loop_cost_judge.py xorshift build/hw/lc_xor_a.tsv build/hw/lc_xor_dec.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0. Ratio predicted ~1.03 over item 27 (19.32 ns on its route vs 18.71 here). A FAIL with
item 27 passing points at the shortened datapath lines or at rule M's umux0 / umux1 (send both logs).

## 35. xorshift item 33's sizes x0.55 except the incrementer (fr4a_x55a), chosen by the delay-model draws -- 16.85 ns, 128 / 128 draws on 32 routes
research/JOURNAL.md 2026-11-16 / 17 (PROGRAM "The board decides"). nextpnr 9c732bc6303458df. Board route seed 21 (P 16.84 ns =
the median of 32 routes, 15.93-18.19; item 33 is 18.91). Its route: 32 / 32 draws (farm draws2) and the gate at SLOW_MAX,
FAST_MIN and worst on xor17 and xor19, 6 / 6 PASS with every run of every batch right. The draws first fail at x0.40a (4 of
16 routes); x0.50a ties with this at 16.74 and the longer was taken. Model error on the August builds: the simulation runs
~8% slow per iteration (SIM-VS-BOARD.md), so the board should show ~15.5 ns. From cells/:

    cp ../build/frontend/xorshift/comp/handshake_transformed.mlir /tmp/xor_hs_orig.mlir
    cp ../research/data/fifteen/xorshift_predec.mlir ../build/frontend/xorshift/comp/handshake_transformed.mlir
    BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 NEXTPNR_SEED=21 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=../research/data/xorshift_sizes_T3s50_fr4a_x55a_bench.vh ./hw/build_bench.sh xorshift
    cp /tmp/xor_hs_orig.mlir ../build/frontend/xorshift/comp/handshake_transformed.mlir
    md5sum build/hw/xorshift_bench_gen/xorshift_bench_gen.sdf    # 9145cd49 = the route judged here (the .bit md5 varies by build time)
    python3 ../research/tools/ffmux_scan.py build/hw/xorshift_bench_gen/xorshift_bench_gen.fasm; echo "exit $?"   # must be 0
    CLK=0x00100C00 hw/loop_cost.sh xorshift && cp build/hw/loop_cost_xorshift.tsv build/hw/lc_xor_x55a.tsv
    (item 33: #34's commands for lc_xor_a.tsv, if not already run)
    python3 ../research/tools/loop_cost_judge.py xorshift build/hw/lc_xor_x55a.tsv build/hw/lc_xor_a.tsv; echo "exit $?"

Pass: `=== PASS ... ===`, exit 0 (every point's derived oracle). Predicted ratio over item 33 ~1.11 (18.71 -> 16.84 on
their board routes). A FAIL here with item 33 passing means the draws' delay model is too generous on this die: that is
the most useful result this item can give, so send both logs.

## Owner-side check, not a board experiment (cheap, still useful)
ANSWERED in the cloud on 2026-10-25: the failure was the netlist, not the patch or the chipdb.
yosys 0.62 maps soak_top's two 8-input functions to MUXF7/MUXF8, and rloc_stamp gave their LUTs
slots no placement can honour (fixed in 77b20a8). The check below still tells whether the local
yosys makes MUXF7/F8 here (`grep -c MUXF build/pnr/synth.log`); if it does not, the two
toolchains produce different netlists from the same source, which is worth knowing.
On the owner's machine, with the local toolchain rebuilt from this branch's
patches/ (the local one has only main's patches, see the first journal entry):

    cd cells && BD_NO_TIGHTEN=1 ./flow.sh; echo "exit $?"

Pass: `flow.sh PASS`, exit 0. If it passes there and fails in the cloud
(`Unable to find legal placement ... rdly_chain`), the difference is the chipdb
or the build, not the patch. If it fails there too, the committed
nextpnr-xilinx-rloc-group.patch is not the one PR #1's routed numbers came from.

## Owner-side data request (no board needed): the August n=128 ring raw data -- DONE (owner, db3c299b; result 2026-11-03)
**Delivered and used.** `research/board/ro_many_aug/` (bit, fasm, routed JSON, SDF, toolchain, measured.tsv). Result in
`research/data/fid/ring128/README.md`: on the measured route, all 128 periods lie between the full stack's FAST_MIN and
SLOW_MAX; the band model at 0.38 misses by +11.5% (MISMATCH), and one global x = 0.288 predicts every ring within 3%
(held-out splits all pass). The request text below is kept for the record.

The board-fidelity GLS (PROGRAM.md, "THE priority") has to be validated ring by ring. The repo has the ring
summary (76/128 slower than the SDF, offset ~+988 ps) but not the per-ring board periods, nor the August
`ro_many_top` routed.json/SDF/bit they were measured on (that route predates the lut-perm-sink patch and cannot be
rebuilt). If they still exist on the owner's machine, commit them under `research/board/ro_many_aug/`:
the raw `g*.log` (or whatever ro_many_measure.py read), `ro_many_top_routed.json`, `ro_many_top.sdf`, the `.bit`,
and its toolchain.txt. Self-check: `python3 cells/gls/fid/ring_predict.py --help` names the inputs it needs;
`md5sum` of the .bit should match any md5 recorded in the JOURNAL for that build.
Simplest form (no board needed, reads the cached raw logs in `build/hw/ro_many_top/raw`):

    cd cells && RO_OFFLINE=1 RO_MEAS_TSV=measured.tsv python3 hw/ro_many_measure.py; echo "exit $?"

Pass: exit 0 and `measured.tsv` has 128 rows (`g b links measured_ps spread predicted_ps`). Commit it with the
routed.json + SDF of that build; the cloud side runs `cells/gls/fid/acceptance.py --ro-many-data ...` on it.
