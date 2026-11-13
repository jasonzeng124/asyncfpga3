# Board queue

Experiments that have passed every check possible without the board, most
valuable first. Each one: branch/commit, exact commands, pass criterion
(self-reporting, never "read the scope"), and what a failure would mean.

**Before programming any build here: check its sdf md5 against the one the item names.** Two nextpnr defects (JOURNAL
2026-11-08) leave a constant site pin unrouted so the die reads its default instead: a 5FF D (collatz64 bench seed 4)
and an F7 select (ipow bench seed 7, wrong answers). Both are a deterministic function of the route, and every route
named here decodes EQUIVALENT (or only the benign GND-buffer kinds). If the md5 differs, the route was not gated: run
the full stack's equivalence on it before using the board (cells/gls/ps/build_ps.sh HWDIR WORK "" bit prints the
fasm_equiv VERDICT; refuse "not configured by the bits" and any "MUX/S0 json ('const', 0) bits ('const', 1)").

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
18. **xorshift at ~18.7 ns per iteration: item 17 + the rule-1 link between the loop increment and the compare dropped
   (BDC_NO_LINK=ulink_n30__1), the 15 ns lead's lever 5, on the kernel bench**: #19 below. Full gate 24/24 on 8 bench
   routes. Predicted 2.12x per round over item 4 on this route (1.92-2.25 over 8), ~1.08x over item 17. Judge: `python3
   ../research/tools/loop_cost_judge.py xorshift build/hw/lc_xor_l5.tsv build/hw/lc_xor_s50.tsv`.
19. **ipow item 13 + a latch on the merge fork's result branch (BDC_MERGE_RES_LINK=ucontrol_merge0), the 15 ns lead's
   lever 1 carried to ipow by the event-graph search, on the kernel bench**: #20 below. Full gate 24/24 on 8 bench routes.
   Predicted 1.18x per iteration over item 13 on this route (1.13-1.21 over 8). Judge: `python3 ../research/tools/
   loop_cost_judge.py ipow build/hw/lc_ipow_r.tsv build/hw/lc_ipow_fm.tsv`.

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
