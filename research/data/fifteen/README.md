**THE AUTOMATIC COLUMN, flow v9 + the trim step (farm suite13t, all its tasks; regenerated 2026-11-21 01:00 UTC with
Dynamatic's own circuits ROUTED, research/data/suite/dynamatic/routed/README.md).** One switch, BDC_AUTO=1, no list of
kernels: the flow's own sizing loop with its search phase, then the trim step (research/tools/auto/auto_size.sh
AUTO_TRIM=1, CA_BENCHCAP=1), placer seeds 1-4 per kernel, every route judged by 4 draws of the delay model with the runt
monitor (research/tools/suite/suite_one.sh); nextpnr 6e5d224472232d5d. **42 of 62 kernels pass** (a judged rule-CLEAN
route; every draw on every judged route returned every right answer; no clean route counted whose draws had a pulse
under 1 ns). **7 UNFINISHED** (draws pass only on routes the loop left NOT CLEAN: cmpchain, factorial, fir,
iterative_division, nested, quadrec, spmv). **13 NO RESULT**: 11 kernels whose every task stopped at the farm's 240-min
limit (digitdiv, digitsum, divmods, gcd, iir, image_resize, isprime, loop_path, nest3, share_test_1, single_loop; how
far each loop got is in its row) and sobel / video_filter (not run).

**On the board next (research/BOARD-QUEUE.md, 2026-11-21):** item 42 (collatz, flow v10 + formal's proved eq2 rewrite,
14.48 ns), item 43 (xorshift, + the proved plain move, 16.35 ns), and item 44 -- flow v10's whole suite, 46 kernels,
one route each, run with the simulation gate's own vectors and judged by its own rules in one self-judging loop
(research/tools/suite/board_suite.sh). Every route rebuilds byte for byte from a committed spec.

**The distance to Dynamatic: its side now routed, the two sides measured differently** (wording corrected 2026-11-21
after audit T173; the numbers are the ones it reproduced). Dynamatic's own circuit for the same fixture (on-merges
buffers, its own dynamatic-opt) was exported by OUR exporter (research/tools/suite/dyn_export.py: the owner's build has
no export-rtl) and checked against OUR model of it, not Dynamatic's simulator (research/tools/suite/dynamatic_est.py:
on every call simulated, results = the C and cycles = the model's; 8 kernels have one call), then routed on our part
on 4 seeds, for 60 of the 62 kernels (divmods: Dynamatic's remsi.v is wrong on negative operands; test_stdint: no
check, so its row keeps an ESTIMATE and is out of the means). Dynamatic's period is nextpnr's achieved Fmax (--freq 250
--timing-allow-fail --ignore-loops) of the kernel in an I/O wrapper with no BRAM, mean of the 4 seeds (every log:
research/data/suite/dynamatic/routed/pnr_logs.tar.xz); its ns per iteration = that period x the model's simulated
cycles per iteration. Ours is a different kind of number: the event-graph period of our routed circuit simulated at
the delay band (each route judged by draws), and that simulation runs ~8 % slow per iteration against the August board
(research/SIM-VS-BOARD.md). Neither side's figure here has been run on silicon. The figures this replaces (3 single
routes from 2026-08 and 29 estimates) had flattered Dynamatic by 15 % on the geometric mean (routed / estimated 1.15
over 50 kernels, up to 2.25x on spmv). Over the 28 passing kernels with a P and a routed Dynamatic figure (stencil_2d not comparable,
test_stdint an estimate):
- **ours / Dynamatic's on-merges circuit: geometric mean 0.93.** Slower where its circuit runs one cycle per iteration
  (xorshift 1.53, collatz 1.61, collatz64 1.62, countloop 1.65, sqrtsub 1.70, varshift 2.40, fill 2.43), faster where
  its buffering waits 4-10 cycles per iteration (ipow 0.44, horner 0.35, iterative_sqrt 0.33, sumi3_mem 0.28, memsum
  0.36, dot2 0.46).
- **ours / Dynamatic at its loop-recurrence bound: geometric mean 2.00.** The bound is COMPUTED, not built: the fewest
  cycles per iteration any buffer placement could give (dynamatic_est.py's recurrence analysis, rings through the
  loop-header merges only) x the on-merges circuit's routed period. No Dynamatic circuit here reaches it (its buffer
  solver needs Gurobi, which the build lacks), and a placement that did need not keep that period. Five memory /
  multi-cycle kernels dominate it (share_test_2 11.1, mul_example 8.5, vector_rescale 6.4, gather 4.8, binary_search
  3.6); without them 1.55 (n = 23); on the 9 kernels whose on-merges circuit already runs one cycle per iteration
  (bound = measurement there) 1.68.
So 0.93 is the distance to the circuit Dynamatic's build here produces (measured differently on the two sides), and
2.00 the distance to a Dynamatic that reached its recurrence bound at the same period, an optimistic figure for it.
One clean route's draw had pulses under 150 ps with right answers (xorshift s1, the latch-fed steer race formal B28
found; refused as evidence, xorshift passes on its other clean routes).
Command: `research/tools/suite/suite_table.py --kernels research/tools/suite/kernels.txt --reasons
research/data/suite/headline_reasons_s13t.tsv --no-ratio isprime,stencil_2d` over results/suite13t_s1a..s4b and
suite13t_s5_rerun1's tasks 3-8 (its tasks 1-2 are exit1's) at origin/claude/cluster 656f1380f (2026-11-21 00:07 UTC); Dynamatic's
figures from research/tools/suite/dynamatic_ref.tsv (d65543df9). Table regenerated 2026-11-21 03:52 UTC from the
same result files with suite_table.py's corrected wording (T173: the latency footer and last line said ESTIMATED /
single routes; test_stdint's ratio is now marked as an estimate); one bracketed NOT CLEAN figure moved on
regeneration (nested's fit 24.34 -> 24.60 ns; cause not found, not a passing figure).

**Next table: flow v10** (suite13t_s5a_v10_*): v9 + the trim limited to the critical cycle + the latch-fed race check
(AUTO_RACE_Z=4.5) + formal's Lean-proved loop-test rewrites (8 kernels); its tasks resume past 240 min from $SHARED
(resume parts 1a_r1, 1b_r1, 2a_r1 filed so far), sobel / video_filter get rows (suite13t_s5a_v10_5sv). Seed-1 pairs
(research/JOURNAL.md 18:24): unchanged routes identical, collatz 22.75 -> 14.48 ns, xorshift 17.59 -> 16.35, countloop
22.22 -> 19.12, twoloops NOT CLEAN -> clean 14.71. **Flow v11 in preparation:** symmetric delay lines made trimmable
(cells/rtl BD_SYMTRIM, opt-in) with overbuild and trim-back: the first finish route of 5 of 5 loops tried was rule-CLEAN
as built, three of them on kernels v10 never got clean (research/JOURNAL.md 2026-11-21 00:45).

| kernel | status | routes judged (rule-clean + NOT CLEAN) / built | draws passing (clean; not clean) | ns per iteration (P) on clean routes, median (range) [on NOT CLEAN routes] | worst latency per call, ns | kernel LUTs | Dynamatic, ns per iteration | ratio | hand recipe's best, ns | latency per call, ns: ours, mean over the calls, median (range) over routes | Dynamatic, latency per call, ns | latency ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| binary_search | PASS | 1 + 0 / 1 | 4 / 4; - | 36.67 (36.67-36.67) | 3756 | 1679 | 30.80 (measured, 4 routes) | 1.19 | - | 2988.00 (2988.00-2988.00) | - | - |
| branchloop | PASS | 2 + 2 / 4 | 8 / 8; 8 / 8 | fit 28.54 (28.47-28.61) (slope of call latency on trip count; no event-graph P) [30.05 (30.05-30.05)] | 1944 | 2234 | 28.70 (measured, 4 routes) | 0.99 (fit) | - | 448.71 (447.86-449.57) [457.71 (449.57-465.86)] | 379.37 (cycles simulated, period measured (4 routes)) | 1.18 |
| brhash | PASS | 2 + 2 / 4 | 8 / 8; 8 / 8 | fit 29.54 (27.13-31.96) (slope of call latency on trip count; no event-graph P) [fit 29.14 (27.76-30.53)] | 8028 | 2089 | 34.22 (measured, 4 routes) | 0.86 (fit) | - | 1214.70 (1120.80-1308.60) [1198.50 (1145.40-1251.60)] | 1357.25 (cycles simulated, period measured (4 routes)) | 0.89 |
| cmpchain | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 4 / 4 | -; 16 / 16 | - | 108 | 3092 | - | - | - | 96.71 (94.59-96.71) | 60.79 (cycles simulated, period measured (4 routes)) | 1.59 |
| collatz | PASS | 4 + 0 / 4 | 16 / 16; - | 22.23 (20.25-22.75) | 6000 | 1267 | 13.79 (measured, 4 routes) | 1.61 | 21.50 | 2173.41 (1983.53-2258.12) | 1336.75 (cycles simulated, period measured (4 routes)) | 1.63 |
| collatz64 | PASS | 4 + 0 / 4 | 16 / 16; - | 27.41 (25.56-28.30) | 9960 | 1862 | 16.90 (measured, 4 routes) | 1.62 | 31.40 | 6467.50 (5897.33-6728.00) | 3915.33 (cycles simulated, period measured (4 routes)) | 1.65 |
| countloop | PASS | 4 + 0 / 4 | 16 / 16; - | 19.41 (18.84-22.22) | 5748 | 1807 | 11.73 (measured, 4 routes) | 1.65 | - | 834.30 (816.00-912.00) | 478.79 (cycles simulated, period measured (4 routes)) | 1.74 |
| digitdiv | NO RESULT (suite13t: no result line yet -- 4 task(s) stopped at the farm's 240-min limit (s1: loop at it 1; s2: loop at it 3; s3: loop at it 1; s4: loop at it 4)) | 0 / 0 | - | - | - | - | 476.35 (measured, 4 routes) | - | - | - | - | - |
| digitsum | NO RESULT (suite13t: no result line yet -- 4 task(s) stopped at the farm's 240-min limit (s1: loop at it 6; s2: loop at it 3; s3: loop at it 3; s4: loop at it 3)) | 0 / 0 | - | - | - | - | 476.35 (measured, 4 routes) | - | - | - | - | - |
| divmods | NO RESULT (suite13t: no result line yet -- 4 task(s) stopped at the farm's 240-min limit (s1: loop at it 0; s2: loop shipped it 4; s3: loop at it 2; s4: loop at it 4)) | 0 / 0 | - | - | - | - | - | - | - | - | - | - |
| divmodu | PASS | 4 + 0 / 4 | 16 / 16; - | 1614.00 (1614.00-1614.00) | 372 | 2755 | - | - | - | 255.00 (246.00-390.00) | - | - |
| dot2 | PASS | 4 + 0 / 4 | 16 / 16; - | 29.61 (27.43-32.63) | 1104 | 1475 | 64.03 (measured, 4 routes) | 0.46 | - | 670.88 (622.50-735.75) | 1309.45 (cycles simulated, period measured (4 routes)) | 0.51 |
| factorial | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 4 / 4 | -; 16 / 16 | - [fit 25.35 (25.15-25.48)] | 192 | 2567 | 182.64 (measured, 4 routes) | - | - | 124.00 (123.00-125.50) | 328.98 (cycles simulated, period measured (4 routes)) | 0.38 |
| fill | PASS | 4 + 0 / 4 | 16 / 16; - | 30.16 (29.73-32.78) | 1368 | 1942 | 12.40 (measured, 4 routes) | 2.43 | - | 549.00 (546.00-609.60) | 235.51 (cycles simulated, period measured (4 routes)) | 2.33 |
| fir | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 1 / 1 | -; 4 / 4 | - [25.83 (25.83-25.83)] | 25884 | 821 | 51.66 (measured, 4 routes) | - | - | 26670.00 (26670.00-26670.00) | 51717.73 (cycles simulated, period measured (4 routes)) | 0.52 |
| fold64 | PASS | 1 + 1 / 2 | 4 / 4; 4 / 4 | 21.35 (21.35-21.35) [23.26 (23.26-23.26)] | 6000 | 2818 | 16.72 (measured, 4 routes) | 1.28 | - | 824.40 (824.40-824.40) [927.00 (927.00-927.00)] | 628.83 (cycles simulated, period measured (4 routes)) | 1.31 |
| gather | PASS | 2 + 1 / 3 | 8 / 8; 4 / 4 | 55.30 (54.56-56.04) [56.42 (56.42-56.42)] | 1860 | 1491 | 80.12 (measured, 4 routes) | 0.69 | - | 1280.33 (1260.67-1300.00) [1304.00 (1304.00-1304.00)] | 1748.90 (cycles simulated, period measured (4 routes)) | 0.73 |
| gcd | NO RESULT (suite13t: no result line yet -- 4 task(s) stopped at the farm's 240-min limit (s1: loop at it 4; s2: loop at it 7; s3: loop at it 4; s4: loop at it 4)) | 0 / 0 | - | - | - | - | 44.52 (measured, 4 routes) | - | - | - | - | - |
| horner | PASS | 4 + 0 / 4 | 16 / 16; - | 21.05 (20.57-24.22) | 6252 | 1717 | 60.24 (measured, 4 routes) | 0.35 | - | 877.64 (843.27-988.91) | 2307.84 (cycles simulated, period measured (4 routes)) | 0.38 |
| if_convert | PASS | 3 + 0 / 3 | 12 / 12; - | 54.74 (50.50-56.52) | 10956 | 804 | 80.54 (measured, 4 routes) | 0.68 | - | 7864.00 (7430.00-8358.00) | - | - |
| if_loop_1 | PASS | 2 + 2 / 4 | 8 / 8; 8 / 8 | 26.18 (26.13-26.23) [25.75 (22.93-28.56)] | 2916 | 1873 | 23.34 (measured, 4 routes) | 1.12 | - | 1555.88 (1536.75-1575.00) [1530.00 (1355.25-1704.75)] | 1343.67 (cycles simulated, period measured (4 routes)) | 1.16 |
| if_loop_2 | PASS | 4 + 0 / 4 | 16 / 16; - | 31.37 (27.56-34.18) | 3468 | 1554 | 22.45 (measured, 4 routes) | 1.40 | - | 2046.00 (1836.75-2255.25) | 1433.09 (cycles simulated, period measured (4 routes)) | 1.43 |
| iir | NO RESULT (suite13t: no result line yet -- 4 task(s) stopped at the farm's 240-min limit (s1: loop shipped it 10; s2: loop shipped it 8; s3: loop shipped it 9; s4: loop shipped it 10)) | 0 / 0 | - | - | - | - | 55.47 (measured, 4 routes) | - | - | - | - | - |
| image_resize | NO RESULT (suite13t: no result line yet -- 4 task(s) stopped at the farm's 240-min limit (s1: loop shipped it 7; s2: loop shipped it 6; s3: loop shipped it 10; s4: loop shipped it 10)) | 0 / 0 | - | - | - | - | 16.07 (measured, 4 routes) | - | - | - | - | - |
| ipow | PASS | 2 + 2 / 4 | 8 / 8; 8 / 8 | 20.18 (19.87-20.50) [18.85 (18.73-18.96)] | 696 | 1302 | 45.58 (measured, 4 routes) | 0.44 | 36.20 | 259.76 (252.71-266.82) [248.12 (243.53-252.71)] | 468.67 (cycles simulated, period measured (4 routes)) | 0.55 |
| isprime | NO RESULT (suite13t: no result line yet -- 4 task(s) stopped at the farm's 240-min limit (s1: loop shipped it 9; s2: loop shipped it 7; s3: loop shipped it 8; s4: loop shipped it 9)) | 0 / 0 | - | - | - | - | 11.74 (measured, 4 routes) | - | - | - | - | - |
| iterative_division | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 2 / 2 | -; 8 / 8 | - [20.35 (19.93-20.77)] | 5412 | 3810 | 15.83 (measured, 4 routes) | - | - | 1535.40 (1496.80-1574.00) | 1166.72 (cycles simulated, period measured (4 routes)) | 1.32 |
| iterative_sqrt | PASS | 3 + 0 / 3 | 12 / 12; - | 58.95 (57.81-60.09) | 1080 | 2329 | 178.63 (measured, 4 routes) | 0.33 | - | 462.00 (435.50-472.50) | 1221.95 (cycles simulated, period measured (4 routes)) | 0.38 |
| lfsrfind | PASS | 4 + 0 / 4 | 16 / 16; - | 21.10 (19.70-22.32) | 5772 | 909 | 15.28 (measured, 4 routes) | 1.38 | - | 1015.50 (964.20-1075.20) | 705.29 (cycles simulated, period measured (4 routes)) | 1.44 |
| loop_path | NO RESULT (suite13t: no result line yet -- 4 task(s) stopped at the farm's 240-min limit (s1: loop shipped it 9; s2: loop shipped it 7; s3: loop shipped it 7; s4: loop shipped it 7)) | 0 / 0 | - | - | - | - | 29.63 (measured, 4 routes) | - | - | - | - | - |
| memsum | PASS | 4 + 0 / 4 | 16 / 16; - | 25.13 (23.36-31.15) | 1056 | 1396 | 68.88 (measured, 4 routes) | 0.36 | - | 498.60 (480.00-608.40) | 1199.63 (cycles simulated, period measured (4 routes)) | 0.42 |
| mul_example | PASS | 4 + 0 / 4 | 16 / 16; - | 61.25 (56.03-66.10) | 6636 | 335 | 71.10 (measured, 4 routes) | 0.86 | - | 6339.00 (5658.00-6612.00) | - | - |
| nest3 | NO RESULT (suite13t: no result line yet -- 4 task(s) stopped at the farm's 240-min limit (s1: loop at it 6; s2: loop shipped it 10; s3: loop at it 8; s4: loop at it 4)) | 0 / 0 | - | - | - | - | 12.80 (measured, 4 routes) | - | - | - | - | - |
| nested | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 4 / 4 | -; 16 / 16 | - [fit 24.60 (23.28-31.20)] | 7872 | 3519 | 13.76 (measured, 4 routes) | - | - | 914.73 (876.00-1094.18) | 574.21 (cycles simulated, period measured (4 routes)) | 1.59 |
| nested_loop | PASS | 2 + 0 / 2 | 8 / 8; - | 49.25 (48.35-50.14) | 20208 | 1315 | 52.01 (measured, 4 routes) | 0.95 | - | 20211.00 (19626.00-20796.00) | - | - |
| quadrec | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 3 / 3 | -; 12 / 12 | - [35.52 (30.16-38.43)] | 9876 | 3270 | 11.58 (measured, 4 routes) | - | - | 1327.20 (1168.80-1443.00) | 449.47 (cycles simulated, period measured (4 routes)) | 2.95 |
| share_test_1 | NO RESULT (suite13t: no result line yet -- 4 task(s) stopped at the farm's 240-min limit (s1: loop shipped it 11; s2: loop shipped it 9; s3: loop shipped it 10; s4: loop shipped it 8)) | 0 / 0 | - | - | - | - | 62.58 (measured, 4 routes) | - | - | - | - | - |
| share_test_2 | PASS | 4 + 0 / 4 | 16 / 16; - | 96.96 (96.30-99.07) | 9936 | 2401 | 77.75 (measured, 4 routes) | 1.25 | - | 9912.00 (9588.00-10188.00) | - | - |
| simple_example_1 | PASS | 4 + 0 / 4 | 16 / 16; - | - | 72 | 86 | - | - | - | 72.00 (72.00-72.00) | - | - |
| single_loop | NO RESULT (suite13t: no result line yet -- 4 task(s) stopped at the farm's 240-min limit (s1: loop shipped it 11; s2: loop shipped it 10; s3: loop shipped it 8; s4: loop shipped it 8)) | 0 / 0 | - | - | - | - | 51.41 (measured, 4 routes) | - | - | - | - | - |
| sobel | NO RESULT (not run in suite13t: its loop and draws do not fit the farm's 240 min (suite10b-10d); flow v10 leaves it out too) | 0 / 0 | - | - | - | - | 67.97 (measured, 4 routes) | - | - | - | - | - |
| spmv | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 3 / 3 | -; 12 / 12 | - | 1512 | 3943 | 96.81 (measured, 4 routes) | - | - | 957.00 (853.50-975.00) | - | - |
| sqrtsub | PASS | 4 + 0 / 4 | 16 / 16; - | 20.59 (17.15-32.24) | 8292 | 1338 | 12.11 (measured, 4 routes) | 1.70 | - | 755.54 (632.77-1115.08) | 423.02 (cycles simulated, period measured (4 routes)) | 1.79 |
| stencil_2d | PASS | 1 + 0 / 1 | 4 / 4; - | 417.02 (417.02-417.02) | 11724 | 2352 | 37.83 (measured, 4 routes) | 11.02 (not comparable: out of the mean) | - | 11886.00 (11886.00-11886.00) | - | - |
| straight | PASS | 4 + 0 / 4 | 16 / 16; - | - | 72 | 1022 | - | - | - | 72.00 (72.00-72.00) | 14.66 (cycles simulated, period measured (4 routes)) | 4.91 |
| sumi3_mem | PASS | 2 + 0 / 2 | 8 / 8; - | 24.09 (22.61-25.56) | 25620 | 615 | 84.60 (measured, 4 routes) | 0.28 | - | 24603.00 (22734.00-26472.00) | 84696.94 (cycles simulated, period measured (4 routes)) | 0.29 |
| test_bitint | PASS | 4 + 0 / 4 | 16 / 16; - | - | 312 | 644 | 38.52 (measured, 4 routes) | - | - | 285.00 (240.00-312.00) | 438.65 (cycles simulated, period measured (4 routes)) | 0.65 |
| test_bool_array | PASS | 4 + 0 / 4 | 16 / 16; - | - | 96 | 108 | - | - | - | 84.00 (84.00-96.00) | - | - |
| test_divui | PASS | 4 + 0 / 4 | 16 / 16; - | - | 480 | 2294 | - | - | - | 195.00 (180.00-516.00) | - | - |
| test_flatten_array | PASS | 3 + 0 / 3 | 12 / 12; - | - | 33396 | 1585 | 14.61 (measured, 4 routes) | - | - | 31662.00 (28608.00-33402.00) | - | - |
| test_int16 | PASS | 4 + 0 / 4 | 16 / 16; - | - | 60 | 3 | - | - | - | 60.00 (60.00-60.00) | - | - |
| test_loop_free | PASS | 3 + 1 / 4 | 12 / 12; 4 / 4 | - | 72 | 994 | - | - | - | 72.00 (72.00-72.00) [72.00 (72.00-72.00)] | 20.43 (cycles simulated, period measured (4 routes)) | 3.52 |
| test_memory_1 | PASS | 4 + 0 / 4 | 16 / 16; - | - | 288 | 1001 | 20.56 (measured, 4 routes) | - | - | 172.00 (164.00-180.00) | - | - |
| test_memory_2 | PASS | 3 + 1 / 4 | 12 / 12; 4 / 4 | - | 312 | 1122 | 20.41 (measured, 4 routes) | - | - | 180.86 (172.29-180.86) [164.57 (164.57-164.57)] | - | - |
| test_stdint | PASS | 4 + 0 / 4 | 16 / 16; - | 49.58 (44.87-53.27) | 5364 | 400 | 80.67 (ESTIMATE) | 0.61 (Dynamatic ESTIMATED: out of the measured mean) | - | 5012.25 (4434.00-5382.00) | - | - |
| twoloops | PASS | 1 + 3 / 4 | 4 / 4; 12 / 12 | 14.91 (14.91-14.91) [16.58 (15.81-16.83)] | 4380 | 2261 | 11.81 (measured, 4 routes) | 1.26 | - | 1000.91 (1000.91-1000.91) [1042.36 (978.55-1049.45)] | 668.06 (cycles simulated, period measured (4 routes)) | 1.50 |
| unused_arg | PASS | 4 + 0 / 4 | 16 / 16; - | - | 72 | 88 | - | - | - | 72.00 (72.00-72.00) | 6.72 (cycles simulated, period measured (4 routes)) | 10.71 |
| varshift | PASS | 4 + 0 / 4 | 16 / 16; - | 29.89 (28.95-30.26) | 7800 | 2538 | 12.48 (measured, 4 routes) | 2.40 | - | 1261.80 (1241.40-1300.80) | 520.23 (cycles simulated, period measured (4 routes)) | 2.43 |
| vector_rescale | PASS | 3 + 0 / 3 | 12 / 12; - | 54.33 (51.37-57.75) | 57780 | 589 | 50.68 (measured, 4 routes) | 1.07 | - | 55602.00 (51450.00-58260.00) | - | - |
| video_filter | NO RESULT (not run in suite13t: its loop and draws do not fit the farm's 240 min (suite10b-10d); flow v10 leaves it out too) | 0 / 0 | - | - | - | - | 56.02 (measured, 4 routes) | - | - | - | - | - |
| while_loop_3 | PASS | 4 + 0 / 4 | 16 / 16; - | 25.30 (24.49-27.93) | 1008 | 800 | 50.60 (measured, 4 routes) | 0.50 | - | 293.57 (288.00-312.00) | - | - |
| xorshift | PASS | 2 + 1 / 4 | 8 / 8; 4 / 4 | 17.59 (16.67-17.63) [16.80 (16.80-16.80)] | 4572 | 1292 | 11.48 (measured, 4 routes) | 1.53 | 16.76 | 1750.42 (1674.95-1811.37) [1716.95 (1716.95-1716.95)] | 1133.63 (cycles simulated, period measured (4 routes)) | 1.54 |

Hand recipes (per-kernel knobs and sizes, the column the automatic path has to close): collatz: item 31 (fcsel3a): median of farm routes, board route 21.27, 32 / 32 draws; collatz64: item 32 (fc64sel3p): median of farm routes, 32 / 32 draws; ipow: item 29 (fisel3m): median of farm routes, 24 / 24 draws; xorshift: x55a10 (item 35 + UCMPI0 10): median of 28 EQUIVALENT farm routes (cand3b), 200 / 200 draws.

Dynamatic's figures: binary_search: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 7 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 10.18 ns mean (10.00-10.45), nextpnr 6e5d224472232d5d x 3.02 simulated cycles per iteration; branchloop: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 14 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 8.35 ns mean (7.64-9.20), nextpnr 6e5d224472232d5d x 3.44 simulated cycles per iteration; brhash: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 10 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 11.41 ns mean (10.95-12.20), nextpnr 6e5d224472232d5d x 3.00 simulated cycles per iteration; collatz: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 17 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 13.79 ns mean (13.43-14.22), nextpnr 6e5d224472232d5d x 1.00 simulated cycles per iteration; collatz64: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 18 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 16.90 ns mean (16.73-17.14), nextpnr 6e5d224472232d5d x 1.00 simulated cycles per iteration; countloop: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 10 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 11.73 ns mean (11.09-12.09), nextpnr 6e5d224472232d5d x 1.00 simulated cycles per iteration; dot2: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 8 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 10.71 ns mean (10.12-11.25), nextpnr 6e5d224472232d5d x 5.98 simulated cycles per iteration; factorial: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 12 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 14.05 ns mean (13.70-14.52), nextpnr 6e5d224472232d5d x 13.00 simulated cycles per iteration; fill: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 5 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 12.40 ns mean (12.00-12.63), nextpnr 6e5d224472232d5d x 1.00 simulated cycles per iteration; fir: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 2 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 8.62 ns mean (8.45-8.90), nextpnr 6e5d224472232d5d x 6.00 simulated cycles per iteration; fold64: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 10 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 16.72 ns mean (15.41-18.08), nextpnr 6e5d224472232d5d x 1.00 simulated cycles per iteration; gather: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 9 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 11.48 ns mean (10.76-12.09), nextpnr 6e5d224472232d5d x 6.98 simulated cycles per iteration; horner: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 11 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 12.05 ns mean (11.62-12.36), nextpnr 6e5d224472232d5d x 5.00 simulated cycles per iteration; if_convert: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 3 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 13.42 ns mean (12.93-14.14), nextpnr 6e5d224472232d5d x 6.00 simulated cycles per iteration; if_loop_1: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 8 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 11.71 ns mean (11.30-12.38), nextpnr 6e5d224472232d5d x 1.99 simulated cycles per iteration; if_loop_2: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 8 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 11.26 ns mean (10.59-11.87), nextpnr 6e5d224472232d5d x 1.99 simulated cycles per iteration; ipow: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 17 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 9.12 ns mean (8.63-9.40), nextpnr 6e5d224472232d5d x 5.00 simulated cycles per iteration; iterative_division: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 15 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 15.81 ns mean (15.47-16.25), nextpnr 6e5d224472232d5d x 1.00 simulated cycles per iteration; iterative_sqrt: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 12 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 17.90 ns mean (17.15-19.65), nextpnr 6e5d224472232d5d x 9.98 simulated cycles per iteration; lfsrfind: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 10 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,4,5, 7.62 ns mean (7.38-8.10), nextpnr 6e5d224472232d5d x 2.00 simulated cycles per iteration; memsum: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 5 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 11.51 ns mean (11.20-11.81), nextpnr 6e5d224472232d5d x 5.98 simulated cycles per iteration; mul_example: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 3 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 7.18 ns mean (6.84-7.36), nextpnr 6e5d224472232d5d x 9.91 simulated cycles per iteration; nested: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 11 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 13.76 ns mean (13.32-14.12), nextpnr 6e5d224472232d5d x 1.00 simulated cycles per iteration; nested_loop: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 1 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 8.67 ns mean (8.31-9.03), nextpnr 6e5d224472232d5d x 6.00 simulated cycles per iteration; quadrec: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 10 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 11.58 ns mean (11.24-11.95), nextpnr 6e5d224472232d5d x 1.00 simulated cycles per iteration; share_test_2: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 3 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 8.72 ns mean (8.10-9.52), nextpnr 6e5d224472232d5d x 8.92 simulated cycles per iteration; spmv: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 4 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 13.88 ns mean (13.58-14.29), nextpnr 6e5d224472232d5d x 6.97 simulated cycles per iteration; sqrtsub: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 13 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 12.11 ns mean (11.71-12.73), nextpnr 6e5d224472232d5d x 1.00 simulated cycles per iteration; stencil_2d: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 1 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 8.12 ns mean (8.01-8.25), nextpnr 6e5d224472232d5d x 4.66 simulated cycles per iteration; sumi3_mem: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 3 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 8.47 ns mean (7.73-9.40), nextpnr 6e5d224472232d5d x 9.99 simulated cycles per iteration; test_bitint: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 6 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 7.08 ns mean (6.88-7.24), nextpnr 6e5d224472232d5d x 5.44 simulated cycles per iteration; test_flatten_array: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 1 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 7.56 ns mean (7.23-7.70), nextpnr 6e5d224472232d5d x 1.93 simulated cycles per iteration; test_memory_1: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 6 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 11.56 ns mean (10.51-12.23), nextpnr 6e5d224472232d5d x 1.78 simulated cycles per iteration; test_memory_2: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 7 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 11.49 ns mean (10.85-12.19), nextpnr 6e5d224472232d5d x 1.78 simulated cycles per iteration; test_stdint: Dynamatic on-merges, simulated 9.91 cycles per iteration (answers = C; any placement >= 1) x period 8.14 ns ESTIMATED from Dynamatic's timing model (x0.793 fitted on 3 routed kernels, worst leave-one-out 16 %); research/tools/suite/dynamatic_est.py; twoloops: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 11 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,3,4,5, 11.81 ns mean (11.06-12.54), nextpnr 6e5d224472232d5d x 1.00 simulated cycles per iteration; varshift: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 10 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 12.48 ns mean (11.99-13.29), nextpnr 6e5d224472232d5d x 1.00 simulated cycles per iteration; vector_rescale: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 2 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 8.45 ns mean (8.20-9.09), nextpnr 6e5d224472232d5d x 6.00 simulated cycles per iteration; while_loop_3: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 7 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 10.12 ns mean (9.69-10.55), nextpnr 6e5d224472232d5d x 5.00 simulated cycles per iteration; xorshift: Dynamatic on-merges buffers: Dynamatic's own Verilog (dyn_export.py; checked on 19 calls: results = the C, cycles = dynamatic_est.py's model) routed on seeds 1,2,3,4, 11.48 ns mean (11.11-11.72), nextpnr 6e5d224472232d5d x 1.00 simulated cycles per iteration.

Latency per call: ours includes the bench's issue, synchroniser and capture and is quantised to its clock (12 ns; a kernel that is a constant, test_int16, takes 5 host cycles = 60 ns), Dynamatic's is the kernel alone: simulated cycles per call on the same calls (dynamatic_est.py's model) x the routed period where the cell says 'period measured' (research/data/suite/dynamatic/routed/), else x the ESTIMATED period (research/data/suite/dynamatic/README.md); a period extrapolated below half the calibrated range is marked and left out of the mean.

P refused (off its route's own slope of call latency on the most executed loop's trip counts by more than 15 %: the event graph's marker was on another loop; the slope is used): branchloop seed 1 P=14.28 ns against a slope of 28.47 ns (0.50x); branchloop seed 3 P=13.07 ns against a slope of 30.45 ns (0.43x); branchloop seed 4 P=13.71 ns against a slope of 28.61 ns (0.48x).

Routes whose draws had a pulse under 1 ns on a kernel handshake net (not counted as passing evidence, whatever their answers): xorshift seed 1 (clean, pulses <150/500/1000 ps 118/118/118 in its worst draw).

42 of 62 kernels attempted pass (a kernel passes when it has a judged rule-CLEAN route and every draw on every judged route, clean or not, returned every right answer; ns per iteration, latency and the ratios are over rule-CLEAN routes only, the NOT CLEAN routes' figures in brackets); 7 more pass every draw only on routes the sizing loop left NOT CLEAN (UNFINISHED: the rule names a short constraint on each, and such a route can pass 4 draws and fail the model a third of the time, formal C68), not counted; geometric mean of the ratio (ns per iteration / Dynamatic's) over passing kernels with a MEASURED Dynamatic figure (n = 28): 0.93; including ESTIMATED figures (n = 29; 2 with our figure from the latency fit): 0.92. Our ns are the simulation's (about 8 % slower per iteration than the August board on the same bitstreams, research/SIM-VS-BOARD.md); Dynamatic's measured figures are routed static timing (nextpnr's Fmax with --ignore-loops, an I/O wrapper without BRAM, mean of 4 placer seeds) x dynamatic_est.py's simulated cycles, not board runs: the two sides are measured differently. Latency per call (ours / Dynamatic's, same calls; Dynamatic's = simulated cycles x the routed period where measured, else x the ESTIMATED period; ours includes the bench): geometric mean over passing kernels (n = 25): 1.22.

## Previous headline: flows v6-v8 (2026-11-19 20:03 UTC, corrected 2026-11-20 09:12 UTC)

**CORRECTION 2026-11-20 09:12 UTC (formal C68): a kernel passes only on a rule-CLEAN route. 34 of 62 kernels pass, not
59.** 25 kernels were counted as passing on draws alone, though every route judged for them was one its sizing loop
left NOT CLEAN (the least-short route of the finish phase, shipped with the rule naming short constraints on it).
Formal's C68 shows why that is not a pass: exit1 spmv seed 1, such a route, passed our 4 draws and hangs in 11 of 32
draws of the same delay model, the race starting at the cell our rule had called short (4 draws miss a 1-in-3 failure
18 % of the time). Those 25 rows now say UNFINISHED; their P and latency stay in brackets. The ratio means do not move
(they were over clean routes already): 1.69 (measured, n = 3), 1.05 (with estimates, n = 22). The latency-ratio mean is
now over passing kernels' clean routes: 1.22 (n = 19; it was 1.38 over n = 31 with NOT CLEAN routes). stencil_2d gained
a clean route since the last copy and passes; its P (408 ns) is the outer loop's period against Dynamatic's innermost
cycle (4.66 cycles of bb3; bb1 is 54), so its ratio is out of the means, as isprime's. A clean route also counts as passing evidence only if no draw on it had a pulse under 1 ns on a kernel handshake net
(suite_table.py since 2026-11-20 09:44 UTC): over the 378 farm routes with runt-monitored draws, the 4 that ever had one were all
NOT CLEAN, among them C68's spmv route (its draw 10102 had 72 pulses under 150 ps and passed); no clean route had one,
so no row moves. The next table is suite13t (flow
v9: the rule fixes that removed most unfixable rows, plus the trim step; on the capture kernels capfix1 had 34 of 38
routes clean where suite12 had 0 of 8).

**THE AUTOMATIC COLUMN, every kernel the suite lists (2026-11-19 20:03 UTC; corrected for auditor T161 / T167 and the owner's
T156 / T161 rules).** One switch, BDC_AUTO=1, with no list of kernels (the md5-keyed MLIR rewrites are off since
f7573b807), the flow's own sizing loop (research/tools/auto/auto_size.sh), judged by draws of the delay model;
nextpnr 6e5d224472232d5d (suite3a / 3b and suite6's own predecessors partly 9c732bc6303458df: identical routes where no GND
pin was missed). Ns per iteration and the ratio use rule-CLEAN routes only; the NOT CLEAN routes' figures are in brackets.
**Every wrong answer the automatic flow has produced, superseded routes included (auditor T169; read 2026-11-19 21:32 UTC
from origin/claude/cluster results/): rule-CLEAN is not a certificate, two of the wrong routes were clean.** test_divui
seeds 1 and 2 (suite10b/9, /10, flow v7, **rule-CLEAN**, FAIL 0 / 4 draws each, 3 of 12 vectors wrong in every draw;
cause: rule A's peers escaped the cell; superseded by divsize1's routes after the fix 1daa7efd4); if_loop_1 seed 1
(suite9/77, v6, NOT CLEAN, FAIL 2 / 4 draws, memory wrong; superseded by ifl1 after rule B's RAM guard); ipow seed 4 in
flow v1 (NOT CLEAN); ipow seed 7 with ring fusion (ringfuse1/31, v8, NOT CLEAN at it 7, FAIL 7 / 8 draws, one draw 16 of
17 vectors, with runts; the least-short finish route came after it). None of these rows shows them now, because a later
request superseded each (kernel, seed). isprime's ratio (an outer-trial
period against Dynamatic's inner-shift cycle) is out of every mean. **branchloop's ratio is now 0.85 from the fit, not 0.40
(2026-11-19 21:52 UTC): its P measured the INNER loop, Dynamatic's 36.77 ns is the OUTER loop's slope; suite_table.py now
refuses a P more than 15 % off its route's own slope of call latency on the trip counts and uses that slope, Dynamatic's
own convention; see "What ns per iteration is" below.** Dynamatic's figures are ESTIMATES except xorshift /
collatz / collatz64 (single nextpnr routes, Fmax x cycles), and on the memory kernels the estimate assumes
Dynamatic's on-merges buffering, which its solver placement could beat by up to ~6x (research/data/suite/dynamatic/
DYNFIG_REPORT.md): those ratios flatter us, so read the mean with estimates as an upper bound on our standing; our ns are the simulation's (~8 % slower per iteration than
the August board, research/SIM-VS-BOARD.md). **How much (auditor T169, recomputed on this table):** 11 of the 22 ratios
are memory kernels (the fixture's handshake has a memref: dot2, fill, fir, if_convert, if_loop_1, if_loop_2, loop_path,
memsum, single_loop, sumi3_mem, while_loop_3); without them the mean with estimates is 1.24 (n = 11), against 1.05 (n = 22) with
them (branchloop at 0.85 from the fit since 21:52 UTC; with its old 0.40 they were 1.16 and 1.01). All 10 ratios below 1
are against ESTIMATED figures, none against a measured one, and 4 of the 10 are not memory kernels (branchloop, digitdiv,
horner, ipow), so the estimate itself, not only the memory buffering, is in question there.
**What "ns per iteration" is (checked 2026-11-19 21:35 UTC):** P is the event graph's period of the routed design
(auto_size.sh final()), not a time the bench measured. Over every PASS route on origin/claude/cluster (30 kernels with
>= 4 routes on the same vectors), P tracks the bench's latency per call (correlation >= +0.9 on 24; on iterative_sqrt,
binary_search, divmodu and fir P varies by under 6 %, too little for a correlation to say anything), except on two
kernels, one route each, both now explained (2026-11-19 21:50 UTC). **dot2 seed 2** (suite8 / suite9, NOT CLEAN: P 156.000
ns = 13 x 12 ns): the host's array fill through the memory port, picked as the marker; fixed in eventgraph.py on
2026-11-18 (430f52be7), after suite9's commit eaef0dec7, and suite_table.py already refuses a P that is a multiple of the
host clock, so it never entered the table. **branchloop seed 2 in finseeds1 arm DA** (rule-clean: P 35.12 ns against
14.2-14.8 on the other routes): the auto marker is the request net with the longest run of equal rise intervals, and
branchloop has two loops. From the bench's own per-call latencies (finseeds1 tasks 16 and 36, 12 ns host cycles, minus
the 0-trip call): on BOTH routes an inner trip is 14.1 / 14.5 ns (n = 0x7fffffff, 30 trips) and an outer iteration
35.8 / 36.4 ns (n = 0x40000001, 61 alternating odd / even iterations; 30.0 / 29.6 on n = 0x40000000, even only). So P
measured the inner loop on five routes and the outer loop on one; the routes do not differ. **Consequence: branchloop's
former figure (14.79 ns, P on the clean route) was its inner loop's trip, while Dynamatic's figure (3.44 cycles, bb1, "the most executed of
2 loops": 160 outer iterations against 68 inner trips over the 14 calls) is the outer loop's; the ratio 0.40 is withdrawn.**
Dynamatic's 3.44 cycles is itself a slope (its cycles per call on bb1's executions; 3.43 recomputed from
dynamatic_lat.tsv), so the like-for-like figure is our slope on the same trip counts: 31.35 ns on the clean route, ratio
**0.85 (fit)**, in the table now (latency-per-call ratio 1.01). Over every farm route, P against that slope is 0.94-1.04
on all 19 single-loop kernels with a varying trip count (research/data/suite/pslope/p_vs_slope.txt), so the rule changes
nothing there. Of the 22 kernels with a ratio, branchloop is the only one that
Dynamatic's table (research/data/suite/dynamatic/table.md, "of N loops") lists with more than one loop; on the other 17
it lists so (gcd, nested, nest3, twoloops, binary_search, the memory nests; isprime already out) the same question must
be answered before a ratio is filled.

**The flow moved on after these routes (2026-11-19 17:07 UTC):** BDC_AUTO=1 now fuses each loop's update with its test
(BDC_RING_FUSE=2, flow v8; farm ringfuse1: faster on 19 of 29 paired seeds, median -1.27 ns, xorshift 8 / 8 at -1.87),
and the sizing loop's finish phase has 6 routes and ships its least-short route. The table below is v6 / v7; farm
suite12 measures v8 on every kernel. ringfuse1's fused arm in full (auditor T169): 32 tasks, 30 routes judged, **215 /
216 draws right**; the one wrong draw is ipow seed 7 (NOT CLEAN, FAIL 7 / 8, listed above); countloop seeds 7 / 8 gave no
route (PNR-TIMEOUT at it 0).

**xorshift against the 15 ns yardstick** (owner, 2026-11-19: a yardstick, not a bar): the automatic column with no
kernel list (v7) runs 22.16 ns per iteration (median of 6 rule-clean routes); flow v8's ring fusion took 1.87 ns off
it on 8 of 8 paired seeds (farm ringfuse1, median of the fused routes 19.9 ns); the hand recipe (item 37) 16.76;
Dynamatic 12.73 (one nextpnr route).

**Provenance (auditor T167).** The exact command, inputs in this order, a later request superseding an earlier one for the
same (kernel, seed): `research/tools/suite/suite_table.py --kernels research/tools/suite/kernels.txt --reasons
research/data/suite/headline_reasons.tsv --no-ratio isprime,stencil_2d` (regenerated 2026-11-20 09:12 UTC with the C68 status rule, from the farm results at origin/claude/cluster c6a1972fc (pushed 09:02 UTC): tasks finished since the 20:03 copy added one NOT CLEAN route to binary_search and one clean route to stencil_2d; earlier: since 2026-11-19 21:52 UTC with suite_table.py's P-against-slope refusal;
regenerated locally from the farm results copied at 20:03 UTC: every row identical to the 20:03 table except branchloop,
now from the fit, and bracketed NOT CLEAN fits on factorial, gcd, isprime, nest3 and nested) over the farm's results/{suite3a, suite3b, suite8, suite7,
suite6 (tasks 25-32 only: ipow, the one suite6 kernel no rewrite touched), suite9, suite9r3, norw1, norw1r2, gifast1,
nsearch1, suite10b, muxn1, suite9r4, divsize1, divres1, suite10c, ifl1, ringfuse1 tasks 33-44 only (its v7 baselines; the
BDC_RING_FUSE arm is a variant, not the column), suite11 (e2c8e6c52: v7 with the mux rule and the cell-confined peers)}. The flow differs by request, by the defaults at each request's commit: suite3a e18df972b,
suite3b dfd498a94, suite8 c605cc2a6, suite9 eaef0dec7, norw1 0cebd725c: flow v6; suite7 45db9e386: v5; suite6 55988c8d5:
v6; norw1r2 8d8f48878 and gifast1 ff31a03c1: + CA_FAST (identical proposals) and the bench-clock seed fallback;
suite9r3 fe52cd741: + rule B's RAM guard; nsearch1 5c6ece20e: + the search phase (countloop's routes are v7); suite10b
3167ade0e: v7 (+ the runt monitor reporting); muxn1 ec9c4c2d8: v7 + the N-way mux select rule; suite9r4: suite9r3's loops finished with 2 draws; divsize1 /
divres1: + rule A's peers confined to the cell (1daa7efd4: test_divui's suite10b routes were undersized by the old rule). Resumes replaced four
earlier build failures, which the table no longer shows: quadrec s2 and varshift s2 / s4 (the bench missed 83 MHz on
one iteration; resumed with the seed fallback), isprime s3 (PNR-TIMEOUT at it 0 in suite7; gifast1's route). cmpchain s1 /
s4's farm verdict NOT EQUIVALENT was a checker false alarm on dead cells (fixed e060d7980; auditor T166 confirms s1);
those routes pass 4 / 4 draws each when rejudged. 8 of the 22 ratios rest on one rule-clean route (branchloop (fit),
digitdiv, dot2, fold64, horner, if_loop_1, single_loop, sqrtsub; counted on this table, auditor T169 counted 7 on the
56-of-62 one).

| kernel | status | routes judged (rule-clean + NOT CLEAN) / built | draws passing (clean; not clean) | ns per iteration (P) on clean routes, median (range) [on NOT CLEAN routes] | worst latency per call, ns | kernel LUTs | Dynamatic, ns per iteration | ratio | hand recipe's best, ns | latency per call, ns: ours, mean over the calls, median (range) over routes | Dynamatic, latency per call, ns | latency ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| binary_search | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 4 / 4 | -; 16 / 16 | - [37.80 (36.21-38.10)] | 4068 | 1657 | 24.18 (ESTIMATE) | - | - | 3072.43 (3011.14-3146.57) | - | - |
| branchloop | PASS | 1 + 3 / 4 | 4 / 4; 12 / 12 | fit 31.35 (31.35-31.35) (slope of call latency on trip count; no event-graph P) [fit 31.83 (30.01-34.44)] | 2160 | 2213 | 36.77 (ESTIMATE) | 0.85 (fit) | - | 490.71 (490.71-490.71) [489.00 (463.29-522.43)] | 486.08 (ESTIMATE) | 1.01 |
| brhash | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 4 / 4 | -; 16 / 16 | - [fit 32.08 (30.73-34.34)] | 8664 | 2110 | 36.40 (ESTIMATE) | - | - | 1314.30 (1261.20-1402.80) | 1443.81 (ESTIMATE) | 0.91 |
| cmpchain | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 4 / 4 | -; 16 / 16 | - | 120 | 3083 | - | - | - | 100.94 (96.71-100.94) | 33.90 (ESTIMATE) | 2.98 |
| collatz | PASS | 5 + 3 / 8 | 40 / 40; 24 / 24 | 22.54 (18.98-25.56) [22.86 (22.79-26.70)] | 7032 | 1289 | 14.05 (measured, 1 route) | 1.60 | 21.50 | 2254.24 (1845.18-2591.29) [2295.88 (2226.35-2625.18)] | 1362.02 (cycles simulated, period measured (1 route)) | 1.66 |
| collatz64 | PASS | 3 + 5 / 8 | 24 / 24; 40 / 40 | 30.93 (29.89-31.49) [30.46 (28.10-33.47)] | 11784 | 1916 | 17.84 (measured, 1 route) | 1.73 | 31.40 | 7259.33 (7231.00-7410.33) [7201.67 (6792.67-8181.33)] | 4131.94 (cycles simulated, period measured (1 route)) | 1.76 |
| countloop | PASS | 7 + 1 / 8 | 28 / 28; 4 / 4 | 21.37 (20.31-24.87) [23.50 (23.50-23.50)] | 6420 | 1797 | 8.36 (ESTIMATE) | 2.56 | - | 916.80 (865.80-1018.20) [988.20 (988.20-988.20)] | 341.14 (ESTIMATE) | 2.69 |
| digitdiv | PASS | 1 + 0 / 1 | 4 / 4; - | 147.74 (147.74-147.74) | 4788 | 3813 | 303.77 (ESTIMATE) | 0.49 | - | 1416.00 (1416.00-1416.00) | - | - |
| digitsum | PASS | 1 + 0 / 1 | 4 / 4; - | 146.42 (146.42-146.42) | 4752 | 3874 | - | - | - | 1447.33 (1447.33-1447.33) | - | - |
| divmods | PASS | 2 + 0 / 2 | 8 / 8; - | 1614.00 (1614.00-1614.00) | 420 | 5988 | - | - | - | 354.12 (270.25-438.00) | - | - |
| divmodu | PASS | 4 + 0 / 4 | 16 / 16; - | 1614.00 (1614.00-1614.00) | 276 | 2764 | - | - | - | 273.00 (258.00-282.00) | - | - |
| dot2 | PASS | 1 + 3 / 4 | 4 / 4; 12 / 12 | 30.97 (30.97-30.97) [33.84 (33.39-34.28)] | 1152 | 1436 | 59.28 (ESTIMATE) | 0.52 | - | 708.75 (708.75-708.75) [726.75 (640.50-761.25)] | 1212.19 (ESTIMATE) | 0.58 |
| factorial | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 4 / 4 | -; 16 / 16 | - [fit 28.21 (26.76-28.85)] | 204 | 2635 | 129.79 (ESTIMATE) | - | - | 139.00 (131.00-142.00) | 233.79 (ESTIMATE) | 0.59 |
| fill | PASS | 2 + 2 / 4 | 8 / 8; 8 / 8 | 32.86 (32.17-33.55) [29.88 (29.42-30.34)] | 1404 | 1942 | 10.95 (ESTIMATE) | 3.00 | - | 587.40 (574.80-600.00) [537.00 (528.00-546.00)] | 208.09 (ESTIMATE) | 2.82 |
| fir | PASS | 3 + 1 / 4 | 6 / 6; 2 / 2 | 26.04 (25.99-26.64) [26.98 (26.98-26.98)] | 27036 | 793 | 48.68 (ESTIMATE) | 0.53 | - | 26688.00 (25668.00-26964.00) [28032.00 (28032.00-28032.00)] | 48738.03 (ESTIMATE) | 0.55 |
| fold64 | PASS | 1 + 3 / 4 | 4 / 4; 12 / 12 | 24.10 (24.10-24.10) [23.96 (23.67-24.25)] | 6252 | 2794 | 11.93 (ESTIMATE) | 2.02 | - | 921.60 (921.60-921.60) [939.60 (901.80-943.20)] | 448.74 (ESTIMATE) | 2.05 |
| gather | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 4 / 4 | -; 16 / 16 | - [51.69 (48.15-55.22)] | 1824 | 1493 | 69.20 (ESTIMATE) | - | - | 1210.00 (1124.00-1244.67) | 1510.48 (ESTIMATE) | 0.80 |
| gcd | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 3 / 4 | -; 12 / 12 | - [fit 29.05 (28.36-31.16)] | 2172 | 7178 | 50.60 (ESTIMATE) | - | 87.20 | 600.00 (593.25-628.50) | 429.97 (ESTIMATE) | 1.40 |
| horner | PASS | 1 + 3 / 4 | 4 / 4; 12 / 12 | 28.03 (28.03-28.03) [30.22 (29.25-31.28)] | 8064 | 1735 | 41.81 (ESTIMATE) | 0.67 | - | 1147.09 (1147.09-1147.09) [1205.45 (1181.45-1233.27)] | 1601.58 (ESTIMATE) | 0.72 |
| if_convert | PASS | 4 + 0 / 4 | 16 / 16; - | 50.48 (49.09-51.86) | 10056 | 807 | 65.70 (ESTIMATE) | 0.77 | - | 7281.00 (6960.00-7592.00) | - | - |
| if_loop_1 | PASS | 1 + 3 / 4 | 4 / 4; 12 / 12 | 27.97 (27.97-27.97) [33.51 (28.61-33.70)] | 3432 | 1888 | 19.90 (ESTIMATE) | 1.41 | - | 1629.00 (1629.00-1629.00) [1960.50 (1705.50-2007.00)] | 1145.83 (ESTIMATE) | 1.42 |
| if_loop_2 | PASS | 3 + 1 / 4 | 12 / 12; 4 / 4 | 29.77 (26.38-32.36) [29.54 (29.54-29.54)] | 3288 | 1541 | 16.67 (ESTIMATE) | 1.79 | - | 1929.00 (1743.00-2142.75) [1989.75 (1989.75-1989.75)] | 1063.98 (ESTIMATE) | 1.81 |
| iir | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 3 / 3 | -; 12 / 12 | - [55.15 (55.09-57.72)] | 57696 | 1184 | 48.68 (ESTIMATE) | - | - | 56868.00 (54852.00-59310.00) | - | - |
| image_resize | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 2 / 2 | -; 8 / 8 | - [69.67 (69.12-70.23)] | 63504 | 2454 | 18.95 (ESTIMATE) | - | - | 63180.00 (61782.00-64578.00) | - | - |
| ipow | PASS | 6 + 2 / 8 | 48 / 48; 16 / 16 | 19.95 (18.71-21.58) [22.96 (22.57-23.36)] | 780 | 1341 | 49.98 (ESTIMATE) | 0.40 | 36.20 | 263.29 (254.12-277.41) [294.71 (292.94-296.47)] | 513.90 (ESTIMATE) | 0.51 |
| isprime | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 3 / 3 | -; 12 / 12 | - [fit 49.65 (49.30-52.87)] | 16632 | 3954 | 9.26 (ESTIMATE) | - | - | 4402.67 (4358.33-4658.67) | 2501.23 (ESTIMATE) | 1.76 |
| iterative_division | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 4 / 4 | -; 16 / 16 | - [25.97 (24.97-31.51)] | 8160 | 3814 | 10.23 (ESTIMATE) | - | - | 1896.60 (1871.20-2326.40) | 754.13 (ESTIMATE) | 2.51 |
| iterative_sqrt | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 4 / 4 | -; 16 / 16 | - [64.45 (62.67-64.91)] | 1164 | 2249 | 110.84 (ESTIMATE) | - | - | 489.50 (487.00-497.50) | 758.20 (ESTIMATE) | 0.65 |
| lfsrfind | PASS | 2 + 2 / 4 | 8 / 8; 8 / 8 | 25.33 (23.18-27.48) [27.79 (26.32-29.27)] | 7536 | 890 | 19.52 (ESTIMATE) | 1.30 | - | 1190.70 (1077.00-1304.40) [1305.90 (1216.80-1395.00)] | 901.06 (ESTIMATE) | 1.32 |
| loop_path | PASS | 2 + 0 / 2 | 8 / 8; - | 45.23 (41.61-48.85) | 8208 | 1045 | 32.27 (ESTIMATE) | 1.40 | - | 7713.00 (7230.00-8196.00) | - | - |
| memsum | PASS | 2 + 2 / 4 | 6 / 6; 8 / 8 | 29.43 (27.48-31.39) [29.08 (28.15-30.01)] | 1068 | 1394 | 59.33 (ESTIMATE) | 0.50 | - | 578.40 (552.00-604.80) [570.60 (560.40-580.80)] | 1033.21 (ESTIMATE) | 0.56 |
| mul_example | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 3 / 3 | -; 12 / 12 | - [59.88 (55.17-66.61)] | 6696 | 334 | 79.88 (ESTIMATE) | - | - | 6066.00 (5676.00-6858.00) | - | - |
| nest3 | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 4 / 4 | -; 16 / 16 | - [fit 48.57 (47.51-51.16)] | 4992 | 5437 | 11.06 (ESTIMATE) | - | - | 1007.75 (983.50-1050.50) | 545.62 (ESTIMATE) | 1.85 |
| nested | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 4 / 4 | -; 16 / 16 | - [fit 29.73 (27.57-34.14)] | 8556 | 3554 | 9.98 (ESTIMATE) | - | - | 1091.73 (1027.09-1222.91) | 416.53 (ESTIMATE) | 2.62 |
| nested_loop | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 4 / 4 | -; 16 / 16 | - [44.89 (40.44-46.05)] | 18576 | 1303 | 44.56 (ESTIMATE) | - | - | 18357.00 (16356.00-18996.00) | - | - |
| quadrec | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 4 / 4 | -; 16 / 16 | - [44.85 (37.71-45.98)] | 11796 | 3291 | 9.09 (ESTIMATE) | - | - | 1689.60 (1393.20-1727.40) | 352.76 (ESTIMATE) | 4.79 |
| share_test_1 | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 1 / 1 | -; 4 / 4 | - [27.27 (27.27-27.27)] | 55548 | 1663 | 58.41 (ESTIMATE) | - | - | 55074.00 (55074.00-55074.00) | - | - |
| share_test_2 | NOT-A-BOARD-ROUTE | 0 + 0 / 4 | -; - | - | - | - | 91.89 (ESTIMATE) | - | - | - | - | - |
| simple_example_1 | PASS | 4 + 0 / 4 | 16 / 16; - | - | 72 | 86 | - | - | - | 72.00 (72.00-72.00) | - | - |
| single_loop | PASS | 1 + 0 / 1 | 4 / 4; - | 46.04 (46.04-46.04) | 23112 | 735 | 40.32 (ESTIMATE) | 1.14 | - | 22974.00 (22974.00-22974.00) | - | - |
| sobel | NO RESULT (no finished route yet: suite10b's loops ran out of time; resumed in suite10c, running) | 0 / 0 | - | - | - | - | 43.37 (ESTIMATE) | - | - | - | - | - |
| spmv | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 4 / 4 | -; 16 / 16 | - | 1512 | 4027 | 43.09 (ESTIMATE) | - | - | 900.75 (874.50-946.50) | - | - |
| sqrtsub | PASS | 1 + 3 / 4 | 4 / 4; 12 / 12 | 23.91 (23.91-23.91) [21.81 (21.17-24.36)] | 6300 | 1398 | 8.36 (ESTIMATE) | 2.86 | - | 881.08 (881.08-881.08) [784.62 (759.23-896.77)] | 292.00 (ESTIMATE) | 3.02 |
| stencil_2d | PASS | 1 + 2 / 3 | 4 / 4; 8 / 8 | 408.13 (408.13-408.13) [407.69 (375.76-439.62)] | 12360 | 2335 | 40.43 (ESTIMATE) | 10.09 (not comparable: out of the mean) | - | 11652.00 (11652.00-11652.00) [11547.00 (10788.00-12306.00)] | - | - |
| straight | PASS | 3 + 1 / 4 | 12 / 12; 4 / 4 | - | 72 | 1327 | - | - | - | 72.00 (72.00-72.00) [72.00 (72.00-72.00)] | 14.92 (ESTIMATE) | 4.83 |
| sumi3_mem | PASS | 4 + 0 / 4 | 8 / 8; - | 25.99 (23.22-27.86) | 27912 | 610 | 88.44 (ESTIMATE) | 0.29 | - | 26451.00 (23040.00-29226.00) | 88540.06 (ESTIMATE) | 0.30 |
| test_bitint | PASS | 1 + 3 / 4 | 4 / 4; 12 / 12 | - | 300 | 635 | 44.32 (ESTIMATE) | - | - | 294.00 (294.00-294.00) [288.00 (276.00-288.00)] | 504.74 (ESTIMATE) | 0.58 |
| test_bool_array | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 4 / 4 | -; 16 / 16 | - | 96 | 112 | - | - | - | 96.00 (84.00-96.00) | - | - |
| test_divui | PASS | 7 + 1 / 8 | 28 / 28; 4 / 4 | - | 480 | 2286 | - | - | - | 192.00 (180.00-516.00) [252.00 (252.00-252.00)] | - | - |
| test_flatten_array | PASS | 1 + 3 / 4 | 4 / 4; 12 / 12 | - [57.48 (57.48-57.48)] | 29580 | 1544 | 15.74 (ESTIMATE) | - | - | 25878.00 (25878.00-25878.00) [29640.00 (28230.00-29934.00)] | - | - |
| test_int16 | PASS | 4 + 0 / 4 | 16 / 16; - | - | 60 | 3 | - | - | - | 60.00 (60.00-60.00) | - | - |
| test_loop_free | PASS | 4 + 0 / 4 | 16 / 16; - | - | 72 | 1007 | - | - | - | 72.00 (72.00-72.00) | 11.55 (ESTIMATE; period extrapolated, model path 4.86 ns) | 6.23 (extrapolated period) |
| test_memory_1 | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 4 / 4 | -; 16 / 16 | - | 288 | 1048 | 13.94 (ESTIMATE) | - | - | 172.50 (168.00-180.00) | - | - |
| test_memory_2 | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 4 / 4 | -; 16 / 16 | - | 288 | 1172 | 13.94 (ESTIMATE) | - | - | 167.14 (159.43-169.71) | - | - |
| test_stdint | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 4 / 4 | -; 16 / 16 | - [50.02 (47.97-53.50)] | 5388 | 399 | 80.67 (ESTIMATE) | - | - | 5043.00 (4848.00-5364.00) | - | - |
| twoloops | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 4 / 4 | -; 16 / 16 | - [18.34 (17.33-18.74)] | 4884 | 2259 | 9.09 (ESTIMATE) | - | - | 1132.91 (1130.73-1214.18) | 514.10 (ESTIMATE) | 2.20 |
| unused_arg | PASS | 4 + 0 / 4 | 16 / 16; - | - | 72 | 86 | - | - | - | 72.00 (72.00-72.00) | 1.95 (ESTIMATE; period extrapolated, model path 1.23 ns) | 36.92 (extrapolated period) |
| varshift | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 4 / 4 | -; 16 / 16 | - [34.22 (29.19-39.06)] | 10056 | 2524 | 11.84 (ESTIMATE) | - | - | 1452.60 (1252.80-1620.00) | 493.64 (ESTIMATE) | 2.94 |
| vector_rescale | UNFINISHED (draws pass on NOT CLEAN routes only) | 0 + 3 / 3 | -; 12 / 12 | - [58.10 (55.10-60.02)] | 60048 | 588 | 48.68 (ESTIMATE) | - | - | 57840.00 (55428.00-61164.00) | - | - |
| video_filter | NO RESULT (no finished route yet: suite10b's loops ran out of time; resumed in suite10c, running) | 0 / 0 | - | - | - | - | 57.14 (ESTIMATE) | - | - | - | - | - |
| while_loop_3 | PASS | 3 + 1 / 4 | 12 / 12; 4 / 4 | 24.86 (24.49-25.75) [27.57 (27.57-27.57)] | 996 | 800 | 34.00 (ESTIMATE) | 0.73 | - | 288.00 (288.00-299.14) [307.71 (307.71-307.71)] | - | - |
| xorshift | PASS | 6 + 2 / 8 | 48 / 48; 16 / 16 | 22.16 (20.42-23.57) [20.89 (20.55-21.23)] | 6096 | 1316 | 12.73 (measured, 1 route) | 1.74 | 16.76 | 2252.84 (2097.47-2427.16) [2124.95 (2061.16-2188.74)] | 1257.59 (cycles simulated, period measured (1 route)) | 1.79 |

34 of 62 kernels attempted pass (a kernel passes when it has a judged rule-CLEAN route and every draw on every judged route, clean or not, returned every right answer; ns per iteration, latency and the ratios are over rule-CLEAN routes only, the NOT CLEAN routes' figures in brackets); 25 more pass every draw only on routes the sizing loop left NOT CLEAN (UNFINISHED: the rule names a short constraint on each, and such a route can pass 4 draws and fail the model a third of the time, formal C68), not counted; geometric mean of the ratio (ns per iteration / Dynamatic's) over passing kernels with a MEASURED Dynamatic figure (n = 3): 1.69; including ESTIMATED figures (n = 22; 1 with our figure from the latency fit): 1.05. Our ns are the simulation's (about 8 % slower per iteration than the August board on the same bitstreams, research/SIM-VS-BOARD.md); Dynamatic's measured figures are single nextpnr routes (Fmax), not board runs. Latency per call (ours / Dynamatic's, same calls, ESTIMATED except cycles x the routed period for the 3 measured kernels; ours includes the bench): geometric mean over passing kernels (n = 19): 1.22.

P refused (off its route's own slope of call latency on the most executed loop's trip counts by more than 15 %: the event graph's marker was on another loop; the slope is used): branchloop seed 1 P=14.22 ns against a slope of 31.83 ns (0.45x); branchloop seed 2 P=14.52 ns against a slope of 34.44 ns (0.42x); branchloop seed 3 P=13.47 ns against a slope of 30.01 ns (0.45x); branchloop seed 4 P=14.79 ns against a slope of 31.35 ns (0.47x); gcd seed 1 P=62.82 ns against a slope of 29.05 ns (2.16x); gcd seed 3 P=61.42 ns against a slope of 28.36 ns (2.17x); gcd seed 4 P=66.30 ns against a slope of 31.16 ns (2.13x); isprime seed 2 P=346.76 ns against a slope of 49.30 ns (7.03x); isprime seed 3 P=358.38 ns against a slope of 49.65 ns (7.22x); isprime seed 4 P=374.58 ns against a slope of 52.87 ns (7.08x).

Routes whose draws had a pulse under 1 ns on a kernel handshake net (not counted as passing evidence, whatever their answers): if_loop_1 seed 4 (NOT CLEAN, pulses <150/500/1000 ps 2/2/2 in its worst draw); test_memory_1 seed 2 (NOT CLEAN, pulses <150/500/1000 ps 72/73/78 in its worst draw).

**The same flow WITH the three md5-keyed rewrites (BDC_AUTO_REWRITES=1; farm suite6, 8 seeds, 8 draws; not the automatic
column):** collatz PASS, 6 + 2 routes (clean + NOT CLEAN), 48 / 48 + 16 / 16 draws, P on clean routes 17.24 (16.20-19.46)
ns; collatz64 PASS, 2 + 5, 16 / 16 + 40 / 40, 23.01 (22.13-23.89); xorshift PASS, 4 + 3, 32 / 32 + 24 / 24, 22.71
(19.43-23.46). Board items 39-41 are from this variant (flow v3).

Earlier headlines (flow v3, suite4, all with the rewrites on the three kernels): collatz 18.98, collatz64 23.71, ipow
24.10, xorshift 20.11 ns per iteration (27 routes, 216 / 216 draws).

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
