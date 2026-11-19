**THE AUTOMATIC COLUMN, every kernel the suite lists (corrected 2026-11-18 22:55 UTC for auditor T161 and the owner's
T156 / T161 rules; it replaces the headline of eaef0dec7, which the audit marked OVERSTATED).** One switch, BDC_AUTO=1,
with no list of kernels (the md5-keyed MLIR rewrites are off since f7573b807), the flow's own sizing loop (flow v6),
judged by draws of the delay model; farm suite3a / 3b / 8 / 9 (suite kernels, seeds 1-4 / 1-2, 4 draws), suite6 (ipow,
8 seeds, 8 draws; the rewrites never touched ipow), suite7 (isprime), norw1 / norw1r2 (xorshift, collatz,
collatz64 with no kernel list, 8 seeds, 8 draws), gifast1 (gcd, isprime with CA_FAST: their loops now finish), suite9r3
(suite9's unfinished loops resumed), nsearch1 (flow v7's search phase on finished loops: countloop's routes are v7), suite10b (running: the kernels new
to the flow); nextpnr 6e5d224472232d5d (suite3a / 3b and part of
suite6's predecessors used 9c732bc6303458df: identical routes where no GND pin was missed). A seed is one route: where
two requests ran the same seed, the later one is counted. **What the audit found, and what changed:** (1) the earlier
headline's xorshift / collatz / collatz64 numbers used the three md5-keyed rewrites -- they are now under the table under
their own name, and the column without a list runs on the farm (norw1); (2) it counted 20 kernels; the suite lists 62,
every one has a row below, with its reason where there is no number; (3) 34 of its 65 judged routes ended NOT CLEAN by
the sizing rule, unstated -- now kept apart: routes, draws and P are given for rule-clean and NOT CLEAN routes
separately, and ns per iteration and the ratio use rule-CLEAN routes only (two NOT CLEAN routes have been wrong: ipow
seed 4 in flow v1, if_loop_1 seed 1 below); (4) isprime's ratio (an outer-trial period against Dynamatic's inner-shift
cycle) is out of every mean; (5) dot2's "156 ns" was the host's array fill: refused (an exact multiple of the host
clock). Dynamatic's figures are ESTIMATES except for xorshift / collatz / collatz64 (single nextpnr routes, Fmax x
cycles); our ns are the simulation's (~8 % slower per iteration than the August board, research/SIM-VS-BOARD.md).
Command: `research/tools/suite/suite_table.py --kernels research/tools/suite/kernels.txt --reasons
research/data/suite/headline_reasons.tsv --no-ratio isprime <the farm result dirs>`.

| kernel | status | routes judged (rule-clean + NOT CLEAN) / built | draws passing (clean; not clean) | ns per iteration (P) on clean routes, median (range) [on NOT CLEAN routes] | worst latency per call, ns | kernel LUTs | Dynamatic, ns per iteration | ratio | hand recipe's best, ns | latency per call, ns: ours, mean over the calls, median (range) over routes | Dynamatic, latency per call, ns | latency ratio |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| binary_search | NO RESULT (added 2026-11-18 (research/data/suite/dyn/README.md: RTL and, for 13 of them, a routed smoke at default sizes); through the automatic path in farm suite10b (running)) | 0 / 0 | - | - | - | - | 24.18 (ESTIMATE) | - | - | - | - | - |
| branchloop | PASS | 1 + 3 / 4 | 4 / 4; 12 / 12 | 14.79 (14.79-14.79) [14.22 (13.47-14.52)] | 2160 | 2213 | 36.77 (ESTIMATE) | 0.40 | - | 489.86 (463.29-522.43) | 486.08 (ESTIMATE) | 1.01 |
| brhash | PASS | 0 + 4 / 4 | -; 16 / 16 | - [fit 32.08 (30.73-34.34)] | 8664 | 2110 | 36.40 (ESTIMATE) | - | - | 1314.30 (1261.20-1402.80) | 1443.81 (ESTIMATE) | 0.91 |
| cmpchain | PASS | 0 + 2 / 4 | -; 8 / 8 | - | 120 | 3076 | - | - | - | 102.53 (100.94-104.12) | 33.90 (ESTIMATE) | 3.02 |
| collatz | PASS | 5 + 3 / 8 | 40 / 40; 24 / 24 | 22.54 (18.98-25.56) [22.86 (22.79-26.70)] | 7032 | 1289 | 14.05 (measured, 1 route) | 1.60 | 21.50 | 2275.06 (1845.18-2625.18) | 1362.02 (cycles simulated, period measured (1 route)) | 1.67 |
| collatz64 | PASS | 3 + 4 / 7 | 24 / 24; 32 / 32 | 30.93 (29.89-31.49) [30.15 (28.10-32.12)] | 11304 | 1917 | 17.84 (measured, 1 route) | 1.73 | 31.40 | 7231.00 (6792.67-7504.00) | 4131.94 (cycles simulated, period measured (1 route)) | 1.75 |
| countloop | PASS | 4 + 0 / 4 | 16 / 16; - | 21.14 (20.45-24.30) | 6276 | 1812 | 8.36 (ESTIMATE) | 2.53 | - | 893.10 (865.80-1018.20) | 341.14 (ESTIMATE) | 2.62 |
| digitdiv | NO RESULT (compiles since 2026-11-18 (research/data/suite/divmod.md: routed smokes at default sizes pass on 4 / 4 seeds for digitdiv, divmodu, divmods); through the automatic path in farm suite10b (running)) | 0 / 0 | - | - | - | - | 303.77 (ESTIMATE) | - | - | - | - | - |
| digitsum | NO RESULT (compiles since 2026-11-18 (research/data/suite/divmod.md: routed smokes at default sizes pass on 4 / 4 seeds for digitdiv, divmodu, divmods); through the automatic path in farm suite10b (running)) | 0 / 0 | - | - | - | - | - | - | - | - | - | - |
| divmods | NO RESULT (compiles since 2026-11-18 (research/data/suite/divmod.md: routed smokes at default sizes pass on 4 / 4 seeds for digitdiv, divmodu, divmods); through the automatic path in farm suite10b (running)) | 0 / 0 | - | - | - | - | - | - | - | - | - | - |
| divmodu | NO RESULT (compiles since 2026-11-18 (research/data/suite/divmod.md: routed smokes at default sizes pass on 4 / 4 seeds for digitdiv, divmodu, divmods); through the automatic path in farm suite10b (running)) | 0 / 0 | - | - | - | - | - | - | - | - | - | - |
| dot2 | PASS | 1 + 3 / 4 | 4 / 4; 12 / 12 | 30.97 (30.97-30.97) [33.84 (33.39-34.28)] | 1152 | 1436 | 59.28 (ESTIMATE) | 0.52 | - | 717.75 (640.50-761.25) | 1212.19 (ESTIMATE) | 0.59 |
| factorial | PASS | 0 + 4 / 4 | -; 16 / 16 | - | 204 | 2635 | 129.79 (ESTIMATE) | - | - | 139.00 (131.00-142.00) | 233.79 (ESTIMATE) | 0.59 |
| fill | PASS | 1 + 2 / 3 | 4 / 4; 8 / 8 | 32.17 (32.17-32.17) [29.88 (29.42-30.34)] | 1344 | 1942 | 10.95 (ESTIMATE) | 2.94 | - | 546.00 (528.00-574.80) | 208.09 (ESTIMATE) | 2.62 |
| fir | NO RESULT (no finished seed yet: the sizing loop hit the farm's 240-min limit (suite3a / 3b / 8 / 9); resumed in suite9r3 / redone in suite10b) | 0 / 0 | - | - | - | - | 48.68 (ESTIMATE) | - | - | - | - | - |
| fold64 | PASS | 0 + 3 / 3 | -; 12 / 12 | - [23.96 (23.67-24.25)] | 6252 | 2785 | 11.93 (ESTIMATE) | - | - | 939.60 (901.80-943.20) | 448.74 (ESTIMATE) | 2.09 |
| gather | PASS | 0 + 4 / 4 | -; 16 / 16 | - [51.69 (48.15-55.22)] | 1824 | 1493 | 69.20 (ESTIMATE) | - | - | 1210.00 (1124.00-1244.67) | 1510.48 (ESTIMATE) | 0.80 |
| gcd | PASS | 0 + 3 / 4 | -; 12 / 12 | - [62.82 (61.42-66.30)] | 2172 | 7178 | 50.60 (ESTIMATE) | - | 87.20 | 600.00 (593.25-628.50) | 429.97 (ESTIMATE) | 1.40 |
| horner | PASS | 1 + 3 / 4 | 4 / 4; 12 / 12 | 28.03 (28.03-28.03) [30.22 (29.25-31.28)] | 8064 | 1735 | 41.81 (ESTIMATE) | 0.67 | - | 1193.45 (1147.09-1233.27) | 1601.58 (ESTIMATE) | 0.75 |
| if_convert | NO RESULT (added 2026-11-18 (research/data/suite/dyn/README.md: RTL and, for 13 of them, a routed smoke at default sizes); through the automatic path in farm suite10b (running)) | 0 / 0 | - | - | - | - | 65.70 (ESTIMATE) | - | - | - | - | - |
| if_loop_1 | WRONG ANSWER under draws | 0 + 4 / 4 | -; 14 / 16 | - [30.66 (27.52-33.70)] | 3432 | 1865 | 19.90 (ESTIMATE) | - | - | 1822.12 (1615.50-2007.00) | 1145.83 (ESTIMATE) | 1.59 |
| if_loop_2 | PASS | 3 + 1 / 4 | 12 / 12; 4 / 4 | 29.77 (26.38-32.36) [29.54 (29.54-29.54)] | 3288 | 1541 | 16.67 (ESTIMATE) | 1.79 | - | 1959.38 (1743.00-2142.75) | 1063.98 (ESTIMATE) | 1.84 |
| iir | NO RESULT (added 2026-11-18 (research/data/suite/dyn/README.md: RTL and, for 13 of them, a routed smoke at default sizes); through the automatic path in farm suite10b (running)) | 0 / 0 | - | - | - | - | 48.68 (ESTIMATE) | - | - | - | - | - |
| image_resize | NO RESULT (added 2026-11-18 (research/data/suite/dyn/README.md: RTL and, for 13 of them, a routed smoke at default sizes); through the automatic path in farm suite10b (running)) | 0 / 0 | - | - | - | - | 18.95 (ESTIMATE) | - | - | - | - | - |
| ipow | PASS | 2 + 5 / 7 | 16 / 16; 40 / 40 | 21.39 (21.20-21.58) [21.73 (19.84-23.36)] | 780 | 1331 | 49.98 (ESTIMATE) | 0.43 | 36.20 | 276.35 (261.53-296.47) | 513.90 (ESTIMATE) | 0.54 |
| isprime | PASS | 0 + 3 / 3 | -; 12 / 12 | - [358.38 (346.76-374.58)] | 16632 | 3954 | 9.26 (ESTIMATE) | - | - | 4402.67 (4358.33-4658.67) | 2501.23 (ESTIMATE) | 1.76 |
| iterative_division | PASS | 0 + 3 / 3 | -; 12 / 12 | - [26.05 (24.97-31.51)] | 8160 | 3829 | 10.23 (ESTIMATE) | - | - | 1921.60 (1871.20-2326.40) | 754.13 (ESTIMATE) | 2.55 |
| iterative_sqrt | PASS | 0 + 3 / 3 | -; 12 / 12 | - [64.08 (62.67-64.34)] | 1152 | 2235 | 110.84 (ESTIMATE) | - | - | 490.50 (487.00-490.50) | 758.20 (ESTIMATE) | 0.65 |
| lfsrfind | PASS | 2 + 2 / 4 | 8 / 8; 8 / 8 | 25.33 (23.18-27.48) [27.79 (26.32-29.27)] | 7536 | 890 | 19.52 (ESTIMATE) | 1.30 | - | 1260.60 (1077.00-1395.00) | 901.06 (ESTIMATE) | 1.40 |
| loop_path | NO RESULT (added 2026-11-18 (research/data/suite/dyn/README.md: RTL and, for 13 of them, a routed smoke at default sizes); through the automatic path in farm suite10b (running)) | 0 / 0 | - | - | - | - | 32.27 (ESTIMATE) | - | - | - | - | - |
| memsum | PASS | 1 + 2 / 3 | 4 / 4; 8 / 8 | 27.48 (27.48-27.48) [29.08 (28.15-30.01)] | 1020 | 1395 | 59.33 (ESTIMATE) | 0.46 | - | 560.40 (552.00-580.80) | 1033.21 (ESTIMATE) | 0.54 |
| mul_example | PASS | 0 + 1 / 1 | -; 4 / 4 | - [55.17 (55.17-55.17)] | 5556 | 317 | 79.88 (ESTIMATE) | - | - | 5676.00 (5676.00-5676.00) | - | - |
| nest3 | NO RESULT (no finished seed yet: the sizing loop hit the farm's 240-min limit (suite3a / 3b / 8 / 9); resumed in suite9r3 / redone in suite10b) | 0 / 0 | - | - | - | - | 11.06 (ESTIMATE) | - | - | - | - | - |
| nested | PASS | 0 + 3 / 3 | -; 12 / 12 | - | 8556 | 3556 | 9.98 (ESTIMATE) | - | - | 1100.18 (1027.09-1222.91) | 416.53 (ESTIMATE) | 2.64 |
| nested_loop | NO RESULT (added 2026-11-18 (research/data/suite/dyn/README.md: RTL and, for 13 of them, a routed smoke at default sizes); through the automatic path in farm suite10b (running)) | 0 / 0 | - | - | - | - | 44.56 (ESTIMATE) | - | - | - | - | - |
| quadrec | PASS | 0 + 3 / 3 | -; 12 / 12 | - [45.77 (43.93-45.98)] | 11796 | 3300 | 9.09 (ESTIMATE) | - | - | 1709.40 (1669.80-1727.40) | 352.76 (ESTIMATE) | 4.85 |
| share_test_1 | NO RESULT (added 2026-11-18 (research/data/suite/dyn/README.md: RTL and, for 13 of them, a routed smoke at default sizes); through the automatic path in farm suite10b (running)) | 0 / 0 | - | - | - | - | 58.41 (ESTIMATE) | - | - | - | - | - |
| share_test_2 | NOT-A-BOARD-ROUTE | 0 + 0 / 2 | -; - | - | - | - | 91.89 (ESTIMATE) | - | - | - | - | - |
| simple_example_1 | PASS | 2 + 0 / 2 | 8 / 8; - | - | 72 | 85 | - | - | - | 72.00 (72.00-72.00) | - | - |
| single_loop | NO RESULT (added 2026-11-18 (research/data/suite/dyn/README.md: RTL and, for 13 of them, a routed smoke at default sizes); through the automatic path in farm suite10b (running)) | 0 / 0 | - | - | - | - | 40.32 (ESTIMATE) | - | - | - | - | - |
| sobel | NO RESULT (added 2026-11-18 (research/data/suite/dyn/README.md); through the automatic path in farm suite10b (running) (RTL passes in both flows once the testbench covers the RAM model's clock-to-out: research/data/suite/memorder.md)) | 0 / 0 | - | - | - | - | 43.37 (ESTIMATE) | - | - | - | - | - |
| spmv | NO RESULT (added 2026-11-18 (research/data/suite/dyn/README.md); through the automatic path in farm suite10b (running) (RTL passes in both flows once the testbench covers the RAM model's clock-to-out: research/data/suite/memorder.md)) | 0 / 0 | - | - | - | - | 43.09 (ESTIMATE) | - | - | - | - | - |
| sqrtsub | PASS | 1 + 3 / 4 | 4 / 4; 12 / 12 | 23.91 (23.91-23.91) [21.81 (21.17-24.36)] | 6300 | 1398 | 8.36 (ESTIMATE) | 2.86 | - | 832.85 (759.23-896.77) | 292.00 (ESTIMATE) | 2.85 |
| stencil_2d | NO RESULT (added 2026-11-18 (research/data/suite/dyn/README.md: RTL and, for 13 of them, a routed smoke at default sizes); through the automatic path in farm suite10b (running)) | 0 / 0 | - | - | - | - | 40.43 (ESTIMATE) | - | - | - | - | - |
| straight | PASS | 3 + 1 / 4 | 12 / 12; 4 / 4 | - | 72 | 1327 | - | - | - | 72.00 (72.00-72.00) | 14.92 (ESTIMATE) | 4.83 |
| sumi3_mem | NO RESULT (no finished seed yet: the sizing loop hit the farm's 240-min limit (suite3a / 3b / 8 / 9); resumed in suite9r3 / redone in suite10b) | 0 / 0 | - | - | - | - | 88.44 (ESTIMATE) | - | - | - | - | - |
| test_bitint | PASS | 1 + 3 / 4 | 4 / 4; 12 / 12 | - | 300 | 635 | 44.32 (ESTIMATE) | - | - | 288.00 (276.00-294.00) | 504.74 (ESTIMATE) | 0.57 |
| test_bool_array | PASS | 0 + 2 / 2 | -; 8 / 8 | - | 96 | 113 | - | - | - | 96.00 (96.00-96.00) | - | - |
| test_divui | WRONG ANSWER under draws | 2 + 0 / 2 | 0 / 8; - | - | 60 | 1937 | - | - | - | 60.00 (60.00-60.00) | - | - |
| test_flatten_array | NO RESULT (added 2026-11-18 (research/data/suite/dyn/README.md: RTL and, for 13 of them, a routed smoke at default sizes); through the automatic path in farm suite10b (running)) | 0 / 0 | - | - | - | - | 15.74 (ESTIMATE) | - | - | - | - | - |
| test_int16 | PASS | 4 + 0 / 4 | 16 / 16; - | - | 60 | 3 | - | - | - | 60.00 (60.00-60.00) | - | - |
| test_loop_free | PASS | 4 + 0 / 4 | 16 / 16; - | - | 72 | 1007 | - | - | - | 72.00 (72.00-72.00) | 11.55 (ESTIMATE; period extrapolated, model path 4.86 ns) | 6.23 (extrapolated period) |
| test_memory_1 | PASS | 0 + 2 / 2 | -; 8 / 8 | - | 288 | 1052 | 13.94 (ESTIMATE) | - | - | 178.00 (176.00-180.00) | - | - |
| test_memory_2 | PASS | 0 + 2 / 2 | -; 8 / 8 | - | 276 | 1172 | 13.94 (ESTIMATE) | - | - | 162.00 (159.43-164.57) | - | - |
| test_stdint | PASS | 0 + 2 / 2 | -; 8 / 8 | - [48.29 (47.97-48.62)] | 4896 | 399 | 80.67 (ESTIMATE) | - | - | 4860.00 (4848.00-4872.00) | - | - |
| twoloops | PASS | 0 + 4 / 4 | -; 16 / 16 | - [18.34 (17.33-18.74)] | 4884 | 2259 | 9.09 (ESTIMATE) | - | - | 1132.91 (1130.73-1214.18) | 514.10 (ESTIMATE) | 2.20 |
| unused_arg | PASS | 4 + 0 / 4 | 16 / 16; - | - | 72 | 86 | - | - | - | 72.00 (72.00-72.00) | 1.95 (ESTIMATE; period extrapolated, model path 1.23 ns) | 36.92 (extrapolated period) |
| varshift | PASS | 0 + 4 / 4 | -; 16 / 16 | - [34.22 (29.19-39.06)] | 10056 | 2524 | 11.84 (ESTIMATE) | - | - | 1452.60 (1252.80-1620.00) | 493.64 (ESTIMATE) | 2.94 |
| vector_rescale | NO RESULT (added 2026-11-18 (research/data/suite/dyn/README.md: RTL and, for 13 of them, a routed smoke at default sizes); through the automatic path in farm suite10b (running)) | 0 / 0 | - | - | - | - | 48.68 (ESTIMATE) | - | - | - | - | - |
| video_filter | NO RESULT (added 2026-11-18 (research/data/suite/dyn/README.md: RTL and, for 13 of them, a routed smoke at default sizes); through the automatic path in farm suite10b (running)) | 0 / 0 | - | - | - | - | 57.14 (ESTIMATE) | - | - | - | - | - |
| while_loop_3 | PASS | 1 + 0 / 1 | 4 / 4; - | 25.75 (25.75-25.75) | 936 | 799 | 34.00 (ESTIMATE) | 0.76 | - | 299.14 (299.14-299.14) | - | - |
| xorshift | PASS | 6 + 2 / 8 | 48 / 48; 16 / 16 | 22.16 (20.42-23.57) [20.89 (20.55-21.23)] | 6096 | 1316 | 12.73 (measured, 1 route) | 1.74 | 16.76 | 2214.79 (2061.16-2427.16) | 1257.59 (cycles simulated, period measured (1 route)) | 1.76 |

38 of 62 kernels attempted pass (a kernel passes when it has a judged route and every draw on every judged route, clean or not, returned every right answer; ns per iteration and the ratio are over rule-CLEAN routes only, the NOT CLEAN routes' P in brackets); geometric mean of the ratio (ns per iteration / Dynamatic's) over passing kernels with a MEASURED Dynamatic figure (n = 3): 1.69; including ESTIMATED figures (n = 14): 1.12. Our ns are the simulation's (about 8 % slower per iteration than the August board on the same bitstreams, research/SIM-VS-BOARD.md); Dynamatic's measured figures are single nextpnr routes (Fmax), not board runs. Latency per call (ours / Dynamatic's, same calls, ESTIMATED except cycles x the routed period for the 3 measured kernels; ours includes the bench): geometric mean over passing kernels (n = 27): 1.49.

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
