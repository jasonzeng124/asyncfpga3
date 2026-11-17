# For research and the owner: THE goal (the gcd_hw bitstream theorem)

Started 2026-11-01 by shard A. Counterexamples to THE theorem go here first (PROGRAM.md). The older,
rule-by-rule list is `formal/out/FOR-RESEARCH.md`.


## B2. Paths no vector can reach, reached: with the loop counter preloaded, xorshift's incrementer (UADDI0) can go from 12 to 0 -- 112/112 preloaded draws pass on 4 routes, its 30-bit carry keeps >= 8.0 ns, and the routes run ~5 % faster; collatz / collatz64 counters and 63-bit values the same way (shard B, 2026-11-17 20:58 UTC; untrusted simulation)
Your PROGRAM "Paths no vector can reach" asked for exactly this; formal's PROGRAM gave it to B. Formal's simx on the circuit
decoded from each bitstream, your draw K, H_RUNT(20), host 12 ns. Every build here was rebuilt locally from your command
(nextpnr 9c732bc6303458df); sdf md5s below.
- **How (one command, `formal/tools-B/preload/prun.sh`):** a loop counter enters its loop from a CONSTANT (xorshift's i = 0
  goes through the pipe `ulink_n6`, whose 64 latch halves read GND; collatz's steps = 0 through `ulink_n7`). The tool gives
  those latch state nodes the constant value I0 from t = 0, after checking on an ordinary run that they are constant 0 there,
  so the run is the same bitstream with the entry constant tied to I0 instead of 0; nothing else changes. The expected
  answers come from `oracle.c`, the kernel's C loop copied verbatim with `int i = i0` (`int steps = s0`), refusing inputs
  where the two cannot agree (xorshift needs I0 < rounds: the hardware's loop runs the body once before testing).
  Checks: bit 30 of i + 1 (ulink_n_trueResult_6) flips 7 times in a preloaded run and never in xor19; the same run checked
  against the oracle at I0 + 1 fails.
- **The preload can fail where your vectors cannot (negative control):** +20 ns on the carry-in of uaddi0's slice[4] (the
  carry into bit 16; formal's simx injection, like your SDF injections): xor19 PASS (that carry never moves for rounds <=
  4095), preloaded FAIL, wrong exactly on the calls that use i + 1 = 0x40000000.
- **Vectors.** A: I0 0x3ffffff0, rounds 0x3ffffff1 / 0x3fffffff / 0x40000000 / 0x40000001 (x2) / 0x40000002 / 0x40000010
  (1-32 iterations; i + 1 = 0x40000000, the longest carry the C can ever produce, since i < rounds <= 2^31 - 1, in 5
  calls, its result used in 4; n - 1 = 0x3fffffff in one). B: I0 0x7ffffff0, rounds 0x7ffffff1 .. 0x7fffffff (the compares
  at the top of the range). Ordinary vectors with rounds = 0x80000000 / 0xffffffff / 0xc0000000 (loop skipped): 8/8 on item 35.
| xorshift, item 35's sizes with UADDI0 = | route (sdf) | xor19 draws | preload A | preload B | carry-into-bit-16 slack, ps | period, ps (2 draws) |
|---|---|---|---|---|---|---|
| 12 (item 35) | 21 (9145cd49) | 2/2 | 32/32 (+ 32/32 at CARRY 0.8-1.0) | 32/32 | >= 9140 (fails 9179) | 14427 / 14214 |
| 12 | 2 (b2470514) | 8/8 | 16/16 | 16/16 | >= 8906 | 14213 / 13982 |
| 12 | 4 (ee6304d0) | 8/8 | 16/16 | 16/16 | >= 9453 | 14855 / 14402 |
| 12 | 5 (7a448319) | 8/8 | 16/16 | 16/16 | >= 9531 | 14137 / 14020 |
| 7 (x0.55) | 21 (0a993f62) | 4/4 | 16/16 | 16/16 | >= 8164 | 13901 / 14123 |
| 2 | 21 (fafe42b5) | 4/4 | 8/8 | 8/8 | - | 13883 / 13590 |
| 0 | 21 (96a395ab) | 4/4 | 8/8 | 8/8 | >= 8828 | 14193 / 14196 |
| 0 | 2 (2b8ef891) | 8/8 | 16/16 | 16/16 | >= 8125 | 13331 / 13421 |
| 0 | 4 (f5223fdd) | 8/8 | 16/16 | 16/16 | >= 8046 | 13245 / 13307 |
| 0 | 5 (b4b07f06) | 8/8 | 16/16 | 16/16 | >= 8359 | 13510 / 13454 |
Draws are your K from 2101; preload columns are formal's draws with the oracle from the preloaded state. "Slack" =
carryslack.sh: the largest extra delay on the carry into bit 16 at which 4 preloaded draws (K 2101-2104) all stay right,
bisected to 50 ps: a consequence slack (an upper bound of the settle margin). "Period" = median per-iteration time of
umux0's request OR over a 271-iteration preloaded call, draws 2101 / 2102 (formal's simx time scale, not your P).
- **Reading.** Every preloaded draw passes at every UADDI0 down to 0, and the 30-bit carry keeps >= 8.0 ns with UADDI0 = 0.
  i + 1 goes to the loop steer ucond_br6, whose join also waits for ucmpi1 (i < n - 1, UCMPI1 = 5, its own 32-bit chain);
  nothing captures i + 1 until the next iteration, ~14 ns later. Same 4 seeds, UADDI0 12 -> 0 (each a different route,
  since the netlist changes): period mean 14.28 -> 13.58 ns (-4.9 %; per seed 21 / 2 / 4 / 5: -0.13 / -0.72 / -1.35 /
  -0.60 ns), xor19 last answer 26.95 -> 25.55 us (-5.2 %). Reading (an inference, not traced): at that join UADDI0's 12
  units outlast UCMPI1's 5, so the incrementer's matched delay sits on the critical cycle of most routes while buying
  nothing a draw can see, even at its worst carry. Four routes a side are a sample; your P on the same routes decides.
- **For the sizing rule (formal PROGRAM, "Research's first lead"):** the part of the static rule this exposes is that it
  sizes an operator's delay for its own worst carry, as if its result were captured when its request arrives. Here the
  result is joined with a sibling (the compare) and then held by transparent latches for a whole iteration; the static
  size pays for a capture that does not happen. Formal has not checked how general this is beyond the counters below.
- **collatz, item 31** (nl6s3a, seed 20, sdf 7aefc4bd = yours): col18 4/4; full-range 32-bit n (0x15555555, i.e. 3n + 1 =
  2^30, and five more peaking to 0x746c9680, all below 2^31) 8/8; steps preloaded at 0x3ffffff0 on those + col18 (n = 1
  excluded: the hardware answers it from a constant) 8/8. Steps carry into bit 16, the carry in the LAST increment (n =
  0x10000: steps ends at exactly 0x40000000): >= 10546 ps. 3n + 1's carry into bit 28: >= 9765 ps.
- **collatz x0.70 seed 27** (your cand4 route; sdf f11ff1ee here): col18 4/4, full-range 16/16, steps preloaded 16/16;
  steps last-increment carry >= 8007 ps (UADDI1 7); 3n + 1 into bit 28 >= 8320 ps. So x0.70's UADDI1 7 is safe for the
  steps counter's full range on this route.
- **collatz64, item 32** (h4s3p, seed 22, sdf 842dd4d7 = yours): its kernel boundary in the decoded net takes all 64 bits
  (the bench's high-word mask is outside the kernel), so 63-bit values are ordinary inputs here: n = 0x1555555555555555
  (3n + 1 = 2^62, a 62-bit carry), 0x0555555555555555, and four odd 62-bit n peaking in [2^62, 2^63) without overflow:
  8/8. Your c6419 already reaches bit 48 (+20 ns on the 3n + 1 carry into bit 48 fails it). The carry into bit 56 keeps
  >= 16484 ps on these vectors. Steps preloaded: 8/8; last-increment carry into bit 16 >= 14609 ps.
- **Which long paths by what:** xorshift: incrementer carries > 12 bits by preload only; compare ripple, entry compare and
  n - 1 at full width by inputs (they are inputs at the kernel boundary). collatz / collatz64: 3n + 1 at full width by
  inputs outside the bench's mask; the steps counter's carries > ~10 bits by preload only. Not reached by anything here:
  none known for these three kernels; ipow's (e > 0 loop, r * b) were not looked at.
- Reproduce: `formal/tools-B/preload/prun.sh BASE OUT I0 LINK "PAIRS" N SEED0` on a margin/run.sh decode dir (KERNEL=,
  TMAX=), `carryslack.sh` for the slack; commands per row in formal/JOURNAL-B.md (2026-11-17).

## C45. Your two x0.55 disagreement candidates, draw for draw (shard C, 2026-11-17 20:45 UTC, updated 20:55; untrusted simulation)
Built here with your flows (shrink8 / shrink9 sizes, nextpnr 9c732bc6303458df): ipow x0.55 seed 12 (sdf c3542c6d), collatz
x0.55 seed 30 (sdf 9d3f9fea) -- please confirm these md5s are your routes. Formal's simx on the decoded bits, your draw K:
| build | draw | yours | formal |
|---|---|---|---|
| collatz x0.55 r30 | 3001 (CARRY 0.91) | FAIL | FAIL (wrong counts) |
| | 3002 (0.59) | PASS | PASS |
| | 3003 (0.75) | FAIL | FAIL |
| | 3004 (0.55) | PASS | **FAIL** |
| ipow x0.55 r12 | 1201 | hang | **PASS** (17/17, last answer 4.15 us) |
| | 1202 | PASS | PASS |
| | 1203 (CARRY 0.20) | hang | **PASS** |
| | 1204 | hang | **PASS** |
- **collatz route 30, the race:** the loop-entry steer again (ucmpi0.uz_n4 -> ucond_br2/3/4), steercorners.sh: 28 ps with 12
  runts at chains 0.20 / rest 0.31 / CARRY 0.20, 24 ps / 14 runts at CARRY 0.6, 104 ps / 14 runts at 1.0, and the uniform
  runs at those three corners return WRONG answers -- in formal this route fails without any slow carry; the trigger is fast
  chains against a slower rest. Your gate absorbs some of those runts (resolver), which would explain 3004. ucmpi2 keeps
  >= 1.4 ns. With UCMPI0 at 8 (C43's recipe; a different route, sdf 2a0586e4) seed 30 passes 8/8 draws (3001-3008).
- **ipow route 12:** formal does not reproduce your hangs. Not the DSP delay (formal with nextpnr's DSP SDF arcs: same 4/4
  PASS; +10 ns on every DSP arc still passes on route 5). Known difference that produced hangs before (C17): your GLS
  starts every LUT state node at X. **Your own gate passes too:** research/tools/eventgraph/bench_gate.sh at origin/claude/
  research 20:3x UTC, run here on this build (HW = the build dir of sdf c3542c6d; XRAY_DB pointed at the toolchain's
  prjxray-db/zynq7), ipow17: draw:1203 `PASS 17/17 cycles 1030 VERDICT: EQUIVALENT`, the same with GATE_PLUSARGS=
  +META_INIT=0, draw:1201 `PASS 17/17 cycles 998`, draw:1204 `PASS 17/17 cycles 1062` (each ~380 s on one core here; the
  draw file reads chains 0.2187 rest 0.2370 carry 0.2025 = yours). So the hangs are not in your model on this route as
  built here. Either your shrink8 route 12 is a different bitstream (please compare its sdf md5 with c3542c6d), or the
  farm runs ended for another reason (shrink8's run() records "TIMEOUT/none" when `timeout 100m` fires: is "hang" a
  timeout?). Logs: /home/user/runs/rg12_* in formal's sandbox (not committed; the command is above).

## C44. ipow x0.55's per-iteration loop test: UCMPI2 10 -> 13 lifts the slow-CARRY margin from 166-398 ps to >= 2.1 ns, but costs ~5-9 % end to end; choosing the route is cheaper (shard C, 2026-11-17 20:20 UTC; untrusted simulation)
Your ipow x0.55 sizes with only UCMPI2 = 13 (unshrunk 18), seeds 1 / 4 / 11 (sdf b072ad55 / 9fe3a5a0 / 405ab163), ipow17,
steercorners.sh at chains 0.20, CARRY 1.0, rest 0.31 / 0.20:
| seed | x0.55: ucmpi2 worst (C40) | UCMPI2 13: ucmpi2 worst | ucmpi0 worst | draws | last answer mean, x0.55 -> UCMPI2 13 |
|---|---|---|---|---|---|
| 1 | 357 | 2368 | 1515 | 8/8 | 4.22 -> 4.60 us |
| 4 | 398 | 2451 | 1398 | 8/8 | 4.39 -> 4.65 us |
| 11 | **166** | 2095 | 997 | 8/8 | 4.25 -> 4.60 us |
- ucmpi2 is per iteration, so this one is paid in speed (+6-9 % of ipow17's total; per-iteration figure not measured).
  Three steps were more than needed; 11 or 12 would likely do, untested. Alternatively keep x0.55 and take a route whose
  ucmpi2 margin is large (3, 5, 8: >= 789 ps at all 8 corners).

## C43. Collatz x0.55: the same recipe -- keep the per-call entry compare UCMPI0 at its unshrunk 8 (x0.55 has 5) -- lifts routes 4 / 8 from 6-52 ps with runts to >= 691 ps at all 8 corners (shard C, 2026-11-17 20:15 UTC; untrusted simulation)
Your nl6s3a_x55 + pre_eq2, col18, built here; steercorners.sh (C36's method, 8 corners, no scatter); ucmpi0.uz_n4 -> entry
steers ucond_br2/3/4, ucmpi2.uz_n36 (the n == 2 loop test) -> ucond_br5/6:
| build | route (sdf) | ucmpi0 worst / best, ps | runts | ucmpi2 worst | draws (K 100r+1..8) | last answer mean |
|---|---|---|---|---|---|---|
| x0.55 | 4 (bc2b7d14) | **22** (0.20/0.20/1.0) / 402 | 2 at 0.20/0.31/1.0 | 1006 | 8/8 | 23.98 us |
| x0.55 | 8 (55cd1694) | **6** (0.20/0.31/0.20) / 451 | 3 at 0.20/0.31/0.20, 6 at 0.20/0.31/1.0 | 578 | 8/8 | 23.68 us |
| x0.55, UCMPI0 8 | 4 (40d5ea59) | 1172 / 1697 | 0 | 1476 | 8/8 | 25.69 us |
| x0.55, UCMPI0 8 | 8 (fa596415) | 691 / 1369 | 0 | 1392 | 8/8 | 21.99 us |
(x0.55 routes 20 / 3, C37: 681 / 583 ps worst, no runts.) Every corner run returned all 17 right answers.
- On route 8 the knife edge is there with CARRY/F7 at its FAST end (6 ps, 3 runts at chains 0.20 / rest 0.31 / CARRY 0.20):
  this race is not only a CARRY-band question; fast chains against a slower rest close it.
- Cost: the restored UCMPI0 is per call; last answers moved +7 % (route 4) and -7 % (route 8), i.e. inside route scatter.
- **Recommendation for both shrink leads:** shrink the per-iteration delays, keep the loop-ENTRY compares (UCMPI0 here,
  UCMPI0 in xorshift C41) at their unshrunk sizes. With that, the remaining slow-CARRY exposure is the per-iteration loop
  test (ucmpi1 in xorshift, ucmpi2 in ipow: 166 ps on ipow route 11, C40), which is where route choice still matters.

## C42. With A13 (CARRY/F7 not pinned by any August loop time), the "redraw at the fitted CARRY/F7 band" step cannot narrow it: take C41's fix instead of waiting for the fit (shard C, 2026-11-17 19:50 UTC)
- A13 (shard A, 18:28): on the August board bitstreams, moving the CARRY/F7 band over {0.2, 0.39, 1.0} changes collatz /
  collatz64 per-iteration time by 0.00 ns -- in bundled data the cycle is set by matched delays (LUT chains), and the carry
  chains only have to settle inside them. So board LATENCIES can never place CARRY/F7; only a carry-chain-specific board
  measurement (a CARRY4 ring or delay line) could.
- The races that depend on that band are exactly the ones that decide item 35 (C36 / C38: ucmpi0 -> ucond_br2 goes from 408
  ps at CARRY 0.2 to 0 near 0.9). So the fit will leave item 35's weakest race where it is: anywhere in [0.2, 1.0].
- C41 removes the dependence at no speed cost: UCMPI0 = 10 keeps >= 916 ps (entry) and >= 387 ps (loop test) at CARRY 1.0 on
  8 routes. Recommendation: rebuild item 35 with UCMPI0 = 10 and pick the route by ucmpi1's slow-CARRY margin; the collatz
  (C37, >= 583 ps) and ipow (C40, >= 789 ps) x0.55 leads already keep their margin at CARRY 1.0.
- For A's fit: ipow's August bitstream can now be decoded too (C39's DSP48E1 path; run.sh picks it when the FASM has DSP
  config lines).

## C41. A near-free fix for item 35's weak race: UCMPI0 back to 10 (item 33's size) keeps >= 387 ps at CARRY/F7 1.0 on 3 routes, at no measurable cost; 8 is not enough (shard C, 2026-11-17 19:25 UTC; untrusted simulation)
ucmpi0 is the loop-ENTRY compare (once per call), so its matched delay is paid per call, not per iteration. Item 35's sizes
(fr4a_x55a) with only BD_SZ_..._UCMPI0 changed (6 -> 8, 6 -> 10), built here on seeds 21 / 2 / 4 (sizes files:
x55a with that one line edited; the netlist change reroutes, so each is a new route). steermargin.py at chains 0.20 / rest
0.31 (C36's worst corner), xor19 + xorlong; smallest settle gap, ps (runts = requests under which the condition moved):
| UCMPI0 | route | ucmpi0 -> entry steers, CARRY 0.2 / 0.6 / 1.0 | ucmpi1 -> loop steers, CARRY 0.2 / 0.6 / 1.0 |
|---|---|---|---|
| 6 (item 35) | 21 | 408 / 194 / **12, 10 runts** | 620 / 604 / 321 (C36) |
| 6 | 2 / 4 | C36: 114 / 124 at 1.0 | C36: **114, 2 runts** (route 2) / 622 |
| 8 | 21 (sdf c50cea4f) | 951 / 693 / 436 | 431 / 160 / **19, 6 runts** |
| 8 | 2 (c48e1518) | 730 / 523 / 289 | 1241 / 675 / 414 |
| 8 | 4 (4bfc5a87) | 1262 / 1016 / 771 | 1345 / 1083 / 822 |
| 10 | 21 (42b4fb4c) | 1424 / 1170 / 916 | 917 / 646 / 387 |
| 10 | 2 (f1da196a) | 1592 / 1370 / 1134 | 1026 / 1026 / 1026 |
| 10 | 4 (05a84ea0) | 1504 / 1275 / 1047 | 1337 / 1317 / 1046 |
Every run returned all right answers. Draws (your model, xor19, K 100r+1..8): 8/8 PASS on all six builds.
- **UCMPI0 10 on 5 more routes** (19:45; seeds 1 / 3 / 5 / 6 / 7, sdf 8f165305 / 9a68cb56 / b073c245 / d7201a17 / dca58e5f), CARRY
  1.0 corner: ucmpi0 2080 / 2250 / 1297 / 1700 / 1477 ps, ucmpi1 1202 / 1283 / 742 / 765 / 1701 ps, 0 runts; draws 8/8 each;
  last answer 25.97-27.44 us. Over 8 routes the worst is route 21's ucmpi1, 387 ps.
- **Cost:** last answer on xor19, same 8 draws on seed 21: item 35 mean 26.98 us, UCMPI0 8 26.55 us, UCMPI0 10 26.76 us;
  seeds 2 / 4 at 10: 26.57 / 26.32 us. No cost visible above route scatter, as expected for a per-call delay.
- **But the loop test is the other half:** with UCMPI0 at 8 the new route 21 puts ucmpi1 -> ucond_br6 at 19 ps with 6 runts
  at CARRY 1.0 (UCMPI1 is 5 in every row), and item 35's route 2 already had it at 114 ps. ucmpi1 is per ITERATION, so
  lengthening it costs speed. With UCMPI0 10 its worst is 387 ps on these three routes; three routes are a sample.
- **Suggestion:** if item 35 goes to the board, take UCMPI0 = 10 (no speed cost) and choose the route by ucmpi1's margin at
  the slow-CARRY corner (formal can run steermargin on any route you name in under 10 minutes).

## C40. ipow x0.55 routes 3 / 5 / 8: 32/32 draws each; loop-steer settle margins >= 789 ps at all 8 corners, no runts (shard C, 2026-11-17 18:10 UTC; untrusted simulation)
Same builds as C39 (md5-identical to yours), ipow17 (reaches e = 0x7fffffff), formal's simx with the DSP48E1 decode.
- **Draws (your model, K = 100r+1..32):** route 3 32/32 (last answer 4.33-4.81 us), route 5 32/32 (4.11-4.64 us), route 8
  32/32 (4.35-5.01 us). Wilson lower bound 0.893 per route.
- **Settle margins** (steermargin.py, 8 corners as C36/C37; ps; 0 runts everywhere; all answers right at every corner):
| route | ucmpi0 (e > 0 entry) -> steers, worst / best | ucmpi2 (loop test) -> steers, worst / best |
|---|---|---|
| 3 | 1131 (ucond_br4) / 1828 | **789** (ucond_br8; chains 0.20 / rest 0.31 / CARRY 1.0) / 1593 |
| 5 | 1378 (ucond_br5) / 2321 | 1350 (ucond_br9) / 2239 |
| 8 | 1493 (ucond_br5) / 2066 | 2135 (ucond_br8) / 2952 |
- **8 more routes (20:00; seeds 1 2 4 6 7 9 10 11, sdf f0ea1d9f 65fe87c1 fa33c8ae 2064e904 8adfc041 e47afcf8 8ae050c7
  bc8ddf0f):** draws K 100r+1..8: 64/64 PASS (last answer 3.99-4.88 us). Slow-CARRY corner only (chains 0.20 / rest 0.31 /
  CARRY 1.0), ucmpi0 / ucmpi2 settle margins: 891/357, 1387/1468, 1074/398, 1300/1509, 453/1499, 695/516, 1176/1320, **617/166**
  ps; no runts. So over 11 routes ipow x0.55's loop test (ucmpi2 -> ucond_br6) goes down to **166 ps on route 11** (357 / 398 on
  routes 1 / 4): like collatz x0.55, the shrink is route-sensitive at the slow-CARRY end, and the board route should be
  chosen by this margin (3, 5, 8 keep >= 789 ps at all 8 corners).
- **Item 29 itself (the ipow board candidate, h4s3m, seed 19, sdf b521630f = yours; first time formal could run it):**
  K 1901-1932 32/32 PASS (last answer 5.52-6.19 us); settle margins ucmpi0 -> ucond_br4 3054-3951 ps, ucmpi2 -> ucond_br7
  4605-5894 ps over the 8 corners, no runts. So x0.55 spends ~2-3.8 ns of these races' margin (worst 789 ps on route 3).
- **Reading:** on these races ipow x0.55 keeps 0.8-1.5 ns at the worst corner of your box, more than collatz x0.55 (C37,
  >= 583) and far more than item 35 (C36/C38, ~0 at slow CARRY). The worst corner is again CARRY/F7 slow with fast chains.
  Not covered here: the select race at ipow's muxes (shard B's class) and the DSP's internal glitches (one arc per input
  group; prjxray's DSP arcs are faster than nextpnr's SDF, C39).

## C39. ipow in formal's simulator (DSP48E1 now decoded); your route-19 failure IS the F7-select bit: wrong at every corner as built, right with that one select set to the netlist's 0 (shard C, 2026-11-17 18:05 UTC; untrusted simulation)
- **New:** the margin tool now decodes DSP48E1 sites from the bits (formal/tools/margin/dsp/: wraps A's decoder, every
  register must be off, OPMODE/ALUMODE/INMODE/CARRYIN decoded from tie-offs and inverter bits, anything else refused;
  checked against routed.json on 4 routes and against x*y mod 2^32 on 2007 operand pairs per multiply, 0 mismatches).
  Delay: prjxray's DSP_{L,R} timing (A->P 0.9-3.8 ns), which is FASTER than nextpnr's SDF (A->P 5.4 ns, what your GLS
  uses); `DSP_SDF=` widens to it. On route 5 draws 501/502 the answers and their times are identical either way, and +10 ns
  on every P arc still passes (+20 ns fails): the multiply is not ipow's binding path on that draw.
- **Your ipow x0.55 routes, built here md5-identical** (seeds 3 / 5 / 8 / 19, sdf 0b333646 / e7c5057d / 70048ae0 /
  d63bfd80), ipow17, your draws: route 3 (301/302), 5 (501/502), 8 (801/802) PASS 2/2 each: no disagreement. 32 draws
  each and the loop-steer margins at 8 corners are running (next item).
- **Route 19 (your 11:51 attribution, which the audit marked UNVERIFIED):** formal's decode of the bits gives SLICE_X19Y65's
  F7AMUX select = constant 1 (AX has no active pip; the walker reaches VCC through prjxray's default BYP_ALT0 path), while
  the netlist cell (ushrsi0 mux7, the e >> 1 shifter) has S0 = GND. As built: your draws 1901/1902 FAIL, all FAST_MIN FAIL,
  all SLOW_MAX FAIL, the same 11/17 every time; each wrong answer is the right answer for e >> 4 (the shifter ends the loop
  early) -- a logic defect, not timing. With that one select forced to 0 in the decoded net (force_pin.py): 1901/1902
  PASS, FAST_MIN PASS, SLOW_MAX PASS. So the failure is the F7-select defect and nothing else that formal can see.

## C38. Item 35's weakest race against the CARRY/F7 band alone: the settle margin falls ~55-65 ps per 0.1 of band and reaches 0 at CARRY/F7 ~ 0.9 (shard C, 2026-11-17 17:55 UTC; untrusted simulation; for PROGRAM "First: where does the board sit")
For your fit of the LUT/routing band and the CARRY/F7 band as two numbers: what the second number does to item 35.
Board route 21 rebuilt here (sdf 9145cd49 = yours), vectors xor19 + formal/tools/margin/vec/xorlong.hex (rounds to 4095),
steermargin.py (C36's method: uniform bands, no scatter), chains at 0.20, CARRY4/F7/F8 band swept 0.2..1.0. Smallest
settle gap of the loop-entry condition (ucmpi0.uz_n3) before ucond_br2's request, and of the loop test (ucmpi1.uz_n41)
before ucond_br6/7, ps; runts = requests under which the condition moved:
| CARRY/F7 band | 0.2 | 0.3 | 0.4 | 0.5 | 0.6 | 0.7 | 0.8 | 0.9 | 1.0 |
|---|---|---|---|---|---|---|---|---|---|
| ucmpi0 -> ucond_br2, rest 0.31 | 408 | 354 | 301 | 247 | 194 | 137 | 72 | **8** | **12, 10 runts** |
| ucmpi0 -> ucond_br2, rest 0.20 | 490 | 436 | 383 | 329 | 271 | 207 | 142 | 78 | **14** |
| ucmpi1 -> ucond_br6/7, rest 0.31 | 620 | 620 | 620 | 620 | 604 | 539 | 473 | 408 | (C36: 321+) |
| ucmpi1 -> ucond_br6/7, rest 0.20 | 683 | 683 | 683 | 683 | 643 | 578 | 513 | 382 | 317 |
Every run returned all right answers (runts absorbed in formal's simulator, as in C36).
- **Reading:** the margin is nearly linear in the CARRY/F7 band: ~-55 ps per 0.1 (rest 0.31), zero near 0.9. If your fit
  puts CARRY/F7 where the August kernels put everything (0.22), item 35 keeps ~0.4-0.5 ns here (~2-3 median SDF errors of a
  ~2 ns path); at 0.5 about 0.25-0.33 ns; above ~0.85 it lives on absorbed runts. So the fit needs to bound CARRY/F7 below
  ~0.6 for this race to keep one median error of margin.
- **Identifiability note:** in this race the chains and the rest are at fixed bands; the CARRY band alone moves it. If the
  August kernels' per-iteration times depend on CARRY/F7 only weakly (their carry chains are a small part of an iteration),
  the board timings will pin the CARRY/F7 band loosely; a kernel whose loop is carry-dominated (collatz's 3n+1 select, the
  compares) is what pins it.
- Collatz x0.55 (C37, routes 20 / 3) moves by ~170 ps between CARRY 0.20 and 1.0 and keeps >= 583 ps at the worst corner.

## C37. Collatz x0.55 on your two EQUIVALENT routes (20, 3), col18: 64/64 draws each, loop-steer settle margins >= 583 ps at all 8 corners, no runts (shard C, 2026-11-17 17:25 UTC; untrusted simulation)
Built here, md5-identical to yours: nl6s3a_x55 + pre_eq2, seed 20 (sdf b2b0dad9), seed 3 (sdf d8884e45); nextpnr
9c732bc6303458df. Vectors: your col18 (inside the bench's 16-bit mask, peaks to 30 bits).
- **Draws (your model, formal's simx on the decoded bitstream):** route 20 K 2001-2064 64/64 PASS (Wilson 0.943-1.000),
  last answer 23.8-27.2 us; route 3 K 301-364 64/64 PASS, 22.7-26.0 us. Your 2001/2002 and 301/302 are among them: no
  disagreement.
- **Settle margins** (steermargin.py, C36's method: uniform bands, no scatter; all 8 corners of your box, chains / rest in
  {0.20, 0.31}, CARRY/F7 in {0.20, 1.0}); smallest gap of the condition before a request, ps; 0 runts everywhere; every
  corner returns all 17 right answers:
| route | ucmpi0 -> entry steers (ucond_br2/4), worst corner | best corner | ucmpi2 (n == 2 exit) -> ucond_br6, worst | best |
|---|---|---|---|---|
| 20 | **681** (ucond_br2; chains 0.20 / rest 0.31 / CARRY 1.0) | 1138 | 712 (same corner) | 1375 |
| 3 | **583** (ucond_br4; same corner) | 1073 | 1144 | 1771 |
- **Reading:** the 18-24 ps knife edge of C35 (x0.55 routes 4 and 8, one corner, col17) does not occur on the two routes
  you would take to the board: their worst corner keeps ~0.6-0.7 ns, about 3-4 median SDF errors (8.5 %) of a ~2 ns
  path, and below the August long-route error (~1 ns slow) only if the condition's path is that long. As with item 35
  (C36), the worst corner is CARRY/F7 at the slow end (1.0) with fast chains; the margin moves ~170 ps between CARRY 0.20
  and 1.0. Route choice matters for this shrink: pick 20 or 3, not 4 or 8.
- Files: the commands are in formal/JOURNAL-C.md (progress 17:25); the scripts are the margin tool's (draws.py via run.sh
  DRAWS=64 DRAW_MODEL=research, steermargin.py).

## C36. Item 35 (board route 21) at your model's slow-carry corners: its loop-entry steer runs with LIVE RUNTS -- the condition moves under the request on 5 of 23 calls; answers still right (shard C, 2026-11-17 11:20 UTC; untrusted simulation)
Redo of C33 / C34 after the audit's T143: all 8 corners of your box (chains, rest in {0.20, 0.31}, CARRY/F7 in {0.20, 1.0}),
vectors xor19 + formal/tools/margin/vec/xorlong.hex (rounds 4095, 4094, 2048, 2047), steermargin.py, uniform bands, no
scatter. Smallest settle margin of the condition before the request at the loop steers (ps), and runts = requests under
which the condition moved:
| route | ucmpi0 -> ucond_br2, worst corner | ucmpi1 -> ucond_br6/7, worst corner | all 8 corners: right answers? |
|---|---|---|---|
| 21 (board, 9145cd49) | **15 ps, 5 runts** at chains 0.20 / rest 0.31 / CARRY 1.0; 17 ps at 0.20 / 0.20 / 1.0 | 321 ps (0.20 / 0.20 / 1.0) | yes, all 8 |
| 4 (ee6304d0) | 124 ps (0.20 / 0.31 / 1.0) | 622 ps | yes |
| 2 (b2470514) | 114 ps (0.20 / 0.31 / 1.0) | **114 ps, 2 runts** (0.20 / 0.31 / 1.0) | yes |
With CARRY/F7 at 0.20, every route keeps >= 245 ps; the edge is the slow end of the CARRY/F7 band you have never measured.
- **Where (route 21):** the tight calls are at 4.37 us, 25.35 us and 27.23 us (gaps 15, 24, 57 ps), xor19 calls, not only
  the long rounds. ucmpi0 is the loop-entry test (per call), so these are calls whose entry compare ripples through the
  carry chain late.
- **Consequence:** the run still gives every right answer, and only fails when ucmpi0's condition is delayed a further
  1.03-1.13 ns at those corners (sideslack). The steer's runts are absorbed downstream in formal's simulator (transport
  LUTs with the 20 ps filter), as in your gate's resolver model and the audit's T136. Whether silicon absorbs a runt at a
  steer is exactly the open runt question (C19 / your BOARD-QUEUE item 2).
- **Reading:** at the slow-carry end of your model, item 35's board route works by absorbing steer runts, with no settle
  margin at all. The audit's T143 (140 ps at advA on long rounds) points the same way; formal's number is lower. If the
  board shows item 35 failing, this race is the first place to look; the fix is ucmpi0's matched delay (UCMPI0, item 33's
  size keeps 1.48 ns, C34).

## C33 / C34 / C35 correction (shard C, 2026-11-17 10:05 UTC): the margins are minima over ONE corner and short vectors -- OVERSTATED (audit T143)
The audit (T143, interim) reproduces formal's figure at formal's corner (ucond_br2 400 ps vs formal 321 ps at ucond_br7) but
finds lower inside the same model: advA (chains 0.20, rest 0.31, CARRY 1.0) puts item 35's ucmpi0 -> ucond_br2 at 264 ps
on xorshift_17 and 140 ps on rounds up to 4095. A slow "rest" delays the compare's condition more than the request, and
long round counts reach states xor19 does not. So "321-614 ps at the model's slow-carry corner" is not the model's minimum;
read C33-C35's numbers as upper bounds. Being redone over all 8 corners of your box (chains, rest in {0.20, 0.31}, CARRY/F7
in {0.20, 1.0}) with long-round vectors (formal/tools/margin/vec/xorlong.hex: rounds 4095, 4094, 2048, 2047).

## C35. Collatz x0.55 (every size): on 2 of 8 routes the loop-entry steer's condition settles only 18-24 ps before its request at your model's slowest-carry corner (shard C, 2026-11-17 10:05 UTC; untrusted simulation)
Your x55 sizes, routes 1-8, col17 (C29: 16/16 draws on each), steermargin.py on ucmpi0.uz_n4 -> ucond_br2/3/4 (C33's
method). Smallest settle margin per route (ps; no request ever has the condition move under it):
| route | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|
| all FAST_MIN | 724 | 577 | 559 | 134 | 300 | 820 | 422 | 192 |
| rest 0.20, CARRY/F7 1.0 | 841 | 614 | 658 | **24** | 216 | 946 | 451 | **18** |
- **Where:** the tight request is the zero-trip call n = 1 (route 8: ucond_br2 at 1.8927 us, ucond_br3 64 ps; route 4:
  ucond_br3 at 1.9093 us). That call's input was driven at ~0.42 us and was stable since, so the late condition is inside
  the kernel: the compare ucmpi0 on the value the loop header has just passed, against the steer's request through
  ucmpi0's matched delay -- the same race that fails x0.50 on routes 2 and 6 (C29). The next-smallest request on those
  routes has >= 397 ps.
- **Consequence:** adding delay to ucmpi0's last LUT, the run first fails at +218-234 ps (route 8) and +562-577 ps (route 4)
  at that corner (+327 / +515 ps at FAST_MIN): the steer tolerates a little lateness, but 18 ps of settle margin is far
  inside one median SDF error. Your draws pass there because CARRY/F7 at 1.0 with the rest at 0.20 is the edge of the box.
- **Reading:** collatz x0.55 is not uniformly one step above the edge: on routes 4 and 8 its loop-entry steer is on a
  knife edge at the slow-carry corner. If x0.55 goes to the board, pick a route by this margin (routes 1, 3, 6 have > 550
  ps at both corners), or keep UCMPI0 at its x0.70 size.
- The current board candidates on the same race (unshrunk sizes): item 31 (route 20, ucmpi0 -> ucond_br2/3/4) 1506 ps at
  FAST_MIN, 1970 ps at the slow-carry corner, 4676 ps at SLOW_MAX; item 32 (route 22, ucmpi2 -> ucond_br6) 2928 / 3806 /
  9001 ps. So the knife edge appears only with the x0.55 shrink.
- For comparison, collatz64 x0.55 (C31), ucmpi2 -> ucond_br6, routes 1-4: FAST_MIN 1338 / 818 / 1023 / 610 ps, slow-carry
  corner 1498 / 806 / 1029 / 454 ps: no knife edge on those four routes.

## C34. Item 35's sizes (fr4a_x55a) on 5 routes: loop-steer settle margins 166-341 ps at your model's slowest-carry corner (shard C, 2026-11-17 09:45 UTC; untrusted simulation)
Built here (nextpnr 9c732bc6303458df), xor19, steermargin.py (C33's method; no row has the condition moving under a request).
Draws: your K = 100r+1..8 on routes 1-4 all PASS (8/8 each); route 21 = C28. Smallest settle margin per route:
| route (sdf) | ucmpi1 steers, FAST_MIN | ucmpi1 steers, rest 0.20 + CARRY/F7 1.0 | ucmpi0 steers, FAST_MIN | ucmpi0 steers, rest 0.20 + CARRY/F7 1.0 |
|---|---|---|---|---|
| 21 (9145cd49, board) | 484 (br6) | 321 (br7) | 363 (br2) | |
| 1 (33852d52) | 601 (br9) | 341 (br9) | 674 (br2) | 394 (br2) |
| 2 (b2470514) | 272 (br6) | 323 (br6) | 541 (br2) | **181 (br2)** |
| 3 (7b649492) | 501 (br9) | 230 (br9) | 519 (br5) | 283 (br5) |
| 4 (ee6304d0) | 820 (br7) | 622 (br7) | 497 (br2) | **166 (br2)** |
- The race: the loop compares' outputs (ucmpi0.uz_n3, ucmpi1.uz_n41) against the requests of the steers they feed
  (ucond_br2/5 from ucmpi0, br6-9 from ucmpi1), both from the steer's join. Positive on every route at both corners.
- Scaled by the measured error: 166 ps is about one median SDF error (8.5 %) of a ~2 ns path, so on routes 2 and 4 at
  the slow-carry end this race has roughly one median error of margin, and less than the August data's long-route error
  (~1 ns slow). Your rule E rows for ucond_br2 on these routes would be the number to set beside this.
- Against item 33 (unshrunk fr4a, route 27, sdf 7f0c0592, built here; 8/8 draws): ucmpi0 steers 1480 ps (FAST_MIN) / 1527 ps
  (slow-carry), ucmpi1 steers 2075 / 2767 ps. So x0.55a spent ~1.2 ns of this race's margin (1.48 -> 0.32-0.36 ns on the
  board routes) to save ~2 ns per iteration (C28 / your shrink5).
- These are uniform-band margins on one draw each (no per-pip scatter). The board route (21) is not the tightest.
- Route 4 (the tightest) with 256 draws of your model (draws 1-256, per-pip scatter included): 256/256 PASS (Wilson lower
  bound 0.985). So the 166 ps margin does not turn into failures inside your model; it is the model's error that would.

## C33. Settle margins at the loop steers, in ps, for item 35 and the x0.55 shrinks (shard C, 2026-11-17 09:35 UTC; untrusted simulation)
steermargin.py: every LUT that reads the compare's output; per request rise, the time since the condition last arrived
at that LUT pin (arrival = source flip + copy and pin arcs at the corner; no scatter). Smallest over the whole vector set;
"runts" = requests under which the condition moved (0 in every row). Agrees with the audit's T139 on item 35's ucond_br2
(363 ps at FAST_MIN vs 264-485 ps).
| build (route, vectors) | condition -> binding steer | all FAST_MIN | rest 0.25, CARRY/F7 1.0 | rest 0.20, CARRY/F7 1.0 | all SLOW_MAX |
|---|---|---|---|---|---|
| item 35 (21, xor19) | ucmpi1 -> ucond_br7 | 600 ps | 419 ps | **321 ps** | 1830 ps |
| item 35 | ucmpi1 -> ucond_br6 | 484 ps | 739 ps | 685 ps | 1501 ps |
| item 35 | ucmpi0 -> ucond_br2 | 363 ps | | | |
| collatz x0.55 (2, col17) | ucmpi0 -> ucond_br2 | 577 ps | 672 ps | 614 ps | 1590 ps |
| collatz x0.55 (6, col17) | ucmpi0 -> ucond_br4 | 820 ps | | | 2282 ps |
| collatz64 x0.55 (4, c6418) | ucmpi2 -> ucond_br6 | 610 ps | 520 ps | **454 ps** | 1497 ps |
| collatz64 x0.55 (1, c6418) | ucmpi2 -> ucond_br6 | 1338 ps | | | 3914 ps |
(The 321 ps on item 35's ucond_br7 is one request of 1839; the next smallest is 923 ps.) Read these, not the C29 / C31 /
C32 sideslack numbers, as the margins: sideslack measures how late until a WRONG answer, which includes runts the model
absorbs. All rows are one route each, uniform bands; the per-pip scatter of your model (sigma 0.126 per pip) is not in them.

## C32. (note on C29 / C31 / C32 slack numbers) sideslack.py's numbers are CONSEQUENCE slacks (how much later until a wrong
answer); the settle margin at the steer (condition settled before the request) can be smaller, as on item 35's ucond_br2
(0.36 vs 1.08 ns). Read them as upper bounds of the settle margin.

## C32. Item 35's two loop compares, slack in ps in formal's simx (shard C, 2026-11-17 09:20 UTC; untrusted simulation)
Route 21 (sdf 9145cd49), xor19, sideslack.py: extra delay on every input arc of the compare's last LUT (its condition comes
later), uniform bands, no scatter, bisected to 16 ps; first failing extra:
| compare (last LUT) | all FAST_MIN | rest 0.25, CARRY/F7 0.6 | rest 0.25, CARRY/F7 1.0 | all SLOW_MAX |
|---|---|---|---|---|
| ucmpi1 (uz_n41, the loop test) | 0.61 ns | 0.69 ns | **0.42 ns** | 1.86 ns |
| ucmpi0 (uz_n3) | 1.08 ns | 1.42 ns | 1.17 ns | 3.20 ns |
- The tightest: ucmpi1's condition may come 0.42 ns later at the slowest CARRY band your model allows. That is the race
  xorshift's x0.40a / x0.50a failures were on (C24 / C25); at x0.55a it keeps 0.4-0.7 ns at the model's bands.
- **Against the audit's T139** (ucond_br2, fed by ucmpi0: 264-485 ps at the fast corners). Traced (09:30): in formal's own
  all-FAST_MIN run, at ucond_br2's pins (request p2 from ucond_br2_j, condition p3 from ucmpi0.uz_n3; arrival = source flip +
  path FAST_MIN), the condition settles >= **363 ps** before each of the 19 requests (next: 392, 392, 397, 399 ps) and never
  moves while a request is high: **agrees with T139**. The consequence slack is larger (1.08 ns) because between +0.36 and
  +1.08 ns the condition moves under a live request -- a steer runt -- and the answers still come out right in formal's
  simulator (as the audit saw in T136). Per CLAUDE.md, the number to use is the settle margin, 0.36 ns at FAST_MIN; the
  1.08 ns says only that the runts formal's model produces in between are absorbed downstream.

## C31. Collatz64 below item 32's sizes in formal's simx: x0.55 24/24 on routes 1-4 (63-bit trajectories); x0.50 fails route 4 via ucmpi2 (the 64-bit n == 2 exit compare) (shard C, 2026-11-17 08:30 UTC; untrusted simulation)
Sizes made with your shrink_sizes.py from collatz64_sizes_T4cdb_h4s3p (x0.55: 21 sizes moved, x0.50: 29). c6418 (full 64-bit
n, peaks 63 bits), your model, draws 1-6, host 12 ns.
| sizes | route 1 | route 2 | route 3 | route 4 | last answer (c6418) |
|---|---|---|---|---|---|
| item 32 (h4s3p), route 22 | | | | | 98.0 us (C30, 8/8) |
| x0.55 | 6/0/0 | 6/0/0 | 6/0/0 | 6/0/0 | 64.9-69.9 us |
| x0.50 | 5/0/1 | 6/0/0 | 6/0/0 | **2/4/0** | 68.2-73.0 us |
(PASS / FAIL / UNDECIDED; sdf x0.55 d70a99da d3a30a8c 0415dd53 3c6d6f4f, x0.50 8c0229a0 c1011df9 e686e1a5 1801a64e.)
- x0.50 is no faster than x0.55 on these routes, and fails on route 4 (results stop after 3 or 5 answers).
- **The path (route 4, chainfix.py, +2000 ps on one of 57 chains at a time, no scatter):** with every non-carry arc at band
  0.25 and CARRY4/F7/F8 at 0.6 the run fails and only `ucmpi2.udly` fixes it; with every arc at SLOW_MAX the run hits the
  event cap and only `ucmpi2.udly` clears it; with every arc at FAST_MIN it passes. ucmpi2 is the exit test n == 2 on 64 bits,
  an equality yosys built from LUTs into F7/F8 wide muxes (8 mux8 trees, final LUT ucmpi2.uz_n38; corrected 08:50: not a
  CARRY4 chain); UCMPI2 = 16 (h4s3p), 9 (x0.55), 8 (x0.50). The compare's mux tree against its shortened matched delay,
  failing when the F7/F8 band (the same unmeasured U[0.2, 1.0] class as CARRY4) is slow: the same kind of race as
  xorshift's x0.40a (C24).
- **The same race's slack at x0.55, in ps** (sideslack.py: extra delay on every input arc of ucmpi2.uz_n38, the compare's
  last LUT, i.e. the condition arrives later; uniform bands, no scatter; bisected to 16 ps; the run must pass at 0):
  | route | rest 0.25, F7/F8/CARRY 0.6 | rest 0.25, F7/F8/CARRY 1.0 | all SLOW_MAX | all FAST_MIN |
  |---|---|---|---|---|
  | 4 | 0.69 ns | 0.53 ns | 1.47 ns | 0.63 ns |
  | 1 | 1.86 ns | 1.69 ns | 3.97 ns | 1.34 ns |
  Route 4 is the tight one; its slack stays positive across the model's band range, and is 0.53 ns at the slowest F7/F8
  the model allows. (An injection outside the prjxray band; it says how much later this side may come, not a probability.)
- **Reading:** x0.55 looks like the collatz64 candidate formal's simulator would pick (no failure on 4 routes, ~30 % less
  time than item 32 on the same vectors, though item 32's number is from route 22). Keep UCMPI2 >= 9 if shrinking further.
  On your c6419 (inside the bench's domain) x0.55 routes 1-4 pass 6/6 each too (last answer 74.9-80.6 us vs item 32's
  113 us on route 22, C30).

## C30. Collatz64 item 32 (seed 22, sdf 842dd4d7) on c6419 and on 63-bit trajectories: 8/8 each in formal's simx (shard C, 2026-11-17 07:50 UTC; untrusted simulation)
Your model, draws 1-8, host 12 ns. c6419: 8/8 PASS (last answer mean 113 us). c6418 (your deleted file: n ~ 2^59, peaks at
63 bits, outside the bench's domain, driven by formal as the full 64-bit n; oracle 267 / 282 / 285 = your c6418.exp): 8/8
PASS. So item 32's kernel handles carries to bit 62 on these draws; the board's bench cannot feed such n.

## C29. Collatz below x0.55 in formal's simx: x0.55 clean on routes 1-8 (col17); x0.50 fails routes 2 and 6 at every corner; the path is ucmpi0 -> ulink_n1__1 (shard C, 2026-11-17 07:45 UTC; untrusted simulation)
Sizes: your x55 file, and x0.50 / x0.45 made with your shrink_sizes.py from nl6s3a (it reproduces your x55 file exactly).
Routes 1-8, col17 (full 32-bit n, no bench mask), your model, your K = 100r+1..4 plus formal draws. PASS/FAIL/UNDECIDED:
| route | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|---|---|---|---|---|
| x0.55 (16 draws) | 16/0/0 | 16/0/0 | 16/0/0 | 16/0/0 | 16/0/0 | 16/0/0 | 16/0/0 | 16/0/0 |
| x0.50 (12) | 12/0/0 | **0/12/0** | 11/0/1 | **2/0/10** | 12/0/0 | **0/11/1** | 12/0/0 | 12/0/0 |
| x0.45 (12) | **0/11/1** | **7/5/0** | 12/0/0 | **9/3/0** | 12/0/0 | **8/4/0** | 12/0/0 | **9/1/2** |
- **The race (routes 2 and 6 at x0.50):** fails with every arc at FAST_MIN, at band 0.25 and at SLOW_MAX, no scatter:
  right after the zero-trip call n = 1 the next call answers 0 or never answers. Adding delay to one chain at a time
  (formal/tools/margin/chainfix.py, 57 chains): only `ucmpi0.udly` and `ulink_n1__1.rdly` fix it, always at the same
  threshold (one request path, in series). Shortfall: route 2 0.2-0.4 ns at FAST_MIN, 0.4-0.7 at band 0.25, 0.7-1.0 at
  SLOW_MAX; route 6 0.4-0.7 / 0.7-1.0 / 1.5-2.0 ns. Sizes there: UCMPI0 8 -> 5 (x0.55) -> 4 (x0.50); ULINK_N1__1 2 -> 2 -> 1.
- **Reading:** collatz's edge lies between x0.55 and x0.50, one step below x0.55 (as for xorshift, C25). The failure at
  x0.50 is a every-corner shortfall on the loop-entry compare's request path, which a static check on that path would see.
  If you shrink below x0.55, keeping UCMPI0 >= 5 and ULINK_N1__1 >= 2 is what formal's simulator says to try first.
  x0.55's slack on this path is not measured yet. Route 4 at x0.50 hits the event cap on 10 of 12 draws (a livelock or a
  very long run; not traced).
- **Which signals race (route 6, x0.50, band 0.25; failing run vs the same run with +1000 ps on ulink_n1__1.rdly,
  diverge.py):** the first storage / steer LUTs whose event counts differ, in order: ulink_n1__1.rdly.chain.g[0] ->
  ucmpi0.uor -> ucmpi0.udly.chain.g[0..3] -> the joins ucond_br2/3/4_j -> the steers ucond_br4, ucond_br2, ucond_br3
  (7 flips vs 4) -> ulink_n7 stage 0, ulink_n_falseResult_3 stage 0. So the loop-entry steers ucond_br2/3/4 receive their
  request (through ucmpi0's matched delay) before ucmpi0's compare result has settled, and fire both ways: your rule E at
  those steers (the C21 row named ucond_br3/4 from ulink_n1__1). Both sides start at the common launch ulink_n1__1.
- **x0.55's slack on the same race (added 09:05; sideslack.py, extra delay on ucmpi0.uz_n4 = the compare's last LUT,
  uniform bands, no scatter):** route 2: 0.80 ns (all FAST_MIN), 1.08 ns (rest 0.25, CARRY 0.6), 2.25 ns (all SLOW_MAX);
  route 6: 1.02 / 1.36 / 2.27 ns. With x0.50's shortfall (route 2: 0.2-0.4 / 0.4-0.7 / 0.7-1.0 ns), one step of
  UCMPI0 and ULINK_N1__1 is worth ~1.2-3 ns on this path: x0.55 keeps about one ns of it at the model's bands.

## C28. Item 35 (xorshift x0.55a seed 21, sdf 9145cd49) in formal's simx: your draws2 K 2101-2132 32/32, and 256/256 on draws 1-256 (shard C, 2026-11-17 06:25 UTC; untrusted simulation)
Built in formal's sandbox with the same toolchain (nextpnr 9c732bc6303458df; sdf md5 equals yours). Your model, xor19, host
12 ns after each acknowledge. Draw for draw with your draws2: no disagreement. 256 further draws: no failure (95 % Wilson
lower bound 0.985). Last answer (xor19) 24.8-28.8 us. Formal's decode keeps FFs opaque (C23): not a check of FF-mux bits.

## C27. col17 in formal's simx (no bench mask): item 31 and x0.55 return the right counts for 31-bit-peak trajectories (shard C, 2026-11-17 06:00 UTC; untrusted simulation)
Your 05:39 correction: the bench masks n to 16 bits. Formal's simx drives the kernel boundary itself with the full n, so
col17 tests the kernel. Route 20, your model, draws 1-6, fixed host: item 31 (sdf 7aefc4bd) 6/6 PASS, x0.55 of every size
(sdf b2b0dad9) 6/6 PASS, including 77671 -> 231, 94959 -> 301, 109881 -> 309 (oracle kernels.py from kernels/collatz).
So the long carries are right on these draws in the kernel; the board's bench cannot feed them. If full-range correctness
of the kernel matters beyond the bench's domain, formal can run such vectors; col17 is kept at formal/tools/margin/vec/.
The C26 correction below stands for col14 (blind to long carries), not for col17.

## C26 correction (shard C, 2026-11-17 05:45 UTC): formal's "x0.55 clean on 8 routes" is col14-limited
Your 05:07 result (item 31 x0.55 route 20 fails col17's three 30-31-bit-peak vectors) applies to C26 as well: c_shrink2 ran
col14 only, whose trajectories stay below ~21 bits, so its 32/32 on 8 routes says nothing about the long carries. Read C26's
x0.55 row as "no failure on col14", not as margin. Formal's col17 runs (c_shrink7, your shrink7 mirrored) are queued on the
full farm; the same check on item 31's own board route is being run locally. Also from C26's x0.40 failures (c_x40col2,
c_x40r12, untrusted simx): routes 20 and 7 pass with slower delay chains (a shortened matched delay losing to its logic);
route 12 fails at every uniform corner (all arcs FAST_MIN, all SLOW_MAX), so on that route x0.40 is wrong with no scatter at
all -- a static (rule A-like) failure, not a draw-model one.

## C26. Collatz item 31's sizes in formal's simx: clean to x0.55 on 8 routes (as your shrink2); first failures at x0.40 (shard C, 2026-11-17 01:05 UTC; untrusted simulation)
Your model, draws 1-32, col14, fixed host. fm_c_shrink2 (your shrink2 sizes) and fm_c_shrink2b (x0.40-0.10 made with your
shrink_sizes.py from nl6s3a inside the task; files `collatz_sizes_T3cdb_nl6s3a_fx*` exist only there). PASS / FAIL / UNDEC.:
| factor | route 20 | route 3 | route 7 | route 12 | more routes |
|---|---|---|---|---|---|
| 0.85 / 0.70 | 32/0/0 | 32/0/0 | 32/0/0 | 32/0/0 | |
| 0.55 | 32/0/0 | 32/0/0 | 32/0/0 | 32/0/0 | routes 1, 2, 4, 5: 32/0/0 each |
| 0.40 | **10/19/3** | 32/0/0 | **2/27/3** | **0/32/0** | |
| 0.30 | 32/0/0 | 31/1/0 | 32/0/0 | **8/22/2** | |
| 0.20, 0.10 | 0/32 | 0/32 | 0/32 | 0/32 | |
(Each factor is a different route, so the rows need not be monotone.) Last answer (col14) mean: 16.5 us at x0.85,
13.4 us at x0.55, ~12.5 us at x0.40. Your shrink2: x0.85-0.55 8/8 on routes 20, 3, 7, 12: agree. **Reading:** as for item
33 (C25), the first failure in formal's simulator lies between x0.55 and x0.40; x0.55 is clean on 8 of 8 routes. The
failing races at x0.40 are not traced yet.

## C25. Your shrink5 (item 33 x0.55a / x0.50a, routes 1-32) in formal's simx: x0.55a 1024 / 1024; x0.50a fails rarely on routes 7 and 18, at slow-carry draws (shard C, 2026-11-17 00:45 UTC; untrusted simulation)
Farm fm_c_shrink5: per route your draw numbers K = route x 100 + 1..4, plus formal's draws 1-28; your model, xor19, fixed
host. Formal's decode keeps FFs opaque (C23), so your FFMUX-FLAG routes (50a_29) are not judged here.
- **Draw for draw (your K):** every one of your 4-draw sets passes in formal too (all 64 routes x factors where you have
  results): no disagreement.
- **x0.55a, 32 routes x 32 draws: 1024 / 1024 pass.**
- **x0.50a, 32 routes x 32 draws: 1016 / 1024.** Failures only on route 7 (draws 5, 10, 21 of 28: a hang after 7 answers,
  twice; a wrong value at vector 8 once) and route 18 (draws 4, 5, 10, 12, 21: a hang after 5 answers). Their CARRY4 / F7 /
  F8 band is 0.95-0.99 except draw 12 (0.58): the compare's carry chain at the slow end of your unmeasured U[0.2, 1.0]
  against the shortened UCMPI matched delays -- the same race as x0.40a (C24), now rare.
**Reading.** Both simulators put item 33's first failing factor (with the counter's add kept) between x0.55a and x0.50a:
formal finds it at x0.50a on 2 of 32 routes with ~2-4 % of draws; your 4 draws per route are too few to see a rate that
low. x0.55a is clean in both, one step above the first failure; the margin there depends on how slow CARRY4 really is
(the one band your model has never measured). A board run at x0.55a would be the measurement that settles it.

## C24. Your shrink3 / shrink4 sizes for item 33 in formal's simx: x0.40c passes everywhere; x0.40a and x0.30a fail on most routes (shard C, 2026-11-17 00:00 UTC; untrusted simulation)
Same builds (sdf md5s equal yours on every route compared), your model, draws 1-32 per route, xor19, fixed host 12 ns.
Farm fm_c_shrink34. PASS / FAIL / UNDECIDED (event cap) of 32:
| route | x0.40c | x0.40a | x0.30a |
|---|---|---|---|
| 1 | 32/0/0 | **1/26/5** | **0/25/7** |
| 2 | 32/0/0 | **13/6/13** | **4/10/18** |
| 3 | 32/0/0 | 32/0/0 | **11/11/10** |
| 4 | 32/0/0 | **0/32/0** | **0/31/1** |
| 5 | 32/0/0 | 32/0/0 | 32/0/0 |
| 6 | 32/0/0 | **14/17/1** | **0/22/10** |
| 7 | 32/0/0 | **7/20/5** | **1/31/0** |
| 8 | 32/0/0 | **26/6/0** | **0/13/19** |
| 9 | 32/0/0 | 32/0/0 | **8/11/13** |
| 10 | 32/0/0 | 32/0/0 | **0/32/0** |
| 11 | 32/0/0 | 32/0/0 | 31/1/0 |
| 12 | 32/0/0 | **13/16/3** | **17/8/7** |
| 13 | 32/0/0 | 28/0/4 | 31/0/1 |
| 14 | 32/0/0 | **2/28/2** | **0/31/1** |
| 15 | 32/0/0 | 32/0/0 | **0/26/6** |
| 16 | 32/0/0 | **12/18/2** | **0/9/23** |
Also every-size x0.30 / 0.20 / 0.10: route 2 32/0/0, 0/28/4, 0/24/8; route 5 8/20/4, 0/19/13, 0/24/8.
**Against yours so far (your draws are K = route x 100 + 1..4, not 1-32, so this compares rates, not draws):** x0.40a
route 14: you 2/4, formal 2/32 (agree: it fails). x0.30a route 9: you 3/4, formal 8/19 decided (agree: it fails).
x0.40a route 7: **you 4/4, formal 7 of 27 decided** -- if formal's rate held, 4/4 has probability ~0.005: a disagreement.
x0.40a routes 2 and 8: you 4/4, formal 13/19 and 26/32 decided: not decisive with 4 draws. Routes 3, 5, 9-11, 13, 15
agree (all pass). **Reading:** in formal's simulator, shrinking UCMPI0 / UCMPI1 with the rest (x0.40a) breaks item 33 on
about 10 of 16 routes, while keeping them (x0.40c) passes all 16. So the compares' matched delays are the part that
cannot be cut, in this model -- which bears on your 22:02 correction ("the compares' long carry is simulated"): simulated
or not, formal's draws say their current sizes are needed. Your x0.40a failures on route 14 point the same way.
**Next (running, fm_c_shrink4k):** the same builds with YOUR draw numbers (K = route x 100 + 1..4), for a draw-for-draw
table; then a trace of route 4 (0/32 in formal) to name the race.

**Addendum (00:25 UTC): draw for draw, with YOUR draw numbers (fm_c_shrink4k; P pass, F fail, U formal event cap).**
| build | your draws | formal, same K |
|---|---|---|
| x0.40a route 12 | 1201 F, 1202-1204 P | 1201 F, 1202-1204 P (exact) |
| x0.40a route 14 | 1401 P, 1402 F, 1403 P, 1404 F | 1401 F, 1402 F, 1403 U, 1404 P |
| x0.40a route 16 | 1601 F, 1602 P, 1603 F, 1604 P | 1601 F, 1602 F, 1603 F, 1604 P |
| x0.40a route 7 | all P | 701 U, 702 F, 703 U, 704 F |
| x0.40a route 2 | all P | all U (event cap) |
| x0.30a route 9 | 901 P, 902 F, 903 P, 904 P | 901 F, 902 P, 903 P, 904 U |
| x0.40a routes 3, 5, 6, 8-11, 13, 15; x0.30a route 11 | all P | all P (13: 1302 U) |
So the two simulators agree on WHICH routes break when the compares are shrunk (12, 14, 16, 9 at x0.30a), and on 4 of
the 9 failing draws exactly; they differ on route 7 (formal fails, you pass) and on single draws of 14, 16 and 9. Both say
x0.40a is not safe on every route. **The race (fm_c_x40a4, route 4, draw 1):** the 4-round call returns the seed itself
(0 rounds), i.e. the loop test (`i < n-1`, compare ucmpi1) sends the token to the exit; it fails the same with the chain
band at 0.31 or 0.40, the rest at 0.20, no pip scatter, and gets further only with the CARRY4/F7/F8 band at 0.20. So it is
the compare's carry chain (CARRY4 band, the unmeasured part of your model) against its shortened matched delay (UCMPI).

## C23. Your shrink1 (item 33 sizes x0.85 .. x0.40, routes 27 / 2 / 5 / 9) in formal's simx: formal finds the first timing failures at x0.40 on routes 2 and 9; your x0.55 failures are the FF-mux defect formal cannot see (shard C, 2026-11-16 23:30 UTC; untrusted simulation)
Same builds (sdf md5s equal yours), your model, draws 1-64 (yours 1-8), xor19, fixed host 12 ns. Farm fm_c_shrink1.
| factor | route 27 | route 2 | route 5 | route 9 |
|---|---|---|---|---|
| 0.85 | you 8/8, formal 64/64 | 8/8, 64/64 | 8/8, 64/64 | 8/8, 64/64 |
| 0.70 | 8/8, 64/64 | 8/8, 64/64 | 8/8, 64/64 | 8/8, 64/64 |
| 0.55 | **you 0/8 (NOT EQUIVALENT, FFMUX-FLAG), formal 64/64** | 8/8, 64/64 | 8/8 (NOT EQUIVALENT, ffmux-clean), 64/64 | **you 0/8 (FFMUX-FLAG), formal 64/64** |
| 0.40 | 8/8 (NOT EQUIVALENT), 64/64 | running, **formal 22 PASS / 24 FAIL / 18 undecided** | running, formal 64/64 | running, **formal 1 / 63** |
- **x0.55 routes 27 and 9:** your gate fails 11/19 on every draw, the same way, and your fasm_equiv / ffmux_scan flag the
  bitstream. Formal passes them 64/64 because **formal's decoder treats slice flip-flops as opaque** (it simulates LUTs,
  muxes, carries and routing; an FF output stays at its initial value unless the harness drives it). So a formal PASS says
  nothing about FF-mux / packing defects; your fasm_equiv and ffmux_scan remain the only checks for them (as your PROGRAM
  says). Not a timing disagreement.
- **x0.40 routes 2 and 9:** formal's failures are timing: they change with the draw (wrong values from vector 6 to 11,
  hangs after 5-6 answers, some draws at the event cap). Route 27 passes in both of us. **Prediction for your running
  tasks:** route 9 fails most draws, route 2 about half, route 5 passes. A miss there is a disagreement to trace.
So in formal's simulator item 33's matched delays can go to x0.55 on all four routes (x0.40 on 2 of 4); the first timing
failure is between x0.55 and x0.40, and it is route-dependent.

## C22. (00:10 UTC: your draws1 is complete; final: 0 disagreements on candidates, 1 on the control -- +3000 draw 15) The disagreement table, your draws1 vs formal's simx on the same routes and draws: no disagreement so far (shard C, 2026-11-16 22:20 UTC; both untrusted simulation)
Same route (sdf md5 equal), same draw K and its bands (Random(7919K+17), checked against your logs), your vectors.
| candidate | your GLS (draws1, finished draws) | formal simx (fixed host; draws 1-32, and 1-128) | disagreements |
|---|---|---|---|
| item 33 fxa s27 | 32 / 32 | 32 / 32 | none |
| item 27 fxd s2 | 32 / 32 | 32 / 32 | none |
| item 31 fcsel3a s20 | 32 / 32 | 32 / 32; 128 / 128 | none |
| item 28 fcsel3m s20 | 32 / 32 | 32 / 32; 128 / 128 | none |
| item 30 fc64sel3 s10 | 32 / 32 | 128 / 128 | none |
| item 32 fc64sel3p s22 | 32 / 32 | 128 / 128 | none |
| item 29 ipow | 24 / 24 | not decodable (DSP48E1) | -- |
Your control (fxd s2, ucond_br6's condition +3000 / +8000 ps by SDF injection) has no counterpart yet: formal's
simulator reads the bitstream, not the SDF, but simx can add the same delay to the same pins (an `I` injection). I will
run it when your +8000 half reports, so the two controls compare.
**Your control, in formal's simx (fm_c_ctl1, 22:25 UTC):** item 27 fxd s2, the condition input of ucond_br6.u$LUT6 / LUT5
(pin 1, from ucmpi1.uz_n41, the arc your sdf_inject regex selects) + PS, your model and draws:
| injection | your GLS | formal simx |
|---|---|---|
| none, draws 1-32 | (candidate row c1) 32 / 32 | 32 / 32 |
| +3000 ps, draws 1-16 | 16 / 16 | **15 / 16: draw 15 hangs** after 17 correct answers (before 0x12345678, 100 rounds) |
| +8000 ps, draws 17-32 | 0 / 16 | **0 / 16**: every draw returns the 3-round value again at vector 6 (2497366906 for vector 5's 2064144800 ...) |
So formal's model fails your +8000 control as you require, and it disagrees with your gate on ONE draw: +3000, draw 15
(bands chain 0.2157, rest 0.3099, cells 0.3674). That is the first row of the disagreement table; I will trace it.
**The disagreement measured (fm_c_ctl2 / fm_c_ctl4, 23:05 UTC).** On draw 15 the hang does not depend on the runt filter
(the same at w 0, 20, 30, 40); it is a threshold: +2000 and +2500 pass, +3000 hangs, +3500 fails after 4 answers. The
threshold injection (bisection to 31 ps; a run counts as FAIL only on a RESULT MISMATCH) over your draws 1-32:
**+2906 to +4000 ps, median +3281.** At or below +3000: draws 15 (+3000), 21 (+2906), 27 (+2968), 31 (+2906). Draw 8 gives
no verdict at +3500 (event cap, 3 tries). So formal's model puts this steer's slack (condition vs request, plus what the
rest of the circuit tolerates) about 0.1-0.6 ns above +3000 on most draws, and below it on four. **Ask:** your threshold
on a few draws (15 and one with a high formal threshold, e.g. 4 or 24 at +3500), or at least your verdict at +3000 on
draws 21, 27 and 31. If yours sits well above +3000 everywhere, the two models' delays on this path differ by a few
hundred ps, and that is the calibration question to settle (prjxray pip delays in formal's decode vs your xray.sdf).
Both simulators agree that every candidate passes every draw. Neither has shown the model can fail a known-bad build
under YOUR parameters (formal: xf2_1, nc64_7 64 / 64 each); under the wider fid parameters formal's simx fails them in
~2-3 % of draws (C20). So "1.00" from either of us is weak evidence until the model is shown to fail something real.

## C21-RETRACTED. Item 30's "token split" was formal's harness offering n = 97 before its data (shard C, 2026-11-16 21:55 UTC)
**C21 below is withdrawn.** fm_c_x30ps put the race in picoseconds: at ucond_br3 the request (pin 4, from the join)
rises at 3,537,286 ps in both runs; the condition (pin 3, ucmpi0.uz_n4, computed from the kernel INPUT n) moves at
3,535,148 with a 1-ps host and at 3,538,491 with the 12-ns host. The 12-ns host moved n at 3,535,019 (12 ns after
n = 1's acknowledge fell), but formal's simulated host had already raised the request for n = 97 at 3,530,886, 1 ns
after the previous answer: **a host that presents its data after its own request**, which no real host does
(bench / PS writes the operand, then requests). The thresholds fit this: hosts up to 8 ns pass, 16 ns and more fail.
simx is fixed (the request now waits for its data plus su; checked: with an 8-us host the old harness reported a false
MISMATCH on gcd_ps, the fixed one answers right). Every PASS in C20 / C21 stands (a later operand can only make it
harder); the item 30 failures, item 32's design s1 failure, and the rates in C21 are void. Reruns with the fixed host:
fm_c_draws6. Research's rule E row for this steer on item 30 (skew.py -v, unchanged): ucond_br3/4 +1947 raw, -1331
guarded (launch ulink_n1__1.ctl) -- a lead only, as before.

## C21. (WITHDRAWN, see C21-RETRACTED) Item 30 (collatz64 h4s3 s10, sdf 637ff02e) fails 5 of 32 of YOUR draws in formal's simulator: a token split at the entry steers after the zero-trip call n = 1 (shard C, 2026-11-16; untrusted simulation)
**Problem.** Your draws1, mirrored in formal's simulator of the decoded bitstream: your model (draw K = 1..32; bands
from Random(7919K+17) per class -- my values equal those your logs print for K = 1, 2, 9; region 0.02; per-pip 0.126),
the same routes (sdf md5s equal yours), your vectors (xor19, col14, c6415). Formal's LUTs: transport with the 20-ps
filter; host 12 ns after each acknowledge. Farm fm_c_draws4.
| build | draws passing |
|---|---|
| item 27 s2, item 33 s27, item 28 s20, item 31 s20, item 32 s22 (and item 26 s25) | 32 / 32 each |
| **item 30 s10** | **27 / 32: draws 5, 8, 12, 13, 21 fail** |
| BAD xf2_1, BAD nc64_7, pc64_7 (64 draws) | 64 / 64 each: your model's spread never reaches their races |
**The failure (all five draws the same).** Vectors 27, 1, 97, ...: answers 111, 0, then **0 again** for n = 97 (and 118
arrives later as an extra 4th answer), so the stream is one call behind from there on. Traced on draw 5 (fm_c_x30dbg,
fm_c_x30dbg2): the n = 97 call is offered at 3.5309 us; the entry steers `ucond_br3`, `ucond_br4`, `ucond_br2`
(SLICE_X16Y21.A6 / B6, SLICE_X16Y29.C6) fire twice where the passing variant fires once (first difference 3.5374 us),
then `ucontrol_merge1.uarb1` and `ulink_n8` / `ulink_n_index_11` carry two tokens: one copy leaves on the exit side
at once (the wrong 0 at 3.5462 us) and one runs the loop (118 at 6.82 us). The steers' condition was left at "exit"
by the zero-trip call; the request for the next call reaches the steer before the condition has moved. Your rule E
at the entry steers, after a zero-trip call.
**What it needs (variants of draw 5, bands b_c / b_r / b_cells = 0.217 / 0.225 / 0.987):**
- fails as drawn, with b_r 0.27, b_cells 0.50-0.90, no per-pip scatter, no runt filter (w 0), host 12 ns or 100 ns,
  and with vectors (1, 97);
- passes with **b_c 0.27** (delay chains slower), **b_cells 0.40**, **a 1-ps host**, or with (97), (27, 97), (2, 97).
So it needs the zero-trip call just before, delay chains near the fast end of your U[0.20, 0.31] and the CARRY4 / F7 /
F8 band at 0.5 or more (the part of your model you mark "never measured"). The filter and the pip scatter play no
part, so this is not a runt-pulse artefact of formal's LUT model.
**What I would like from you:** your draws1 result for item 30 on draws 5, 8, 12, 13, 21 (tasks 21-24 were still
running at 21:15 UTC). If your GLS passes them, this is the disagreement the owner asked for and the next thing to
trace (start-up, host model and the steer LUT model are the candidates). If it fails them too, item 30 should not go
to the board as is. Files: fm_c_draws4/7 (draws.txt), fm_c_x30dbg (variants), fm_c_x30dbg2 (diverge_*.txt,
boundary_fail.txt). Reproduce: `DRAWS=32 DRAW_MODEL=research run.sh` (formal/tools/margin/README.md).

**Addendum (21:30 UTC, fm_c_draws5: 128 of your draws per route, your vectors).** Item 30's board route: **108 / 128
pass (0.84, Wilson 95 % 0.77-0.90)**; all 20 failures are this split ([111, 0, 0 ...]). Item 30's design on seeds 1, 2, 3:
128 / 128 each. Item 32's design (h4s3p): board route s22 128 / 128; seeds 2, 3 128 / 128; **seed 1 127 / 128, the same
split**. Items 25, 26, 28, 31: 128 / 128. So the race is in the h4s3 / h4s3p collatz64 family and its rate depends on
the route; item 30's board route is the worst of the eight routes measured.

## C20. The board approximator in formal's simulator of the decoded bitstream: every board candidate 64/64; both known-bad builds fail some draws (shard C, 2026-11-16; untrusted simulation)
**Problem.** Your PROGRAM and ours (owner, 2026-11-16: "the board decides"): judge a build by the fraction of random
delay draws that return the right answers. This is the same question asked in formal's own simulator: the circuit
decoded from the bitstream's FASM (not the netlist), prjxray bands per pin, transport LUTs with the 20-ps runt filter
(H_RUNT(20); no metastability resolver), host 12 ns after each acknowledge, formal's start-up.
**Model (first run, before your FOR-FORMAL model was published):** your fid GLS parameters: every pin arc at
FAST_MIN + 0.38 (SLOW_MAX - FAST_MIN), times exp(0.16 N) per 10x10-slice region and exp(0.126 N) per arc. Your gate
vectors (xor19, col15, c6416), oracles from kernels/*.c (formal/tools/margin/kernels.py). `run.sh DRAWS=64`,
farm fm_c_draws1 / fm_c_draws2. Every rebuilt SDF md5 equals yours.
| build | sdf | PASS / FAIL / UNDEC. of 64 | last answer, mean (range) |
|---|---|---|---|
| item 27 xorshift s2 | a9bdac53 | 64 / 0 / 0 | 36.5 us (33.0-40.4) |
| item 33 xorshift s27 | 7f0c0592 | 64 / 0 / 0 | 36.0 us (33.0-39.5) |
| item 33's design, seeds 1 / 3 / 4 | 796b669f / .. | 64/0/0 each | 35.8 / 36.2 / 36.0 us |
| item 28 collatz s20 | d86bdde5 | 64 / 0 / 0 | 23.1 us |
| item 31 collatz s20 | 7aefc4bd | 64 / 0 / 0 | 19.3 us |
| item 25 collatz s24 | e001dc27 | 64 / 0 / 0 | 32.8 us |
| item 26 collatz64 s25 | 6982a9d5 | 64 / 0 / 0 | 100.1 us |
| item 30 collatz64 s10 | 637ff02e | 64 / 0 / 0 | 96.4 us |
| item 32 collatz64 s22 | 842dd4d7 | 64 / 0 / 0 | 88.1 us |
| item 32's design, seeds 1 / 2 / 3 | .. | 64/0/0 each | 91.4 / 84.7 / 83.2 us |
| **BAD xf2_1** | dc138ea2 | **60 / 2 / 2** | 43.6 us |
| **BAD nc64_7** | 98809562 | **62 / 2 / 0** | 165.6 us |
| pc64_7 (nc64_7's good neighbour) | acc06847 | 64 / 0 / 0 | 167.5 us |
The failing draws: xf2_1 draw 56 returns 2068339104 for xorshift(0x92d68ca2, 3) (bit 22 wrong) and draw 18 stops after
5 answers, both at the 3-round vector where your trace puts its ulink_n7 hold race; nc64_7 draws 18 and 38 return
wrong step counts (e.g. 133 for 6171, 862 for 77031). Deterministic: the xf2_1 task, run twice, gave the same draws.
**Correction (22:15 UTC, after C21-RETRACTED; fm_c_draws7, fixed host, same fid model):** BAD xf2_1 **61 / 1 / 2** (draw 56
was the harness artefact: it followed the zero-trip vector; draw 18 still fails, stopping after 5 answers); BAD nc64_7
62 / 2 / 0 unchanged (draw 18 is wrong at the first vector, 239 for 27); pc64_7 64 / 0. Under YOUR model (fm_c_draws4,
64 draws) all three pass 64 / 64, and with the fixed host every candidate route passes 128 / 128 (fm_c_draws5/6:
items 25, 26, 28, 30, 31, 32 and items 30 / 32's designs on seeds 1-3; items 27 and 33 32 / 32 in fm_c_draws4).
**Reading.** In this model the candidates are clean and the known-bad builds are below their neighbours, but only by
~3 % of draws: the model's spread rarely reaches the races that broke them at your FAST_MIN gate. A fraction of 1.00
over 64 draws says the failure rate is below ~6 % (95 %), not that it is zero. "Last answer" includes the 400-ns
reset and the host's 12-ns reaction per handshake; it is the whole vector list, not ns per iteration.
**Next (running, fm_c_draws3):** your draws1 exactly: your model (draw K = 1..32, bands from Random(7919K+17),
region 0.02, per-pip 0.126), your eval_task.sh routes, your vectors (col14, c6415). That gives the per-draw
disagreement table. Tool: `formal/tools/margin/draws.py`, `run.sh DRAWS=N` (README "The board approximator").

## C19. The "steer-cone" failures are runt request pulses into a link controller, at the edge of the 20-ps filter (shard C, 2026-11-16; search, untrusted)
**Problem.** Since C11 I have reported failures from "steer cones" (every arc into a steer/merge LUT slowed at once,
host 2 ns) at kappa 0.35-0.44, without naming the race. explain.py looked at the storage LUT where the failure
surfaced, and that LUT was not where the run went wrong. **New tool:** simx `--tcut T` keeps the slowed arcs slow
only for input changes before T. `formal/tools/margin/tcut.py` bisects T until run(T) fails and run(T-1) passes;
the first storage LUT that then differs is where the outcome is decided. It also traces the deciding pulse upstream
(`run.sh TCUT=1`). Farm fm_c_tcut1 (same routes as c_min1, builds rebuilt from your recipes), plus a local run on
item 25.

**Finding.** Every one of these failures has the same shape. A pulse 20-41 ps wide leaves a steer or merge LUT and
reaches a link controller's request pin while the request it gates is already high. In formal's transport-delay
model the pulse then circulates in the controller's own feedback loop (it oscillates with a period of 68-128 ps)
and the run fails.
| build | kappa (w 20) | pulse source -> controller | pulse width |
|---|---|---|---|
| item 27 xorshift s2 | 0.28 (PHYSICAL hang), 0.42 | ucond_br9 (SLICE_X16Y32.C6) -> ulink_n_trueResult_12.ctl | 37 / 32 ps |
| fcsel3m s2 | 0.37 | ucond_br5 (SLICE_X18Y26.C6) -> ulink_n_trueResult_4 st0 ctl | 20 ps |
| fcsel0 s24 | 0.37 | ucontrol_merge1.udly.chain.g[1] (SLICE_X18Y24.C6) -> ulink_n_index_11 st0 ctl | 20 ps |
| item 25 collatz s24 (local) | 0.62 | compare-tree F8 glitch -> SLICE_X16Y34.A5 -> ulink_n_falseResult_3 st0 ctl | 41 ps |
| item 25, w 0 | 0.38 | ucond_br6 (SLICE_X16Y26.A5, out = !A1 & A2, inputs 3 ps apart) -> ulink_n_falseResult_7 st0 ctl | 1 ps |

On item 25 (the case traced end to end) the steer's condition comes from a compare tree whose F8 mux glitches for
29-47 ps (its select and its data input arrive at different times). In the all-fast reference that glitch reaches
the steer about 900 ps before the request, and the steer masks it. With the cone at 1.62 x fmax it arrives after the
request, so the steer passes it on as a request pulse. This is your rule E (the select or condition reaches the
steer before the request it gates), broken by a glitch rather than by a late final value.

**What this means.**
- Two of the w=20 rows fail on pulses EXACTLY 20 ps wide, the H_RUNT threshold. The others are 32-41 ps. These
  kappas measure the filter setting as much as the circuit. At w 0 the same cones fail on 1-ps pulses.
- Whether such a pulse sustains an oscillation in a LUT feedback loop on silicon is a question about the device, not
  about routing. Formal's model says yes for any pulse wider than w, because it has no pulse shrinkage. These rows
  should NOT be read as races with a picosecond slack, and I do not rank builds on them. The binding races I
  reported with picosecond slack (C13/C16 feedback, C11/C18 latch holds) are two-path races and are unaffected.
- A question for you: can your GLS show a 20-40 ps pulse on a ctl input (`ulink_*.ctl` pin from a cond_br / merge
  delay LUT)? If your gate passes such pulses with transport interconnect, a forced one (a pulse injected on
  ucond_br9's output while ulink_n_trueResult_12's request is high) would show whether your model also oscillates.
Files: fm_c_tcut1/*/tcut_*.txt on claude/cluster; tool formal/tools/margin/tcut.py; JOURNAL-C 07:2x-07:4x.
**Correction to C11/C15 wording:** the c_min1 explanations of minimised w=0 rows ran the wrong row (explain.py took
the w=20 row's arc set). Their "not a two-path race" verdicts are void; this item replaces them.

## C18. Board candidates 29-32 (your FOR-FORMAL 5feabe72), with your host and with a 1-ps host (shard C, 2026-11-16; search, untrusted)
Farm fm_c_margin_bq29: every race class, each broken race traced at your SDF; hosts at 1 ps and 12 ns; files in
`formal/tools/margin/out/farm_bq29_*`. Kappas only order the search.
- **item 32 (collatz64 h4s3p s22, sdf 842dd4d7).** The first finite failure, with either host, is your ulink_n13 hold
  race: `ulink_n13.lat.pair[4]` (LUT5); common launch `ulink_n13.ctl`; path A, ctl -> the latch's enable: 1 LUT + 6 routing
  arcs, 972 ps at the fast-band maximum, **SDF 1752 (routing 1600)**; path B, ctl -> `uack` chain (3 LUTs) -> `umux1.uya` ->
  `ulink_n_falseResult_5` stage 1 ctl -> its latch -> `umux1` data -> the ulink_n13 latch's data pin: 8 LUTs + 43
  routing, SDF 5613. Slack +987 ps worst in-band, **+3861 ps at your SDF** (1.46 x the worst short-ring error). A KERNEL
  race, same structure as items 26 and 28 (C14); keeping ULINK_N13_UACK at 3 leaves it nearly 4 ns at the SDF here.
  ulink_n28 does not appear among the races the search breaks up to 0.45. Hangs (kernel acks a/b, not start) from
  0.44 (a steer cone, not traced). The falseResult_7 controllers: +838 ps at the SDF (fbslack), as on item 28's routes.
- **item 30 (collatz64 h4s3 s10, sdf 637ff02e).** No finite failure up to 0.45 with either host; a livelock at 0.44
  (12-ns host) and hangs from 0.41 (steer cones, not traced). falseResult_7 controllers +838 ps at the SDF.
- **item 31 (= fcsel3a s20):** C15 (uselect0's capture holds to 0.45; falseResult_7 stage 0 controller +174 ps worst
  in-band, +764 at the SDF).
- **item 29 (ipow h4s3 s19, sdf 4a92cdf3): not analysed.** Its multiplier is a DSP48E1, and formal's bitstream decoder
  refuses DSP sites (it models LUTs, MUXF, CARRY4, flops and latches only). A margin for item 29 needs a DSP48 model.

## C17. Your select negative controls (research/data/selneg) in formal's model: the request-join injections never fail; the same select at the mux DATA LUTs fails from +6 ns (shard C, 2026-11-16; search, untrusted)
`formal/tools/margin/selneg.py` (simx with an extra delay on chosen arcs; farm fm_c_selneg2; outputs
`formal/tools/margin/out/farm_selneg2/`). Same routes as yours (items 27, 28, 26; rebuilt, SDFs = yours), every other arc
at its prjxray fast-band minimum (your FAST_MIN column), host releasing operands 12 ns after the acknowledge, transport
delays everywhere. Two injections from the select link's latch (`lat.odd`):
- **join**: into `umuxN.uj0` / `uj1` -- your arcs, as your README describes them;
- **data**: into the mux's 32 data LUTs (`umuxN.udat.*`) -- the select reaching the data late (rule E's race).
| mux | join +1 / +3 / +6 / +12 ns | data +1 / +3 / +6 / +12 ns | your gate, FAST_MIN, join +3 / +6 / +12 |
|---|---|---|---|
| item 27 umux0 | ok ok ok ok | ok ok **WRONG** no-verdict | PASS / no completion / no completion |
| item 27 umux1 | ok ok ok ok | ok ok no-verdict **WRONG** | PASS / FAIL 16/17 / no completion |
| item 27 umux2 | ok ok ok ok | ok ok ok ok | no completion / no completion / no completion |
| item 27 umux3 | ok ok ok ok | ok ok ok **WRONG** | PASS / PASS / PASS |
| item 28 umux0 | ok ok ok ok | ok ok no-verdict **WRONG** | no completion / no completion / no completion |
| item 28 umux1 | ok ok ok ok | ok ok no-verdict **WRONG** | no completion / no completion / no completion |
| item 28 umux2 | ok ok ok ok | ok ok ok **WRONG** | PASS / PASS / PASS |
| item 26 umux0 | ok ok ok ok | ok ok ok **WRONG** | -- / no completion / no completion |
| item 26 umux1 | ok ok ok ok | ok ok ok no-verdict | PASS / PASS / no completion |
| item 26 umux2 | ok ok ok ok | ok ok ok **WRONG** | PASS / PASS / PASS |
("no-verdict": event cap, typically a livelock; "WRONG": a wrong answer.)
- In formal's model a late select at the REQUEST join only delays the mux's request (the runs end later by about the
  injected time, and every answer is right): that is the safe direction for the bundle. Your gate fails on 20 of
  these runs. We checked one obvious difference and it is not it: your gate's interconnect is transport too
  (`build_ps.sh` compiles with `-DGLS_TRANSPORT_IC`). Others remain: your clocked PS host, your LUT cells (specify
  IOPATH: inertial at ~124 ps), your 17 vectors vs our 3-4. A trace of one failing run (item 28 umux0, join +3000,
  FAST_MIN: which handshake stops, and where) would tell which; formal can replay the same injection with a dump.
- The data-LUT injection is the arrival race: in formal's model it breaks item 27 umux0/umux1 and item 28 umux0/umux1
  from +6 ns, five more lines at +12 ns, never item 27's umux2; +3 ns passes everywhere. So on these routes the select
  can arrive 3+ ns late at the data LUTs before a capture breaks; your corrected rule E (arrival at the mux) is the
  check that matches this race.

## C16. C13's controller-feedback race over 32 routes, from your SDFs (shard C, 2026-11-16; static screen, untrusted)
`fbslack.py` on 16 routes of item 28's structure (fcsel3m, seeds 1-16) and 16 of item 27's (xorshift pre_dec fr4, seeds
1-16), rebuilt on the farm (fm_c_fbroutes; table: `formal/tools/margin/out/fbroutes/table.txt`). Slack = B (the fastest SDF
return from the controller's output to another of its pins) - A (its own feedback interconnect + IOPATH), at your SDF.
| controller | routes | median | min (route) | max |
|---|---|---|---|---|
| `ulink_n_falseResult_7.many.stage[0].u.ctl` (item 28's structure) | 16 | +1119 ps | +906 (s1) | +1402 |
| `ulink_n_falseResult_7.many.stage[1].u.ctl` | 16 | +1117 | **+764** (s4, s14: feedback via 5 routing arcs, A 772) | +1124 |
| `ulink_n_index_11.many.stage[0].u.ctl` (select link) | 16 | +2269 | +1774 | +2715 |
| `ulink_n_index_15.many.stage[0].u.ctl` (item 27's structure, select link) | 16 | +1397 | **+845** (s2 = item 27's own route) | +1813 |
- On 12 of the 16 fcsel3m routes the smallest controller slack anywhere in the kernel is one of the falseResult_7
  stages (0, 1 or 2); on the xorshift routes it is most often the select link `ulink_n12__1`'s controller (+706 to +1118).
- The feedback interconnect A is 295 ps when the placer keeps it in the slice (A = 419 with the LUT) and about 650 ps
  when it leaves it (A = 772): that single placement choice moves the slack by ~350 ps, and the fast-band worst split
  (C13, C15) by more. Route minimum over all 32 routes: +684 ps (fcsel3m s10, `ulink_n8` stage 1 ctl).
- So at your SDF this race has 0.7-1.4 ns everywhere we looked, about 1-1.6 x the worst short-ring error of a path that
  long. The dynamic runs (C13, C15) show where it bites: inside the fast band, when the feedback route is the long
  one (fcsel1 s24 +45 ps, fcsel3a s20 +174 ps). A check that keeps every controller's feedback inside its slice, or
  that requires B - A above a guard, would remove the tail.

## C15. Your two asks of 2026-11-16 (FOR-FORMAL 1b00b6ae): C10's routes with a 12 ns host, and fcsel3a seed 20 (shard C, 2026-11-16; search, untrusted)
`formal/tools/margin/run.sh` with `HOSTDELAY=12000` (the host moves the next operand 12 ns after the acknowledge it
reacts to; still a Spec.Env behaviour), every race class, each reported race traced to two paths and timed at your SDF
(farm fm_c_margin_r12; files there and in `formal/tools/margin/out/`). The kappas only order the search.
**C10's routes, 12 ns host.** The falseResult_3 stage-0 races C10 reported are gone on every route (they were
input-hold races against a 1-ps host, as the audit and C11 said). What the search still breaks:
| route | first finite failure (kappa) | the race, in ps | hang (kernel acks a/b, not start) |
|---|---|---|---|
| fcsel2 s1 (5b538ca5) | none <= 0.45 | -- | 0.37: `ulink_n_falseResult_7` stage 1 ctl feedback (4 routing arcs) vs rdly g[0] -> stage 2 ctl -> back: +132 worst in-band, **+904 SDF** |
| fcsel2 s2 (fb1efc41) | 0.44, a steer cone (not traced to two paths) | -- | 0.45 |
| fcsel1 s24 (afab5445) | none <= 0.45 | -- | 0.09: falseResult_7 st0 ctl feedback (5 routing arcs): **+45** worst in-band, +406 SDF (C13) |
| fcsel1 s1 (4445b56c) | 0.42: a fork near `ulink_n_falseResult_9` stage 0's latch (SLICE_X17Y54.D6 pin 0 direct vs pin 4 through 2 LUTs) | +111 worst in-band, +657 SDF | 0.40 |
| fcsel0 s24 (bb5fbbdb) | 0.37, a steer cone (got [0]; not traced) | -- | -- |
**fcsel3a seed 20 (7aefc4bd).** 1-ps host: the first race is again the input-hold race at falseResult_3 stage 0 (through
the host: +393 worst in-band, +1216 SDF). 12-ns host: no single-route or capture race below 0.45; the falseResult_7
controllers hang the kernel: stage 0 from 0.24 (no filter): feedback 1 LUT + 5 routing (SDF 772) vs rdly g[0] -> stage 1 ->
back (SDF 1536): **+174 ps worst in-band, +764 ps at your SDF** (0.71 / 1.06 x the worst short-ring error); stage 1 from
0.44: +399 / +1117. **uselect0's line** does not appear among the races our search breaks up to 0.45 on this route
(single routes, whole data cones, steer cones); its own slack in ps (its data vs its request) is not computed yet --
the tool explains races it breaks, and this one it did not break.
**fcsel3a seed 20, capture races swept to kappa 0.90 (12-ns host; fm_c_margin_usel2).** The first one broken (0.46) is
the select link's own latch, `ulink_n_index_11.many.stage[0].lat.odd`, against `ucontrol_merge1`'s bundle: common launch
`ucontrol_merge1.uarb1.ustate`; path A (data): `uarb1.ugrant` -> merge1's data LUT -> latch pin: 3 LUTs + 12 routing,
740 ps fast mid, SDF 1555; path B (enable): `ustate` -> merge1's matched delay `udly.chain.g[1]` -> the link's ctl ->
latch enable: 4 LUTs + 16 routing, 850 ps, SDF 1985. Slack **+110 ps fast mid, +430 ps at your SDF (0.46 x the worst
short-ring error), and -93 ps at the worst split inside the fast band** (A at its band maximum, B at its minimum). So
merge1's matched delay (two elements here) covers its data by about 0.1-0.4 ns. uselect0 is on neither path, and on none of the
paths explained for the other captures that fail up to 0.90 (ulink_n14__1 at 0.82, +1679 ps SDF; three others at
0.84-0.88 with 2.2-9.6 ns of SDF slack; three more traces were rejected as inconsistent). **uselect0's line itself (farm c_margin_usel3, `conenames.py`):** the only capture whose data cone runs through
uselect0 is `ulink_n_falseResult_9.many.stage[0]` (32 latch bits; cone includes uselect0's data LUTs and `uselect0.uz_n29`).
With that whole cone slowed to (1+k) x its fast-band maximum and everything else at (1-k) x the minimum, the kernel is
correct at k = 0.45 (20 ps filter; fm_c_margin_r12 task 7) and the run at k = 0.90 is undecided (event cap). So
uselect0 at 7 holds its capture far beyond every race above in this search. Its slack in ps is not computed (the tool
traces races it breaks). **Checked (farm c_verify1): this race alone does
NOT fail** -- with exactly path A slowed to (1+k) x its fast-band maximum and everything else at (1-k) x the minimum,
the kernel is correct at every k from 0 to 0.45. The -93 ps split is arithmetic on two path sums; the latch does not
lose a value from it on these vectors. The cone failure at 0.46 needs more of the data cone slow at once. Same
structure on item 27 (C12): +1418 / +1423 ps SDF there.
**fbslack.py agrees.** Run on the farm's SDFs, the static screen gives the same controller slacks as the dynamic traces:
fcsel3a s20 st0 ctl +764 ps, fcsel2 s1 st1 ctl +904 ps (both identical to explain.py). So `fbslack.py BUILD.sdf --grep .ctl.`
is a 5-second check of this race on any route of yours.

## C14. The ulink_n13 race (item 28's and item 26's first finite failure) in picoseconds: a kernel race with 2.5-3.1 ns of slack at your SDF (shard C, 2026-11-16; search, untrusted)
Traced by `tools/margin/explain.py` (trigger chains; farm fm_c_explain6). KERNEL race on both: the enable of a
`ulink_n13` latch bit against the NEXT value reaching its data pin after ulink_n13's acknowledge reopens the upstream link.
| build | path A: ulink_n13.ctl -> enable pin | path B: ctl -> uack chain -> umux1.uya -> falseResult_5 st1 ctl -> its latch -> umux1 data -> data pin | slack mid / worst in-band / SDF | x 8.5 % / x 47 % (SDF) | your row |
|---|---|---|---|---|---|
| item 28 (lat.pair[6] LUT6) | 1 LUT + 7 routing: 609 ps mid, SDF 1142 | 6 LUTs + 34 routing: 1958, SDF 4273 | +1348 / +965 / **+3131** | 8.6 / 1.56 | H +1337 (enable 1241, data 2628); hold_bits ulink_n13 min 1566 ps |
| item 26 (lat.pair[6] LUT5) | 1 LUT + **12 routing**: 964, SDF 1975 | 8 LUTs + 38 routing: 2179, SDF 4523 | +1215 / +710 / **+2548** | 6.6 / 1.20 | (not looked up) |
| fcsel3m seed 24 (item 28's structure; host 2 ns): `ulink_n10__3.lat.pair[20]` (LUT5), launch `ucond_br7.uack` | ulink_n10__3.ctl -> enable: 2 LUTs + **22 routing**: 1518 mid, SDF 3337 | ufork8 -> ulink_n10__4 ctl -> ufork3 -> umux0.uya -> falseResult_9 st1 ctl -> its latch -> umux0 data -> pin: 8 LUTs + 48 routing: 2930, SDF 6373 | +1413 / +670 / **+3036** | 5.6 / 1.01 | (not looked up) |
- Your rule H and our trace agree on the enable side (1241 vs 1142 ps at the SDF) and differ on the data side (2628
  vs 4273): our path B is the chain that actually fired in the run (through umux1 and falseResult_5's stage 1 latch);
  your H takes the earliest possible sender, which can be shorter. Both say clean by more than a nanosecond.
- The kappa (0.42 on item 28, 0.26 on item 26) is only this slack's ratio: the race is lost once (1+k) x path A's
  fast-band maximum exceeds (1-k) x path B's fast-band minimum: k = (1872 - 1162) / (1872 + 1162) = 0.23 on item 26.
  Item 26 sits lower because its enable route is 12 routing arcs long, not because its kernel is closer to failing at
  the SDF. For the audit (T119, replay correct with this arc at 1.26 x FAST_MAX and the kernel at 0.74 x FAST_MIN):
  formal's prjxray fast band puts path A at [1162 max] and path B at [1872 min] ps; if the audit's FAST_MIN for
  path B's routing is larger than prjxray's, the replay keeps a positive margin (393 ps there), which would explain it.

## C13. A race none of your rules checks: a link controller's own feedback against the next stage's acknowledge (`ulink_n_falseResult_7` stage 0; shard C, 2026-11-16; search, untrusted)
The hangs in C12 (the kernel acknowledges a and b, never start, and stops) come from one controller,
`ulink_n_falseResult_7.many.stage[0].u.ctl` (a C-element LUT that reads its own output). Traced by `tools/margin/explain.py`
(farm fm_c_explain4; KERNEL race: neither path goes through your host):
- Common launch: that controller's output.
- Path A (must arrive first): its own feedback route back into it (the state it holds).
- Path B: through stage 0's request delay `rdly.chain.g[0]` (one element) to stage 1's controller and back into stage 0's
  controller as the acknowledge.
| route | path A (feedback) | path B (rdly g[0] -> stage 1 ctl -> back) | slack mid / worst in-band / your SDF | x 8.5 % / x 47 % (SDF) | kappa (search order) |
|---|---|---|---|---|---|
| fcsel1 seed 24 (sdf afab5445) | 1 LUT + **5 routing arcs**, 384 ps mid (SDF 851: routing 727) | 3 LUTs + 10 routing, 570 (SDF 1257) | +186 / **+45** / +406 ps | 3.8 / **0.69** | 0.09 |
| item 28 = fcsel3m seed 20 | 1 LUT + 2 routing arcs, 290 (SDF 419) | 3 LUTs + 12 routing, 744 (SDF 1536) | +454 / +335 / +1117 ps | 8.6 / 1.55 | 0.36 (no filter) |
- So the controller has to see its own new state before stage 1's acknowledge comes back, and with stage 0's request
  delay at one element that return is only three LUTs long. On fcsel1 seed 24 the placer gave the feedback route five
  routing arcs (727 ps at your SDF), and the slack inside the fast band is 45 ps. Your rows on that route:
  H +936 / I +467 at stage 1's ctl and F (matched-delay drain) rows elsewhere. None of them is this race (a C-element's
  own feedback against the acknowledge it waits for). We have not found it in your rule set.
- What the failure looks like: the controller misses its state for one event, the link's handshake is left half done,
  and the kernel stops after acknowledging a/b but not start. Formal's frozen Spec calls such runs vacuous; on a board
  this is a hang. A proposed fix in formal's Spec (`SpecWF`) would count it.
- Suggestion: a check that every link controller's feedback route is shorter than its shortest acknowledge return,
  with a guard, on every route. It is a one-route quantity, so it moves with placement (5 routing arcs on one seed,
  2 on another): measure it over routes.
- **A screen you can run on any route now:** `python3 formal/tools/margin/fbslack.py BUILD.sdf --grep .ctl.` (formal's
  branch, needs only your nextpnr SDF, ~5 s): for every LUT that reads its own output, A = its feedback interconnect +
  that pin's IOPATH, B = the fastest SDF path from its output back to another of its pins, slack = B - A, also as a
  multiple of 8.5 % and 47 %. On item 25's route it gives `ulink_n_falseResult_7.many.stage[0].u.ctl` A 419, B 1536,
  slack +1117 ps through rdly g[0] -> stage 1's ctl, the same race and numbers explain.py traced dynamically on item
  28. B is the fastest STRUCTURAL return, so a small slack is a race to check, not a failure. Outputs for items 23, 25,
  BAD xf2_1 and gcd_ps: `formal/tools/margin/out/fbslack/`.

## C12. Item 27 (xorshift board candidate) and item 28: the races formal's tool breaks first, in picoseconds, beside your rows (shard C, 2026-11-16; search, untrusted)
All from farm runs of `formal/tools/margin/run.sh` with every race class (single routes, whole data cones, steer
cones) and the checks of C11; files `origin/claude/cluster:results/fm_c_margin_all2/<task>/` and
`fm_c_explain3/7/explain_*.txt`. "Slack" = path B minus path A from their common launch (positive: the required order
holds), at the prjxray fast-band midpoint, at the worst split inside the fast band, and at YOUR nextpnr SDF; then as a
multiple of the ring data's median error (8.5 %) and worst short-ring error (47 %, 7-link rings). The kappa column is
only the order in which our adversary breaks things.
**item 27 (sdf a9bdac53 = your fxd seed 2).** No single route breaks it in our range; two capture races do:
| latch (capture) | common launch | path A (must be first) | path B | slack mid / worst in-band / SDF | x 8.5 % / x 47 % (SDF) | your rows | kappa |
|---|---|---|---|---|---|---|---|
| `ucontrol_merge0_olink.lat.odd` | `ucontrol_merge0.uarb1.ustate` | data: 3 LUTs + 11 routing, 767 ps (SDF 1397) | enable via the olink ctl: 6 LUTs + 27 routing, 1484 (SDF 3173) | +716 / +451 / **+1776 ps** | 6.6 / 1.2 | none found in fxd seed 2's files (your fr3 build fxf4_s seed 2 has H +3492 at the olink ctl) | 0.39, wrong count (2 of 4 answers), checked |
| `ulink_n_index_15.many.stage[0].lat.odd` (a select link) | `ucontrol_merge1.uarb1.ustate` | data: 3 LUTs + 12 routing, 787 ps (SDF 1540) | enable: 6 LUTs + 25 routing, 1284 (SDF 2958) | +498 / **+243** / **+1418 ps** | 5.6 / **1.0** | your hold_bits on fxd seed 2: the same LUT (SLICE_X14Y33.B6) is the tightest hold bit, min 1159 ps (fxf4_s, fr3: H +1394 at the st0 ctl) | 0.28-0.29: the kernel acknowledges a/b, not start, and stops |
(Update, farm c_verify1: with the host moving data 12 ns after the acknowledge, the olink capture race first fails at
kappa 0.61, not 0.39 as with a 1-ps or 2-ns host, and that 0.61 run breaks Spec.Env (not a counterexample). So although
both of its paths are inside the kernel, how early your host offers the next operand changes whether it bites.)
Both are KERNEL races: neither path goes through your host (unlike C10's and item 25's, which close through the host
releasing the next input; formal's tool now separates the two, `HOSTDELAY=`). Both are setup (capture) races at the merge-arbiter's output: the arbiter's state flip reaches the latch's data through
3 LUTs and its enable through 6, so the bundling here is the difference of two short paths, about 0.5 ns. Your rules
H and hold_bits look at the other direction (hold) of the same latches; rule E looks at the mux select arrival; we have
not found a row of yours for this setup race at the latch's data pin. At your SDF the second race has a slack equal to
the worst error measured on short rings. Path A is the data path that is critical in the all-fast reference run; the
adversary slows the whole data cone, so the path that actually lost can be a longer one inside it (being traced). Not
yet checked on other routes of item 27 (one route is a sample).
**item 27's structure on 4 more routes (seeds 1, 3, 4, 5; sdf e2914f00, e6719b93, 32142fab, 2ae1a2b5; host moving
data 2 ns after the acknowledge, so kernel races only; farm fm_c_margin_x27r).** Seed 5 has the same capture race at
the merge1-arbiter-fed select-link latch: split `ucontrol_merge1.uarb1.ustate`, data 3 LUTs + 11 routing (SDF 1398 ps),
enable 6 LUTs + 24 routing (SDF 2821): slack **+1423 ps at your SDF (1.07 x the worst short-ring error)**, vs +1418 on
seed 2. So this race is about 1.4 ns at the SDF on two routes out of two where it shows. On all five routes the search
also breaks steer cones (a branch condition reaching its C-element late: 0.30-0.45) and finds partial-ack hangs
(0.23-0.31); the steer races are not yet traced to two paths (the tool reports them UNRELIABLE rather than guess).
**item 28 (sdf d86bdde5).** Besides A8's ulink_n13 race (your H +1337, hold_bits 1566 ps, kappa 0.42): from kappa 0.36
(no filter) the kernel can stop after acknowledging a and b but not start, at `ulink_n_falseResult_7.many.stage[0]`'s
controller reading its own output late (a feedback race). The same controller does this on fcsel1 seed 24 from kappa
0.09, on fcsel3m seeds 2 and 24 at 0.35-0.37, and on items 25 and 26 at 0.37-0.38. Formal's frozen Spec calls these runs
vacuous (A: `SpecWF`); on a board they are hangs. Picosecond form: farm c_explain4, running.
**Livelocks** (periodic, never answering; `simx --periodic`): item 28 at 0.42, item 26 0.38, fcsel3m s2 0.38, s24
0.40, item 27 0.35 (no filter).

## C11. What formal's margin tool now looks at beyond A8: whole data paths slow at once (capture races), livelocks, and three checker fixes (shard C, 2026-11-16; search, untrusted)
Item 28's single-route result is A8 (same farm builds, same numbers; C's run: `formal/tools/margin/out/farm_item28_fcsel3m_s20/`).
Per the owner's rule (PROGRAM.md, "A kappa is not a result") the kappas below only say which race our adversary
breaks first; the picosecond form of each race (both paths from their split, cells and routing, slack at your SDF,
your rule row) is what C builds next, in the tool.
- **Capture races (new class, `tools/margin/cones.py`, run.sh `CONES=1`).** A8's sweeps slow ONE route. A bundled-data
  capture fails when the whole data path into a latch is slow and its request path fast. Per link stage, the tool now
  slows the entire combinational cone into the latch bits (datapath, carry, mux data LUTs and the routes of their
  select inputs) and keeps everything else fast. `STEER=1` does the same for a C-element or steer reading data (a
  branch condition). On every collatz/collatz64 route tried, the first capture race the adversary breaks is the
  one-bit latch of **`ulink_n_index_11.many.stage[0]` (lat.odd)**, one of your select links, whose data cone is the
  index computation (~770-1550 arcs); on xorshift item 27 it is `ulink_n_index_15` stage 0 (also a select link) and
  `ucontrol_merge0_olink`'s latch. Checked so far: **item 27 fails as a capture at `ucontrol_merge0_olink`** (2 of 4
  answers, then quiet), where no single-route race fails in the same search range; fcsel3m seed 2 at
  `ulink_n_index_11` stage 0 returns a spurious first answer (106, then 111, 170 for want 111, 170, 350). These rest on
  the old checks; farm c_margin_all2 reruns all classes with the fixes below on items 28, 25, 27, 26, fcsel0 s24,
  fcsel1 s24, fcsel3m s2/s24.
- **Checker fixes that change what is reported (all in `tools/margin`, `tools/huff/envcheck.py`):** (1) runs where no
  20 ps runt filter is consistent with the delay windows are not behaviours and no longer count as failures; (2) a
  run where only the simulated harness broke the protocol (it released data on an acknowledge that then glitched) is
  re-run with a harness that holds data until its next request; (3) envcheck's "request low at the end" was stronger
  than the Spec; a run where your kernel acknowledged a and b but never start and stopped is now reported as
  PHYSICAL: a real harness hangs, but the frozen Spec is vacuous there (A proved it: `SpecWF.env_unsat_partial_ack`).
  Item 25 shows such hangs from steer-condition races without the filter.
- **Livelocks.** `simx --periodic` recognises a run that repeats for ever without answering; the tool reports it on its
  own line (liveness). On gcd_ps it finds the 0.36 livelock with period 79 ps, the period A's Lean proof found.
- **First race in picoseconds (tool: `tools/margin/explain.py`, run.sh now writes `explain_*.txt` for every reported
  race).** item 25 (sdf e001dc27), the race the adversary breaks first without the filter: latch
  `ulink_n_falseResult_3.many.stage[0]` lat.pair[12] (SLICE_X14Y55.A6). Common launch: that stage's `ctl` output
  (SLICE_X16Y38.A6). Path A, ctl -> the latch's enable pin: 1 LUT + 6 routing arcs, 550 ps at the prjxray fast-band
  midpoint (1243 slow-band). Path B, ctl -> 3 LUTs -> the kernel's input acknowledge (a_ack, SLICE_X17Y32.A6) -> the
  harness puts the next input on the bus -> 8 routing arcs -> the same latch's data pin: 1745 ps (4174), with the
  harness taking 1 ps. Slack +1196 ps = 8x the 8.5 % ring error (+838 ps at the worst in-band split). So it is a hold
  race through your harness: the kernel acknowledges its input before the latch holding it has closed, and only a
  harness that changes the data within about 1 ns of that acknowledge can break it. Formal's Spec allows a 0 ps
  harness; your clocked bench does not. Does any rule of yours look at a_ack against that latch's close? The same
  form for items 28, 26, 27 and fcsel3m s1/s2/s24 is on the farm (c_explain1); nominal-SDF slacks next (prjxray band
  midpoints for now).
- Not covered: two independent slow routes outside one cone, the slow corner, kappa_lo (none for any build).

## A14. Where the board sits in the band, and which measurement decides it. LUT vs routing: no August measurement separates them. CARRY/F7: no August measurement places it. Rings and kernels disagree by the same amount in both models, cause unknown (shard A, 2026-11-17 20:33 UTC, corrected 20:38; simulation, untrusted)
This answers PROGRAM ("Research says 0.22 to 0.29 and you said 0.75 to 0.9: say which measurement decides"). It also
records A13, which until now was only in JOURNAL.md (18:28; C42 cites it).
The data are the MEASURED August bitstreams (research/board/aug/builds, decoded by formal; names come from
tools-A/board/aug_synth.py) and the 128 August rings (research/board/ro_many_aug).
b is a position in each model's own [FAST_MIN, SLOW_MAX], so b values from the two models are not comparable as numbers.
In formal's arcs (build_net.py), the measured delays sit at:

| measurement | formal, one b | research, one b (yours) |
|---|---|---|
| collatz per iteration (board 92.7 ns) | 0.387 | 0.222 (full stack) |
| collatz64 per iteration (117.9 ns) | 0.383 | |
| gcd: (2^31-1, 2^31-2) minus (1, 1), 11.70 us; per-coefficient fit 0.387-0.405 | 0.396 | |
| ipow per iteration (60.85 ns; DSP48E1 decoded) | 0.409 | |
| isprime, n = 97 / 1009 minus n = 2 (8.1 / 40.3 us) | 0.389 / 0.388 | |
| 128 rings, median (p05 / p95) | **0.465** (0.420 / 0.512) | **0.288** (+-1.8 %) |

- **Kernels vs rings.** In both models the rings sit higher: +0.078 in formal's, +0.066 in yours. The kernels agree with
  each other to 0.026 (five kernels: 0.383-0.409; ipow and isprime added 20:52,
  out/aug_board/ipow_isprime.txt). The DSP band has no effect on ipow's per-iteration time (B_DSP 0 vs 1: 60.31 ns
  both), so it is not placed either, like CARRY/F7. Your RC-tree model fits the rings more tightly (per-ring spread 1.8 % vs formal's ~5 %), so for
  absolute LUT and wire delay it is the more faithful of the two. Formal's arcs are ~20 % faster in absolute terms.
- **LUT vs routing (b_lut for LUT cell arcs, b_route for pips and site hops; scale_net.py B_LUT).** Each kernel is linear
  in the two: per-iteration = t0 + aL b_lut + aR b_route, fitted from three simx runs. The LUT share of the span is
  0.61 / 0.64 / 0.66 for the kernels and 0.69 for the rings (p05-p95 0.62-0.77). That is nearly the same mix, so these
  measurements cannot tell the two bands apart:
  - Kernels alone give one line: b_lut 0.3 -> b_route 0.53-0.56; b_lut 0.4 -> b_route 0.35-0.39.
  - Rings alone, bootstrap 90 %: b_lut 0.35-0.43, b_route 0.55-0.72. The rms error falls from ~5 % to 3.0 %. The high
    b_route probably absorbs routing that formal underprices: 52k pips with no prjxray record are taken as 0 ps.
  - **No single pair fits both.** At the rings' pair, the kernels come out ~10 % slow (collatz 102.0 vs 92.7 ns).
    The joint fit (0.575, 0.092) leaves the rings at 5.9 % rms and the kernels up to 2.8 % off.
  - So the ring/kernel gap is not a LUT-vs-routing split.
- **WITHDRAWN 20:38: the rise/fall candidate.** The first version of this entry said every kernel delay LUT is a
  bd_delay FASTRISE (OR) stage. That came from a misread INIT. The routed cells are LUT1 buffers: INIT 2'b10, A1
  unconnected, e.g. uselect0.udly.chain.g[9].u. The chains are SYMMETRIC in collatz, collatz64, gcd, xorshift, ipow,
  isprime, gcd_ps, gcd_hw and ro_link_ps. A four-phase cycle therefore pays both edges through them, as a ring does,
  and an edge difference would not separate rings from kernels. The ring/kernel gap is UNEXPLAINED. Untested
  candidates:
  - load and routing that only the rings have (each ring node also drives the BUFG mux);
  - the measurement path;
  - a global difference between the ring run and the kernel runs (temperature or voltage on the day).
- **Added 20:57: the same stage is ~9 % slower in the ring build than in the kernels.**
  - In formal's arcs a ring stage and a kernel delay-chain stage are the same thing: median FAST_MIN LUT arc 154 ps and
    routing 38 ps (mean 55-61) in collatz, gcd and the rings alike (chainstage.py).
  - The rings' excess over the model at b = 0.39 is proportional to length: x1.088-1.095, ~74 ps per stage at 7, 15,
    31 and 63 links. It is per stage, not a readout constant.
  - Splitting each kernel into its delay chains and the rest (scale_net CHAIN / B_CHAIN), the four kernels fit best
    with the chains at b 0.35 and the rest at 0.52 (errors <= 0.9 %).
  - Forcing the chains to the rings' 0.465 needs the rest at 0.19 and leaves errors up to 2.7 %. So the kernel data do
    not support "the chains run as slowly as the ring stages".
  - Same stage, different speed: the leading explanation is a difference between the two builds or sessions (ring
    build Aug 23 ~21:15 local, kernels Aug 24), not between kinds of stage. Not shown.
  - Data: out/aug_board/chain_vs_rest.txt.
  Neither model can represent a rise/fall difference anyway: the August collatz SDF has rise = fall on all 54,592
  entries.
- **CARRY/F7 (A13).** With LUT and routing at 0.39, moving CARRY4 and MUXF7/F8 over {0.2, 0.39, 1.0} changes collatz and
  collatz64 per-iteration time by 0.00 ns. The cycle is set by the matched delays, and the carry chains only have to
  settle inside them. No August measurement places this band, so the CARRY band of ~0.9 at which C38 / C35's races
  close cannot be confirmed or ruled out by the board data in hand.

**PROGRAM's "0.22-0.29 vs 0.75-0.9".**
- Formal's 0.75-0.9 is WITHDRAWN. It came from my tightened REBUILDS of the August kernels (A11). Their tighten loops
  did not converge, so their delay sizes differ from the bitstreams that were measured.
- On the measured bitstreams, formal says 0.38-0.41 and research says 0.22-0.29. These are the same silicon in two
  coordinate systems: formal's arcs are ~20 % faster in absolute terms than research's RC-tree arcs, so the same ns
  sit higher in formal's band.
- The two models agree on both shapes:
  - kernels lower than rings;
  - one b fits every kernel, within 0.026 in formal's coordinates and 1 % in research's.
- "A kernel is mostly carry chains where a ring has none" does not explain the difference. Moving CARRY/F7 over its
  whole band changes no kernel's per-iteration time (0.00 ns). The kernels' per-iteration time is ~73 % delay-chain
  LUT stages, the same stages the rings are made of.

**Rows for research/SIM-VS-BOARD.md** (formal's simx, the measured August bitstreams, one b = 0.39 for every arc;
F / S = all arcs at FAST_MIN / SLOW_MAX):

| kernel | measured | formal F | formal S | formal at b 0.39 | error |
|---|---|---|---|---|---|
| collatz, ns / iteration | 92.73 | 50.35 | 159.81 | 93.04 | +0.3 % |
| collatz64, ns / iteration | 117.89 | 64.43 | 204.16 | 118.92 | +0.9 % |
| gcd, (2^31-1, 2^31-2) minus (1, 1), ns | 11695 | 6305 | 19911 | 11611 | -0.7 % |
| ipow, ns / iteration | 60.85 | 32.41 | 102.16 | 59.61 | -2.0 % |
| isprime, n 97 minus n 2, ns | 8100 | 4411 | 13901 | 8112 | +0.1 % |
| isprime, n 1009 minus n 2, ns | 40335 | 21972 | 69250 | 40410 | +0.2 % |
| 128 rings, median period error | - | - | - | - | +8.8 % (rings slower) |

(xorshift is left out: the August README marks 25 of its board logs match=NO against the bitstream.)

**Which measurement decides:**
1. **For kernel margins: the kernel loop times, not the rings.** The kernel loop times share the kernels' edge mix and
   placement style; the rings do not. Until (2) is done, reading kernel delays at the ring b over-states their delays
   (safe for request delays, unsafe for data paths).
2. **The ring/kernel gap: a kernel and the rings measured in ONE session, with NO new build.** Load ro_many_top.bit
   and run ro_many_measure.py, then load collatz_bench_gen.bit and run its loop sweep, back to back on the same board
   within minutes (both bitstreams are on claude/research). If the rings still read ~9 % slower per stage than
   collatz's chains, the cause is in the builds; if not, it was the day. Also useful: plus a ring whose
   nodes drive nothing but the next stage (rules out the readout load). research/board/aug/builds/ro_link_ps, a ring of
   bd_links that WAS built and has a routed JSON, is the closest thing in hand: a handshake ring with the kernels'
   cells. If it has a board period, formal can place it next. **ASK:** the ro_link_ps bitstream is on claude/research,
   but no board laps are. cells/hw/ro_link_fit.py reads build/hw/ro_link_sweep, and neither the August logs nor
   research/data hold it. If the owner's August sweep output (the "ring N: S stages L laps X ns/lap" lines) still
   exists, please push it. It is the only measurement in hand that crosses rings and kernels.
3. **LUT vs routing: rings whose routing share differs.** For example, the same N with stages forced one per tile
   against packed four per slice. That moves the LUT share from ~0.7 to ~0.4 or ~0.9, enough leverage for a two-band fit.
4. **CARRY/F7: a CARRY4 delay line or ring (C42),** or a kernel whose request path waits on a carry chain.

Files: tools-A/board/{ring_period.py, scale_net.py (B_LUT), twoband.sh, loop_latency.py, gcd_latency.py, aug_synth.py};
outputs tools-A/board/out/aug_board/ and ring_band.txt. Toolchain: none (decoded from the measured FASMs; prjxray arcs).
Not shown: (a) why rings and kernels differ; (b) anything about the August builds' sizes at other routes;
(c) a b with RC on all corners (RC_ALL changed the rings by little, A13).

## A12. REQUEST for the August board builds (shard A, 2026-11-17): the yosys and routed JSONs
For PROGRAM's "where does the board sit in the delay band?": formal's simulator decodes the FASM but names the kernel's
boundary (request, acknowledges, data buses) from \`<k>_bench_gen.json\` + \`<k>_bench_gen_routed.json\` +
\`build/gen/<k>_kernel_bench.v\`, \`<k>_bench_gen.v\`. Only FASM and SDF were pushed. If the owner's August build
directories still hold those four files per kernel, please push them next to the FASMs. Until then A is matching the
SDF's instance names to sites from the PS7 outwards (slower, may not be complete).

Note from shard C (2026-11-17 18:15 UTC), for A: the routed JSONs (plus .bit, .fasm, .sdf, .xdc, pnr/synth logs) of the
MEASURED August bench builds are already on claude/research under research/board/aug/builds/<k>_bench_gen/ (committed
2026-11-04; its README pairs every board log with its bitstream, match=yes for collatz, collatz64, gcd_bench_gen, ipow,
isprime). The yosys synth JSON and the gen Verilog are not there. ipow now decodes (C39: DSP48E1 path, run.sh picks it up).

## A11. Your draw model's band position looks ~35 % too fast against the gcd board data: the decoded August gcd design reproduces all 20 measured latencies at b = 0.39 of [FAST_MIN, SLOW_MAX] (shard A, 2026-11-16; simulation, untrusted)
**WITHDRAWN IN PART (A, 2026-11-17 ~04 UTC): the band-position claim does not hold up.** The same method on two
more August designs rebuilt from their measuring commits gives b = 0.745 for collatz (1b81a36f2; its tighten loop
converged: 35.7 ns of matched delay) and b = -0.03 for xorshift (648f3d106; loop did not converge, untightened
estimate shipped; the board's 49.6 ns per round is BELOW the simulated all-FAST_MIN 53.4 ns). gcd's 0.39 came from an
untightened rebuild too. The spread (-0.03 to 0.75) tracks whether each rebuild's matched-delay sizes match the
measured bitstream's, which were never archived; so these rebuilds cannot pin the board's band position, and "your
draws are ~25 % too fast" is NOT supported. What stands: within one design (gcd), the decoded circuit reproduces the
board's relative costs of its four loops and all 20 per-input latencies to 0.9 % RMS with one scale factor. Pinning b
needs a bitstream that formal has AND that ran on the board (the ASK below stands).
**Added: collatz64** (1b81a36f2, tighten loop converged, 41.5 ns matched delay): board 117.7 ns/step vs sim 44.7 /
141.7 -> **b = 0.752**. So the two rebuilds whose tighten loops converged (collatz 0.745, collatz64 0.752) agree; the
two that shipped bdc's untightened estimate (longer chains than a tightened build) give lower b (gcd 0.39, xorshift
-0.03), the direction expected if the measured August builds were tightened. A tentative reading only: b ~ 0.75 of
[FAST_MIN, SLOW_MAX] for kernels whose sizes plausibly match, i.e. the board slower than your U[0.20, 0.31] draws;
still rebuilds with today's toolchain, not the measured bits.

For PROGRAM's "the board decides": how close is formal's simulator (simx on the circuit decoded from the bitstream) to
the board? The only per-input board data: your `cells/hw/gcd_cost_results.tsv` (ca475ffdb, 24 pairs x 3 x 200 calls,
measured on the August `gcd_bench_gen.bit`, route and sizes not archived).
- Rebuilt gcd_bench_gen from ca475ffdb with today's cloud toolchain (its build_bench.sh, default and BD_SKIP_RULE_E=1:
  both ship bdc's untightened estimate, SDF dee2e292 / FASM 878c0858); decoded; each pair simulated alone with every
  arc at FAST_MIN and at SLOW_MAX; kernel latency = out0 request rise - request rise.
- Your four per-iteration costs (k 126.8, pre-ctz 124.3, main 158.0, inner ctz 114.9 ns, refitted from latmin/latmax)
  fall at b = 0.397, 0.398, 0.388, 0.396 of the simulated [FAST_MIN, SLOW_MAX] range: **one b for all four loops**.
  One b and one harness offset fitted to all 20 pairs that ran: **b = 0.392, offset 36 ns, every input within 2.6 %
  (RMS 0.9 %)**. With b = 0.288 (ring128) the fit is RMS 39 %, max 117 %.
- So on this design the decoded circuit's timing shape matches the board to under 1 %, and the board sits near 0.39
  of the prjxray band, above your draw model's U[0.20, 0.31]. If that holds on today's builds, your draws (and C's)
  are ~25 % too fast, which matters for every race whose two sides scale differently (chains vs routing).
- Also: 4 pre-ctz-heavy pairs ((3145728,5), (163840,7), (6291456,11), (2097152,1)) misbehave in formal's model with
  every arc at SLOW_MAX (a stream of wrong outputs for one pair); at b ~ 0.39 the board returns them correctly.
- **Caveats:** a rebuild, not the measured bitstream (the sizes are what that commit ships today; the August
  toolchain may have converged to tighter ones); linear interpolation between the band ends; one design.
- **ASK:** the August gcd_bench_gen .bit/.fasm or its sizes; or a board run of any bitstream formal has (gcd_ps
  e6bb4aec, or your items 27-33) on fixed vectors with per-call latency. Files: `formal/tools-A/board/` (gcd_latency.py,
  out/).

## A10. Your rule-E question on fcsel1 / fcsel2 ("are the rows at the muxes real?"): in formal's model the mux races are the last to fail, not the first (shard A, 2026-11-16; search, checked; NOT yet in picoseconds)
Farm fm_a_selrace_fcsel: fcsel2 s1 (sdf 5b538ca5), fcsel2 s2 (fb1efc41, your E -114 ps at umux0), fcsel1 s24 (afab5445),
rebuilt = yours. Sweep of every combinational LUT feeding storage (selrun.sh; one route slow at a time, g = 1, corner 0,
vectors 27/703/77031; failures re-run and accepted by both checkers):
- no such race fails below kappa 0.45 on any of the three (435 / 433 / 432 active pins);
- the first that fail (0.66-0.75) are `ucond_br5` reading the comparator `ucmpi2.uz_n36` late, not a mux; also some
  partial-ack hangs at 0.64-0.79 that formal's frozen statement cannot even see (JOURNAL 2026-11-16, SpecWF.lean);
- `umux0`'s data LUTs (`umux0.udat.pair[*]`) first fail at **0.85-0.88** on all three routes.
For comparison, on the same routes the latch races of C10 fail at 0.21-0.32, and those are input-boundary races (A9).
**The same sweep on the board candidates and the select-link minimal pair** (farm fm_a_selrace_board; SDFs a9bdac53,
6982a9d5, 2f825834, 98809562, acc06847 = yours):
| build | combinational race below 0.45? | first combinational failure above (checked) |
|---|---|---|
| item 27 xorshift | none (408 active pins) | 0.56: `ucond_br6` reads comparator `ucmpi1.uz_n41` late |
| item 23 xorshift | none (362) | 0.56: `ucond_br6` reads `ucmpi1.uz_n38` late |
| item 26 collatz64 | none (429) | 0.75: `umux0.udat.pair[0]` reads its select from `ulink_n14__0.lat.odd` late (a true select race) |
| **BAD nc64_7** (select link ulink_n14__1 19 -> 10) | **yes, 0.36**: `uaddi1.udly.chain.g[11]` (the adder's matched delay) reads `ulink_n13.ctl` late; 27/703/77031 -> 111/42/478 | -- |
| pc64_7 (its good neighbour) | none (408) | 0.69: `ucond_br7` reads `ucmpi2.uz_n37` late |
The minimal pair separates here too, but nc64_7's combinational race is NOT at the shortened select link: it is the
adder's delay line seeing ulink_n13's controller late, the link of nc64_7's latch race (C8/C9).
So formal does not confirm rule E's negative rows as near failures: by the time a single late route into umux0 breaks
the result, every other race has long failed. **Caveats:** a kappa is a ratio within formal's search, not a measured
margin (owner, 2026-11-16); the picosecond form of the umux0 races (which pin, select or data; the slack from the
split) is not done yet; two slow routes at once and the slow corner are not covered. Files:
`origin/claude/cluster:results/fm_a_selrace_fcsel/<1..3>/{sel,sel95}/`.

## A9. On the other collatz routes the race formal breaks first is at the kernel's INPUT: a latch still closing when the operand may change (shard A, 2026-11-16; search + trace, untrusted)
**Audit correction (T124b, 2026-11-16 ~06:30; accepted by A):** every picosecond slack in A8 and A9 is the smallest
gap among the arrivals that formal's three vectors (27, 703, 77031) make, so only the low operand bits (<= 17) are
exercised. They are not slacks over all bits. The audit's static check over all 32 bits, at FAST_MIN, finds smaller ones:
fcsel0 s24 177 ps (lat.pair[26]; pair[16] 330 ps), and on **item 28 an input race of 771 ps (bit 19) that is smaller
than ulink_n13's 929 ps** in the audit's own rule H. So A8's "the first race on item 28 is entirely inside the
kernel" is withdrawn: over all bits, item 28 also has an input-boundary race, and it comes first. All of these slacks
stay positive, and the input ones assume a sender with zero data hold (the board's PS is µs slow). The mechanisms named
below are CONFIRMED by the audit.

The latch-enable race that C10 and A8 list at `ulink_n_falseResult_3.many.stage[0]` (fcsel3m seeds 24 and 7, fcsel0
seed 24, and by the same link probably the other C10 rows and item 25's w 0 row) has its DATA pin on the kernel's
input bus: the stage-0 latch bits read `n`'s data nodes (`a_data` in the bench boundary) directly. Traced in formal's
simulation at the mid of the fast window, no slow arc, research's vectors (`race_ps.py`, boundary flip times):
| route | stage-0 ctl closes | enable reaches the latch bit | kernel drops a_ack | env changes the operand | new bit at the latch | slack |
|---|---|---|---|---|---|---|
| fcsel3m s24 (`lat.pair[16]` LUT5) | 2,174,155 | +725 ps | +977 ps | +978 ps | +1,376 ps | **651 ps** (1,644 at slow mid) |
| fcsel3m s7 (`lat.pair[6]` LUT6) | 410,731 | +864 ps | +1,405 ps | +1,406 ps | +1,781 ps | **917 ps** (2,393 at slow mid) |
| fcsel0 s24 (`lat.pair[16]` LUT5) | -- | -- | -- | -- | -- | 616 ps (data from a_data; not broken down) |
- **Which two signals race.** Split: the stage-0 controller's close. (Traced, not inferred: in both runs the a_ack fall's flip-by-flip cause chain passes through that close, at 2,174,155 and 410,731 ps.) Path 1: its enable route to the latch bit (725-864
  ps, all routing plus the LUT pin). Path 2: the kernel's acknowledge falling (the close propagated to `a_ack`), then
  the environment changing the operand, then the bit's route to the latch. The environment in formal's statement
  (Spec.Env, four-phase with the "broad" data rule) may change data the moment the acknowledge falls; the runs above
  do exactly that (1 ps later).
- **What it means for the board.** Your PS harness writes the next operand only after it has read the result, microseconds
  later, so on the board path 2 is µs long and this race cannot fail. These kappas (0.27, 0.28, 0.22) are therefore
  margins against a zero-hold sender, not against the board. Item 28's ulink_n13 race (A8) is inside the kernel, but over all
  operand bits item 28 also has an input race that comes first (audit T124b, above).
- **What it means for bdc.** Under the four-phase bundled-data contract the kernel acknowledges `n` while one of the
  latches that holds `n` can still be open at a bit: it relies on the sender keeping data ~0.6-0.9 ns after the
  acknowledge falls. A pipelined or hardware sender would break it. Your rule H looks at a link's close against its
  upstream; does any rule of yours look at the kernel's input boundary (the acknowledge to the environment against
  the slowest enable bit of every latch reading the input bus)?
- **Added 04:01 UTC: the other two board candidates, same method** (local rebuilds, SDF e001dc27 / 6982a9d5 = yours):
  | build | latch | split | path 1 (enable) | path 2 (next data) | slack, fast mid / slow mid |
  |---|---|---|---|---|---|
  | item 25 (collatz, w 0 only) | `ulink_n_falseResult_3` stage 0 `lat.pair[12]` | (through the environment: data pins on a_data) | -- | sender's next operand after a_ack falls | **1,193 ps** / 2,931 ps (input boundary, as above) |
  | item 26 (collatz64) | `ulink_n13.lat.pair[6]` (LUT5) | `ulink_n13.ctl` | 961 ps (cells 242 + routing 719) | 2,170 ps (cells 1,360 + routing 810): `ulink_n13.uack.chain.g[0..2]` -> `umux1.uya` -> `ulink_n_falseResult_5` stage 1 ctl -> its `lat.pair[6]` -> `umux1.udat.pair[6]` | **1,209 ps** / 3,240 ps |
  Item 26's race is item 28's race (the same links, n13 against falseResult_5 stage 1 through umux1), with a longer
  enable route (719 ps of routing against 354 on item 28). Both are inside the kernel; your rule H is the check.
- Not done: the same breakdown for the other C10 routes; whether formal should report these apart (C's
  boundary class E). Files: `formal/tools-A/target/race_ps.py`; numbers from local runs of C's run.sh nets.

## A8. Your collatz board candidate item 28 (fcsel3m seed 20): the race formal finds first is ulink_n13's latch enable against that latch's next data; no select-arrival race short of a very lopsided assignment (shard A, 2026-11-16; search, checked; picoseconds to follow, see the note at the top of this item)
**Audit correction (T124b, 2026-11-16 ~06:30; accepted by A):** every picosecond slack in A8 and A9 is the smallest
gap among the arrivals that formal's three vectors (27, 703, 77031) make, so only the low operand bits (<= 17) are
exercised. They are not slacks over all bits. The audit's static check over all 32 bits, at FAST_MIN, finds smaller ones:
fcsel0 s24 177 ps (lat.pair[26]; pair[16] 330 ps), and on **item 28 an input race of 771 ps (bit 19) that is smaller
than ulink_n13's 929 ps** in the audit's own rule H. So A8's "the first race on item 28 is entirely inside the
kernel" is withdrawn: over all bits, item 28 also has an input-boundary race, and it comes first. All of these slacks
stay positive, and the input ones assume a sender with zero data hold (the board's PS is µs slow). The mechanisms named
below are CONFIRMED by the audit.

**Owner's rule since 03:30 UTC (PROGRAM.md, "A kappa is not a result"): a kappa only ranks races in our search; it
is not a margin of the chip and must not be read as one, nor used to call one build better than another. The
picosecond form of this race (the two paths from their split, cells and routing apart, slack at the nominal SDF, your
rule row for it, the slack as a multiple of the measured 8.5 % ring error) is the next step; until then read the
kappa column below only as "which race our adversary breaks first".**
**The race, in picoseconds (item 28's route; formal's decoded net, prjxray arcs, uniform corner, no slow class, w 0;
`formal/tools-A/target/race_ps.py`, untrusted).** Storage element: `ulink_n13.lat.pair[6]` (LUT6 SLICE_X10Y26.A6;
enable on pin A1, data on A3/A4 from `umux1.udat.pair[6]`). Split (common launch): `ulink_n13.ctl`'s output
(SLICE_X14Y25.C6). Path 1, the enable: ctl -> latch bit pin, 7 hops, no LUT. Path 2, the next data: ctl ->
`ulink_n13.uack.chain.g[0]` -> `umux1.uya` -> `ulink_n_falseResult_5.many.stage[1].u.ctl` -> its `lat.pair[6]` ->
`umux1.udat.pair[6]` -> the latch's data pin (5 LUTs, 39 hops). Smallest gap over the run (3 vectors, 1,262 enable
changes):
| delays | enable path | data path | slack (data after enable) |
|---|---|---|---|
| mid of the FAST window | 607 ps (cells 253 + routing 354) | 1,950 ps (cells 998 + routing 952) | **1,343 ps** |
| mid of the SLOW window | 1,392 ps (591 + 801) | 4,737 ps (2,414 + 2,323) | 3,345 ps |
At the fast mid, the slack is 52 % of the two paths' sum (1,343 / 2,557 ps): about 6x the 8.5 % median ring error
applied to both paths, and more than the "about 1 ns slow" seen on long routes even if all of it landed on the
354 ps of enable routing. The search's kappa is the same fact as a ratio: the enable path at the fast window's top is
726 ps, the data path at its bottom 1,691 ps, so the order flips at kappa = (1691 - 726) / (1691 + 726) = 0.40; the
search's first failure was at 0.42. **Your rule H is the check for this race** (ulink_n13's close against
falseResult_5 stage 1 releasing the next value through umux1; your nc64_7 trace names the same pair of links). Shard C found
your row (farm results/fcsel3m/20, report_rows_nom.txt): **H +1,337 ps** at your nominal SDF (enable 1,241, data 2,628),
and hold_bits min 1,566 ps over 14,656 windows. Formal's 1,343 ps (prjxray fast mid) agrees in size: the two views
see the same slack, and the kappa is only that slack under an all-fast adversary.
Rebuilt from BOARD-QUEUE ## 29's command on formal's farm and here: SDF d86bdde5d557f44fddbf90c24b88809c (= yours), FASM
e4f259409e188d0ff474e02ee69581dc. Shard C's margin tool, exactly C10's settings (vectors n = 27, 703, 77031; single-pin
adversary, g = 1, corner 0; every failure re-run and accepted by both checkers, arbiter rule included: T >= 124-162 ps).
Item 25 was run in the same request with the same settings, for comparison.
| build | sdf | kappa_hi (20 ps filter) | without filter | binding race |
|---|---|---|---|---|
| **item 28 = fcsel3m seed 20** | d86bdde5 | **0.42** | 0.42 | `ulink_n13.lat.pair[6]` reads `ulink_n13.ctl` late (27/703/77031 -> 111/426/606) |
| fcsel3m seed 1 | d7d13c5d | 0.41 | 0.41 | `ulink_n_falseResult_3.many.stage[0]` lat.pair[16] vs its ctl |
| fcsel3m seed 2 | ce8de32a | 0.37 | 0.33 | same link, pair[12] (w 20) / pair[16] (w 0) |
| fcsel3m seed 24 | e2d7c95d | **0.27** | 0.27 | same link, pair[16]; w 0 also `ulink_n10__3.lat.pair[20]` vs `ulink_n10__3.ctl` |
| fcsel3m seed 7 | 751c6b81 | **0.28** | 0.28 | same link, pair[6] |
| item 25 (nl4, seed 24), same run | e001dc27 | none admissible | 0.42 | same link, pair[12] (as C6/C9) |
- **Reading.** On item 28's own route the first race broken is NOT the falseResult_3 stage-0 enable race of the other
  nl6 routes but the same kind at ulink_n13 (the link of nc64_7's and item 26's races). The kappa varies by 0.15 over
  five routes of this one design, so no comparison with item 25 (one route measured) is made here.
- **Select links.** The tool above only slows routes into storage LUTs, so it cannot see a select reaching the mux DATA
  LUTs late (your rule E, audit T116). Shard A added that sweep (`formal/tools-A/target/selrun.sh`, after run.sh): live
  pins of every combinational LUT that feeds storage, same adversary. Item 28: 431 active pins, **none fails up to
  0.45**. fcsel0 seed 24 (select links at 0): none up to 0.45 either. Pushed to 0.95 on the umux data LUTs only, both
  fail from **0.85**: on fcsel0 a true select race (`umux0.udat.pair[10]` reading the select from `ulink_n14__0.lat.odd`
  late, 27/703/77031 -> 111/108/275, checked), on item 28 a data race (`umux0.udat.pair[12]` reading
  `ulink_n_falseResult_9` stage 1 late). So in formal's model, with one route slow at a time, select arrival is far
  from binding on either build, and select links at 3 vs 0 do not separate. It does not cover two routes slow at
  once, or a slow corner.
- Files: farm `origin/claude/cluster:results/fm_a_margin_fcsel3m/<1..6>/` (kappa_hi.txt, checked.txt, names.txt,
  witness/); select sweep `formal/tools-A/target/out/{item28_fcsel3m_s20,fcsel0_s24}_sel/`.
- **Ask:** does the ulink_n13 trace (witness/command.txt in task 1: the slow arcs are classes.json) replay as a failure
  in your fid GLS? If yes, ulink_n13's latch enable on this route is the thing to look at before item 28 goes to the
  board.

## A7. Your known-bad xorshift build fails in formal's model with NO within-die scatter; the good neighbour does not (shard A, 2026-11-15; search, untrusted)
- Builds: BAD xf2_1 (FASM f2873d4650eb67cb270ada5c9a403421, SDF dc138ea2...) and item 23 (FASM 56434fc4..., SDF
  2f825834...), both rebuilt here from your FOR-FORMAL.md commands, byte-identical to your files. Decoded from the
  FASM (prjxray-db, round trip "invented 0"), boundary named from the yosys/routed JSONs, simulated with prjxray
  bands (transport, w = 0), sequential env, your hold vectors (seed 0x92d68ca2, rounds 3, 4, 8, 5).
- Both are correct at every uniform corner (all arcs at fast min, at mid-band).
- **The race you traced, made adversarial:** ulink_n7's enable from its controller (SLICE_X24Y40.A6) reaches the
  bit-0/1 latch LUTs (SLICE_X24Y40.B5/B6, pin A2) through a 20-pip route. With that route at the top of its fast-corner
  window and every other arc at the bottom (g = 1, κ = 0: inside the prjxray band, no scatter), BAD returns
  1879071104, 1258817536 instead of 2064144800, 2008045182 and then stops answering. **kappa* = 0 for BAD.**
  item 23's same enable route has 6 pips; under the same adversary it is correct at κ = 0, 0.16 and 0.32.
- So this check puts the bad build below the good one and names the failing link (ulink_n7's latch enable). It is
  one race, found by hand from your trace; formal's margin tool (shard C) is what must find it unaided and give
  item 23's own kappa*. Files: formal/tools-A/target/out/{BAD_xf2_1,item23_xorshift_s10}_{cls_n7en,bnd_sim,boundary}.json;
  command: `formal/tools-A/target/simadv_hold.py NET BND_SIM --pairs 2463534242,3 2463534242,4 2463534242,8
  2463534242,5 --corner 0 --kappa 0 --classes CLS --cdefault F --tmax 3000000 --datachange broad --nextreq seq --dfall 1`
  (NET from `make_net_fasm.sh`).

## A6. Your two loop-test rewrites are function-preserving (shard A, 2026-11-15; Lean, standard axioms, check.sh OK)
Inputs (origin/claude/research, read-only; each is exactly `research/tools/fifteen/{pre_dec,pre_eq2}.py`'s output on
`cloud/fixtures/frontend/<k>/comp/handshake_transformed.mlir`, rerun and `cmp`-equal):
| file | md5 | Lean | statement |
|---|---|---|---|
| `research/data/fifteen/xorshift_predec.mlir` | c3c2c89294cb8179033b51e00fc2b14b | `Formal.Rewrite.XorshiftPredec.same_as_original` | for every (seed, n) (every bit pattern, n ≤ 0 and wrap-around included) on which the C returns r, the original graph and the rewritten graph both have complete runs ending with [r] on out0, and every complete run of either (any schedule) ends there |
| `research/data/fifteen/collatz_preeq2.mlir` | 98a5a519a519b1fce11851c9aeec9b34 | `Formal.Rewrite.Collatz.same` | same, for every 32-bit n |
| `research/data/fifteen/collatz64_preeq2.mlir` | 736d600347daa29e7c2128dab10d5008 | `Formal.Rewrite.Collatz64.same` | same, for every 64-bit n (against a hand transcription of collatz64.c, `Collatz64.P`, checked on 27 -> 111) |
- The arithmetic you argued in the scripts' docstrings is what Lean needed, nothing more: xorshift: n >s 0 at loop
  entry and 1 <=s i <=s n inside the loop (`XorshiftPredec.Is`); collatz: `n' == 1 <=> n == 2` for every width
  w >= 3 (`Formal.Rewrite.Eq2.collatz_eq2`). It is FALSE at w = 2 (n = -2: -2 >> 1 = -1), so do not reuse pre_eq2 on
  a narrower type.
- **Every input (added 18:07 UTC).** xorshift: the C returns on every input (`XorshiftPredec.kC_total`), so
  `same_all` gives one value for both graphs on every (seed, n). collatz / collatz64: where the C never returns
  (n = 0, negative cycles), neither graph ever completes a run (`Collatz.same_div`, `Collatz64.same_div`; generic
  lemma `Formal.Rewrite.Diverge.sim_div`). So before and after agree on every input, for all three.
- **Scope.** Token level: the graphs dfimport reads from your MLIR with bdc's own parser and fusion plan; not the
  routed circuit, delays or cells (that is the margin tool's job).
- Reproduce: `formal/tools-A/rewrite/gen.sh`, then
  `cd formal && ./check.sh $(cd lean && ls Formal/Rewrite/*.lean)` (1,467 declarations, standard axioms).

## C10. Shortened-select collatz builds: kappa_hi 0.21-0.32, all at ulink_n_falseResult_3 stage 0 (shard C, 2026-11-15 ~23 UTC; search, checked)

**Correction (shard C, 2026-11-16, after audit T120/T120b and C's own explain.py):** every race in this item is at
`ulink_n_falseResult_3` stage 0, which holds the kernel's INPUT n. Traced in picoseconds (C11, item 25's route), the
competing path runs ctl -> a_ack -> the harness releasing the next n -> the latch's data pin, with the harness taking 1 ps
(the earliest release formal's Spec allows). So these kappas are input-hold races against a 1-ps host, not races inside
the kernel; with your clocked PS host they are not reachable unless it can release operands within ~1-2 ns of the
acknowledge (the audit's open H_ENV row). Read the numbers below in that light.
Item 25's command with your nl6s{0,1,2} sizes, rebuilt on our farm (SDFs 5b538ca5, fb1efc41, afab5445, bb5fbbdb = the
ones you list; fcsel1 seed 1 4445b56c), vectors n = 27, 703, 77031; every failure re-run and accepted by both checkers
(arbiter rule included):
| build | kappa_hi (20 ps filter) | without filter | binding race |
|---|---|---|---|
| fcsel2 seed 1 | 0.22 | 0.21 | `ulink_n_falseResult_3.many.stage[0]` lat.pair[4] (pair[10] w/o filter) reads that stage's ctl late |
| fcsel2 seed 2 | 0.27 | 0.27 | same link, lat.pair[12] |
| fcsel1 seed 24 | 0.32 | 0.32 | same link, lat.pair[10] |
| fcsel1 seed 1 | 0.31 | 0.31 | same link, lat.pair[6] |
| fcsel0 seed 24 | 0.22 | 0.22 | same link, lat.pair[16] |
| fcsel2 seed 24 | -- | -- | our decoder refused the build (a flop configuration, AFF.ZRST, not modelled) |
For reference item 25 (nl4, select links unshortened): no checked failure with the filter, 0.42 without, at the SAME
link. gcd_ps: 0.40. **Reading:** the races that set these margins are not at the select muxes your rule E flags: they
are the latch bits of ulink_n_falseResult_3 stage 0 seeing their own enable late (the class of BAD xf2_1 and nc64_7).
Shortening the selects moved this race from ~0.42 to 0.21-0.32 (not a minimal pair: nl4 and nl6 sizes differ
elsewhere too). Single-pin search: a two-route failure could be lower. Files: `formal/tools/margin/out/farm_fcsel*/`.

## C9. Names for C6/C8, and arbiters checked (shard C, 2026-11-15 ~23 UTC; search, checked)
Rerun with the bench arbiters named: every checked failing run also satisfies the arbiter rule (state settles within
T = 131-206 ps of its last input change), and every kappa_hi is unchanged. Instance names (routed JSON NEXTPNR_BEL):
- **item 26 (collatz64, 0.26):** `ulink_n13.lat.pair[6]` (LUT5 and LUT6) reads its enable from `ulink_n13.ctl` late:
  a latch-enable race at ulink_n13, **the same link as the known-bad nc64_7** (whose race at 0.05 is
  `ulink_n13.lat.pair[2]` reading `ulink_n13.ctl`). Other failing rows on item 26: ulink_n_falseResult_3 stage[0]
  latch pairs (0.30-0.33).
- **item 25 (collatz, 0.42 without the runt filter):** `ulink_n_falseResult_3.many.stage[0].u.lat.pair[12]` (and pairs
  8/10/16) reading `ulink_n_falseResult_3...stage[0].u.ctl` late.
- **pc64_7 (0.39):** `ulink_n_falseResult_7.many.stage[0].u.ctl` (its own feedback): quiet deadlock.
- nc64_7 also fails at 0.31 with the runt filter at `ulink_n14__1.many.stage[1].u.ctl` (the select line you shortened).
So in all four collatz builds the binding race is a link's latch bits seeing that link's controller (enable) late;
item 26 carries nc64_7's link at a larger but still small margin. Files: `formal/tools/margin/out/farm_<build>/names.txt`.

## C8. collatz64 item 26 (board candidate) breaks at kappa = 0.26 in our model; the minimal pair separates (shard C, 2026-11-15 22 UTC; search, checked)
Rebuilt from your FOR-FORMAL commands on our farm (SDF 6982a9d5 / 98809562 / acc06847 = yours), margin tool, vectors
n = 27, 703, 77031. Every failure below re-run with a dump and passed both independent checkers (every gate relation,
every delay inside the prjxray band at g = 1 with within-die scatter kappa, the 20 ps runt rule where used; the
four-phase environment). Arbiter timing (H_ARB) is not checked on bench builds yet.
- **item 26 (collatz64, pre_eq2, h2 pads, seed 25): kappa_hi = 0.26.** Race: decoded LUT SLICE_X20Y41.B5, pin 1, its
  route from SLICE_X22Y40.C6 late (the 10-ish route arcs at (1+k)·FAST_MAX, everything else at (1-k)·FAST_MIN, corner
  0): 27 -> 175, 703 -> 42, 77031 -> 158 (want 111, 170, 350). Same LUT's B6 fails at 0.30. For comparison gcd_ps: 0.40.
- **BAD nc64_7: 0.05** (w = 0; 0.31 with the runt filter), **pc64_7: 0.39**: the minimal pair separates; nc64_7's race
  is SLICE_X22Y45.A5 pin 0 from SLICE_X20Y39.A6.
Files: `formal/tools/margin/out/farm_item26_collatz64_s25/` (kappa_hi.txt, checked.txt, witness/command.txt +
classes.json = the slow arcs). **Asks:** which cells are SLICE_X20Y41.B5/B6 and SLICE_X22Y40.C6 (NEXTPNR_BEL in your
routed JSON); does the trace (command.txt's delay rule) replay as a failure in your fid GLS? If yes, item 26 should
not go to the board before that link is fixed.

## C7. The margin tool runs on your farm, on your routes (shard C, 2026-11-15 ~22 UTC)
From a research farm task (script mentions PEER, so $PEER is a checkout of claude/formal), after your build:
```
B=cells/build/hw/${K}_bench_gen
SIM=simx LATCH=1 W0=1 KLO=0.0 TFULL=25000000 KERNEL=$K PAIRS="27,27 703,703" \
  SYNTH=$B/${K}_bench_gen.json ROUTED=$B/${K}_bench_gen_routed.json \
  KV=cells/build/gen/${K}_kernel_bench.v BV=cells/build/gen/${K}_bench_gen.v \
  bash $PEER/formal/tools/margin/run.sh $B/${K}_bench_gen.fasm $RUNS/m && cp $RUNS/m/{kappa_hi,checked,margins}.txt $OUT/
```
(KERNEL = collatz | collatz64 | xorshift | gcd; PAIRS "a,b" per vector, one-operand kernels "n,n"; xorshift e.g.
"0x92d68ca2,3 0x92d68ca2,4". Needs python3, g++ and $TC's prjxray-db.) It ran this way on our farm today: item 25
rebuilt byte-identically and gave the same races as our local run, in 10 min on 8 cores; item 27 in 2.5 min.
Read `kappa_hi.txt`: the smallest within-die scatter kappa at which a CHECKED failing run was found (both checkers
passed); "none" means no single-pin race failed up to KHI (default 0.45). It is a search: kappa_lo (proved safe) is
never claimed. **New result: item 27 (xorshift board candidate, SDF a9bdac53): no single-pin race fails up to 0.45**
(1,199 storage-LUT pins, your 4 hold vectors, with and without the 20 ps runt filter). Item 25: kappa_hi 0.42 (w = 0;
SLICE_X14Y55.A6 pin 2 from SLICE_X16Y38.A6, n = 703 -> 70).

## C6. First margins from the margin tool (shard C, 2026-11-15 ~21 UTC; search, untrusted)
`formal/tools/margin/run.sh` (decode the FASM with prjxray bands; every live pin of every storage LUT, latches included,
made slow (1+kappa)·FAST_MAX on its route while every other arc is (1-kappa)·FAST_MIN, corner 0, g = 1; C++ simulator,
bisection on kappa; failing runs re-checked by an independent gate checker and the env checker). Results in
`formal/tools/margin/out/<build>/`. "kappa" = within-die scatter at which one admissible delay assignment breaks the build.
| build | fasm md5 | result | race (decoded site names) |
|---|---|---|---|
| BAD_xf2_1 | f2873d46 | **fails at kappa = 0** (wrong value: rounds 8 returns the 4-round value) | SLICE_X24Y40.B6/B5 pin 1 = your ulink_n7 latch bits 1/0 reading the enable from SLICE_X24Y40.A6 late; a 3rd at 0.08 (SLICE_X24Y51.B5 pin 3, same enable) |
| item23_xorshift_s10 (good neighbour) | 56434fc4 | **no single-pin race fails up to 0.45** (1,239 pins; your hold vectors) | -- |
| item25_collatz_s24 | c6404633 | **wrong answer at kappa = 0.44** without runt filter (n = 703 -> 99, want 170), both checkers pass; correct at 0.32 on this race; 0.36-0.40 undecided | SLICE_X16Y57.A5 pin 3, route from SLICE_X16Y38.A6 (10 arcs). (Four other pins fed by SLICE_X16Y38.A6 fail in our w = 20 search at 0.36-0.45, but those runs are NOT admissible: our simulator's runt filter skipped pulse chains longer than the bands allow; disregard them.) |
| gcd_ps_e6bb4aec (reference) | 2dbf962d | 0.36 (livelock, Lean-refuted), 0.40, 0.44: all three known races re-found by the full sweep (16,990 pins, 23 min on 4 cores); no new one | SLICE_X16Y21.A6 pin 0 (merge4 ua2 reads its fork) |
**Asks:** (1) which cells are SLICE_X16Y38.A6 and SLICE_X16Y57.A5 in item 25 (your routed JSON's NEXTPNR_BEL), and does
the 703 -> 99 trace replay in your fid GLS (the witness command and the slow-arc list are in
`formal/tools/margin/out/item25_collatz_s24/`); (2) the bench's arbiters as cells (we do not check H_ARB on bench builds
yet). Not covered by the tool yet: two routes slow at once, the slow corner, inactive pins on other vectors.

## C5. REQUEST for the margin tool (shard C, 2026-11-15): known-bad and known-good builds, and the bench boundary
Formal is building `formal/tools/margin/run.sh BUILD.fasm OUT/` (PROGRAM.md, first section): for a routed build, every
race that can break it at g = 1 (with and without a 20 ps runt filter), the smallest failing within-die scatter kappa*
and its race in your instance names, and a failing delay assignment as a replayable trace. It is checked first on
gcd_ps_e6bb4aec (must re-find kappa = 0.40 and the 0.36 livelock). To check it on your builds we need, per build:
1. build command + `NEXTPNR_SEED` (the cloud/farm toolchain gives the same route), or the files: `.fasm` (or `.bit`),
   yosys JSON, routed JSON, `.xdc`, SDF md5;
2. **known-bad**: the collatz64 select failure and xorshift `xf2_1` your journal names, with the failing vector and
   the corner/scatter at which your GLS fails; **known-good neighbours** (same kernel, passing);
3. the kernel bench's boundary: which ports are the kernel's handshake channels (req/ack/data per channel), how the
   bench drives them (sequential? data setup before req?), and the input vectors to use (full-range ones preferred:
   gcd_ps's 0.40 race only shows on wide operands);
4. then BOARD-QUEUE #28 (xorshift item 27) and the shortened-select candidates as they land.
Put them in `research/FOR-FORMAL.md` (or point to a path on `claude/research`); formal reads it every session.

## 1. The BOARD-QUEUE #1 bitstream cannot carry "every a, b < 2^31" or independent channels (2026-11-01)
- **Finding** (yosys netlist of the target build, `formal/target/BOUNDARY.md`; not a proof): in gcd_hw the kernel's
  three input requests are one net (`gcd_rig.v`'s `bd_fork`: `assign req_out = {N{req}}`), and its operand buses come
  from the rig's 16-entry table with equal bits merged: `a_data` has 18 distinct nets and `a[31]` tied to 0, `b_data`
  20 distinct nets and 7 bits tied to 0.
- **Consequence**: the configured circuit cannot be offered most pairs below 2^31, nor pipelined pairs on independent
  channels. THE theorem is written (formal/lean/Wip/Target/Spec.lean, section 7) for the pairs this wiring can
  represent (the 16 vectors among them), with the shared request as a fork.
- **If the owner wants the full statement**: build and commit a target with a real operand path (gcd_bench or gcd_ps,
  32-bit operand registers, separate channel requests), e.g. as a BOARD-QUEUE item, and name it. The proof is being
  kept generic in the boundary, so a second target should cost the decode, not a new proof.

## C1. Pipelined pairs: gcd_hw's kernel reorders results, or deadlocks (shard C, 2026-11-01)
- **Finding.** With the kernel boundary of Spec.lean (a, b, start on ONE request, `bd_fork`, in_ack = C(acks)) and an
  environment that raises the shared request for pair k+1 as soon as in_ack has fallen for pair k (allowed by THE
  goal and by Spec's `Env`), the kernel accepts pair 2 long before pair 1's result: in the capstone's handshake
  model the input handshake of pair 1 is complete at tick ~140 (unit gate delays), the result at 271-1043. Then:
  * **reordering**: gcd_rig vector 9 (a=0x10000, b=0x1000) then vector 4 (1, 1): out0 gives 1 first, then 4096;
  * **deadlock**: vector 9 twice, or vector 15 (0x400, 0x300) then vector 5 (0x11, 5): no out0 at all.
  A pair that skips the first loop overtakes one that iterates in it (the loop-header control_merges are arbitrated
  merges); two threads in the nested loops block each other at the header muxes (finite storage).
- **This contradicts gcd_rig.v's header** ("the kernel acknowledges `start` only when it is finished"), which
  Spec.lean section 7 currently cites for "the target would not hold two pairs". In the models below start's
  handshake completes at the first link that stores the control token.
- **Evidence.** Lean (kernel, standard axioms): `Formal/Net/PipeGcd.lean` `gcd_hw_pipelined_reorders` (token level,
  the graph bdc emits: a complete run from vector 9 then vector 4 ending with out0 = [1, 4096]).
  `Formal/Net/PipeWit.lean` `gcd_hw_pipelined_reorder_handshake` (the 465-channel CapNet network: every non-source
  cell model, `Held` on every channel, four-phase sources, out0 offers 1 at tick 271 and 4096 at tick 1043): see
  JOURNAL-C for whether it is claimed yet. Simulation only: the deadlocks; random per-node delays 1..4 ticks keep
  both effects (formal/tools/pipe/hwsimgen.py on the generated-netlist model).
- **Not shown.** No delay band and not the bitstream: these are unit-delay (and random-delay) runs of models built
  from bdc's graph and link plan.
- **GLS of the target route (added later the same session).** Research's cells/gls generators (read-only) on
  `formal/target/gcd_hw_03e82630.routed.json.xz` + `.sdf.xz` (nextpnr SDF, md5 6f8b99e6 = the target README's),
  iverilog 12, testbench `formal/tools/pipe/gls/tb_pipe.v` (env_c forced; pair 2 offered as soon as pair 1's input
  handshake is complete), `formal/tools/pipe/gls/run.sh WORKDIR +PIPE=1 +V1=9 +V2=4`:
  9 then 4: the first result is pair 2's gcd (1) and pair 1's never comes; 9 then 9: no result at all; 2 then 4:
  pair 2's result never comes. Sequential controls (PIPE=0) for the same pairs: both results, correct.
  Table: formal/notes/C-pipe-cex.md; acceptance gate (gate.vvp): ANNOTATE_DONE, 0 SDF warnings/errors. With `-DPROBE` (vector 9 twice) the last
  transitions in the design are in umux0/1/2, the first loop's header muxes: the loop the Lean deadlock sits in.
  **Still wanted from research: the same testbench on the board-fidelity stack**, e.g.
  `GLS_SDF=<xray_delay.py SDF> GLS_SDF_FIELD=<corner> GLS_MODEL=fid cells/gls/fid/build_fid.sh <target hw dir> WORK bit`,
  then in WORK: `iverilog -gspecify -DGLS_TRANSPORT_IC [-DPROBE] -I. -o pipe.vvp formal/tools/pipe/gls/tb_pipe.v
  netlist_baked.v cells/gls/prims.v` (check `urig.in_ack`'s wire in nets.map against tb_pipe.v's `IN_ACK`) and
  `vvp pipe.vvp +PIPE=1 +V1=9 +V2=4`, `+V2=9`, and `+PIPE=0` as the control. prjxray is not installed in shard C's
  sandbox.
- **The board as configured is not affected**: gcd_rig's own env (uenv0/uenv1, inside the bitstream) offers the next
  vector only after the result, which is the sequential case (the controls above).
- **For research (to confirm or refute on the target).** Run the fid GLS of `formal/target/gcd_hw_03e82630` with the
  rig's env replaced by a free-running fork env (`env_c = ~in_ack`, e.g. uenv1 as an inverter of in_ack, which is
  `sim.py`'s `noack` negative control) and two vectors queued: 9 then 4 (expect out0 = 1 then 0x1000), and 9 then 9
  (expect a hang). Check also when `start_ack` rises relative to `out0_req` for one vector.
- **For the owner.** The theorem as stated (pipelined environment) is false for this kernel. Options: (a) restrict
  H_ENV to the sequential environment (offer k+1 only after out0's k-th handshake), which is what gcd_rig and
  gcd_bench do; (b) change bdc so a function invocation cannot enter before the previous one leaves (e.g. a
  token-count gate between start and end).

## 2. COUNTEREXAMPLE on the decoded TARGET netlist (simulation, untrusted): pipelined pairs reorder (shard A, 2026-11-01)
This confirms C1 on the netlist decoded from the target's bits, with every arc inside its prjxray band.
- **What**: THE theorem as the owner worded it (the environment may offer pair k+1 as soon as the input handshake of
  pair k completes) is **false for the target bitstream** in an event-driven simulation of the netlist decoded from
  the target's own bits (`formal/tools-A/target/`: decoder from the read-back FASM, every pin arc at one fixed delay
  inside its prjxray band, transport semantics = one behaviour of Spec.lean's `Behaves`).
- **Trace**: pairs (a, b) = (2^19, 2^19) then (3, 5), both representable on the target's operand nets. The shared input
  request rises at 20.0 ns, `start_ack` rises at 141.0 ns (the input handshake of pair 0 completes at 183.3 ns, all
  acks low), pair 1 is offered at 183.3 ns, and out0 delivers **1 at 936.8 ns, then 524288 at 1854.0 ns**: gcd(3,5)
  overtakes gcd(2^19,2^19). Same result at the fast corner (c = 0, fast end), the slow corner (c = 1, slow end), and
  with ±10% and ±20% uniform per-arc scatter. Output: `formal/tools-A/target/out/cex_pipelined_reorder.txt`.
  The mechanism matches shard C's token-level and handshake-level finding (`formal/notes/C-pipe-cex.md`): pair 1 skips
  the k-loop that pair 0 iterates in.
- **gcd_rig.v's header is wrong about the target**: "the kernel acknowledges `start` only when it is finished". In the
  decoded target `start_ack` rises 141 ns after the request, the result 934 ns after. The board rig is still safe,
  because it waits for out0 before the next pair (`gcd_rig.v`'s env is two stages), not because of start_ack.
- **A second, independent requirement**: input data must be held until the channel's acknowledge FALLS ("broad"
  four-phase), not just until it rises ("early"). With the data moved right after req falls (acks still high), pair 0
  never completes (livelock; `out/cex_early_release.txt`); moved at each ack's fall, both pairs are right
  (`out/ok_broad_sequential.txt`).
- **Lean (2026-11-01, later)**: `FormalWit.V9V4.Refute.refuted_range`: ¬ NetCorrect for the decoded target at the
  slow corner with g = 1, κ = 0, for every T ≥ 656 ps and Δo ≤ 2999 ps (vector 9 then vector 4; out0 first = 1).
  So the trace is no longer only a simulation: it is a kernel-checked behaviour of the Spec's model of the decoded
  netlist. Still not shown: that the decoded netlist is the target's configuration beyond H_DECODE (untrusted
  decoder; Python round trip; C's import agrees but shares the walker code, so it is not independent), and research's
  fid GLS with a pipelined env.
- **Test (research, fid GLS)**: drive the target's kernel boundary with a pipelined env (offer pair k+1 when a_ack,
  b_ack and start_ack are all low again), pairs (0x80000, 0x80000) then (3, 5); expect out0 = 1 first.
- **What it means for the board**: nothing new for BOARD-QUEUE #1 as built (its rig is sequential). It means the
  kernel is not a pipelined gcd unit, and any harness that overlaps calls (a PS FSM that issues the next call on
  in_ack) gets results out of order.
- **Rig vectors on the decoded target (07:49, `formal/tools-A/target/out/pipe_*.txt`)**, pipelined env, broad data rule,
  corner 0.5 mid-band: vector 9 then 4 -> out0 [1, 4096] (reordered); vector 9 twice -> quiescent at 349 ns with no
  out0 (deadlock); vector 15 then 5 -> quiescent at 1088 ns, no out0 (deadlock). These are exactly C1's predictions
  from the token and handshake models, now on the netlist decoded from the target's bits.

## 3. Owner decision: how a LUT loop treats runts sets the sequential theorem's κ margin (shard B's result, 2026-11-01)
- **Finding (shard B, JOURNAL-B 09:47-10:20; simulation plus a static Lean bound, `Formal/Cells/Ua1Static.lean`)**: with
  the SEQUENTIAL environment, under the frozen gate model (H_PRIM as Boolean transport: a runt in a LUT feedback loop
  can circulate for ever), the target fails once within-die scatter κ exceeds about 0.155 (g = 1, corner 0.2-0.5):
  one C-element (`ua1` of arbiter 0, SLICE_X2Y18.DLUT) gets a forcing episode shorter than its own loop, the runt
  escapes through one reader (SLICE_X2Y18.CLUT, an OR), and the circuit locks up. With any runt-killing read (a
  reader skipping pulses narrower than ~20 ps, still inside the bands) the same delays are harmless: out0 correct.
  The next storage node would bind only at κ ≈ 0.36.
- **Audit T6 (claude/audit af485141, findings/T6.md)**: the 7 ps runt mechanism is confirmed independently (the
  auditor's own transport simulator on its own decode, flip for flip, every delay inside Adm). Replayed in research's
  fid GLS (7 local arcs changed): the same runt in transport mode; with the GLS's DEFAULT resolver, out0_req pulse
  trains (a four-phase violation) and then a stall at 2 of 3 seeds. So at these delays the failure is not only an
  artefact of the transport semantics. Not yet a Lean counterexample to NetCorrectSeq (only liveness is shown to fail
  in a finite run under transport).
- **What it means**: the sequential theorem's κ margin is ~0.15 under the pessimistic semantics PROGRAM requires, and
  at least ~0.36 (in this evidence) if silicon kills narrow runts. Which applies is a fact about the fabric, so it
  would enter as a named hypothesis, e.g. H_RUNT(w): "a LUT input pulse narrower than w ps is not propagated".
  Stated in Lean as an addition: `Formal/Target/SpecRunt.lean` (`NetCorrectSeqRunt w`, implied by the frozen
  `NetCorrectSeq` for every w, equal to it at w = 0).
- **Test**: research's fid GLS or the board: a C-element loop (bd_ce) driven with a forced episode shorter than its
  loop by a few ps; does the loop settle or keep oscillating? `tools-B/target/` has the delays.
- **Also for the owner (shard A, Spec)**: in the frozen `Adm`, the guard g only widens the global band
  [FAST_MIN/g, SLOW_MAX·g], and at small κ every admissible delay is already inside the corner window, so g has no
  effect there (B's observation). So "the largest g" is not a margin by itself; the margin is a (g, κ) frontier. A fix
  (g scaling the corner window: [(1-κ)·lerp(FAST_MIN,SLOW_MIN,c)/g, (1+κ)·lerp(FAST_MAX,SLOW_MAX,c)·g]) is proposed but
  NOT applied: six B/C files build on the current shape (one claimed lemma, C's `adm_le_dmax`, would become false).
  It needs an audit row and the shards' agreement.
- **APPLIED 2026-11-01 (owner decision 3, PROGRAM.md)** by shard A: `Spec.Adm` is now the g-scaled corner window alone,
  `[(1-κ)·lerp(fmin,smin,c)/g, (1+κ)·lerp(fmax,smax,c)·g]` (no separate band), and `Gate.start` is ⌈(1+κ)·smax·g⌉.
  Fixed: C's SpecSettle (`dmax`/`dmin` now ⌈(1-κ)·fmin/g⌉ ≤ d ≤ ⌈(1+κ)·smax·g⌉, needing `Sane p`, 0 ≤ c ≤ 1 and
  ordered arcs; the old `adm_le_dmax` is false at κ > 0 and is replaced), B's Ua1Static (`lo`/`hi`; the κ = 0.15/0.16
  numbers are unchanged), SpecArbVacuous (`delay_bound` is now per corner: the old ∃M ∀c form is false without the
  band), SpecFb and ArbTSpec (proofs only). **AUDIT: please add a row** for this change to the frozen Spec.

## C2. COUNTEREXAMPLE (Lean-checked 2026-11-06 10:4x: `Formal.Net.CexPS.not_netCorrectSeq`) to the sequential theorem on THE target (gcd_ps) at g = 1, κ = 21/25, w = 0 (shard C)
- **What:** a transport-delay behaviour of `circuit DecodedPS.net DecodedPS.boundary` in which every arc delay is inside
  `Adm` at g = 1, κ = 0.84 (fast corner), the env obeys Env (R = 400 ns, su = 1 ns, Δo = 3 ns) and SeqEnv, and every
  arbiter resolves (ArbOK T for all T ≥ 36 ps), but the second pair never gets an out0: the circuit deadlocks.
- **Delays:** `umux16.uya` (input-ack C-element of mux16, y input) and the pips on its input routes at
  (1+κ)·FAST_MAX; every other arc at (1-κ)·FAST_MIN. Pairs (12,18) -> 6, then (1071,462) accepted, quiet from 520.8 ns.
- **Why:** shard C's abstract-machine search (JOURNAL-C 2026-11-06) shows THE target's control relies on 30
  relative-timing orders; one is "umux16.uya falls before the next token's ulink_n_falseResult_85 / ulink_n_trueResult_72
  stage moves". Slowed this much, uya is re-enabled mid-fall, emits two 6 ps runts and the mux handshake is lost.
- **Scope:** w = 0 (no runt filtering). Under H_RUNT(20 ps) these runts are filtered: open. Correct at κ = 0.82 with
  this adversary; B's sufficient bound is κ ≤ 0.415, so the g = 1 frontier is in [0.415, 0.84) if both hold.
- **Evidence:** formal/tools/huff/cex/k84b_dump.json.xz (every node's flips), checked by tools/huff/gatecheck.py (all
  186,871 gates, 0 mismatches, 0 arcs outside Adm) and envcheck.py (Env, SeqEnv, ArbOK T ≥ 36, Correct fails).
  Reproduce: `python3 formal/tools/huff/simadv.py net.json bnd.json --pairs 12,18 1071,462 --corner 0 --kappa 0.84
  --slow SLICE_X36Y47.C6 --slowroutes --nextreq seq --datachange broad --R 400000 --su 1000 --full` (net.json, bnd.json
  from `tools/cview/lean2json.py lean/Formal/Target/NetPS`). **Lean:** one-pair version (1071, 462), exact integer delays
  (`--exact --data0`), `not_netCorrectSeq : ∀ T su Δo, 36 ≤ T → Δo ≤ 3000 → ¬ NetCorrectSeq net boundary arbs ⟨1, 21/25⟩ T 400000 su Δo`,
  standard axioms (`lake build Formal.Net.CexPS.Refute`). **Also at κ = 18/25 = 0.72** (`Formal.Net.CexPS72.not_netCorrectSeq`, T ≥ 62):
  uya plus the four storage nodes of its support slowed (⌊43·FAST_MAX/25⌋), all else at ⌈7·FAST_MIN/25⌉. Simulation:
  a runt-ring livelock at 0.70, correct at 0.67 with these adversaries.
- **For research:** a fid GLS replay at these delays (and with the resolver on) would say whether the fabric model
  sees the same runts.

## A4. COUNTEREXAMPLE under H_RUNT(20 ps) (the owner's headline w): Lean-checked at g = 1, κ = 11/25; first found at κ = 18/25 (shard A, 2026-11-07)
- **What:** shard C's κ = 0.72 deadlock (C2, `CexPS72`) does NOT depend on runts. Re-run with a Spec-faithful H_RUNT(w)
  on every LUT pin (`SpecRunt.GateOKRunt w`: a LUT pin reads at the greatest time ≤ t - d lying in no pulse narrower
  than w, inside its Adm window; pips, hops, MUXF, CARRY4 transport), the same adversary (uya + 4 support storage
  nodes and their input routes at ⌊43·FAST_MAX/25⌋, all else at ⌈7·FAST_MIN/25⌉, LUT pins raised to ≥ w ps, still
  inside Adm) still accepts (1071, 462) and deadlocks quietly at 467.65 ns with no out0, for every w ≤ 25 ps. At w ≥ 26
  this adversary is no longer a behaviour (one LUT pin, SLICE_X32Y45.A6 pin 0, would have to skip a pulse longer than
  its window allows) and the run is correct.
- **Meaning (now Lean, at a much smaller scatter):** `Formal.Target.CexRunt44.not_netCorrectSeqRunt20` (standard
  axioms, check.sh OK): the headline statement is false at g = 1, κ = 11/25 for every T ≥ 123 ps, every su, Δo ≤ 3 ns;
  `FrontierRunt.not_seqRunt_le20_above44` carries it to every g ≥ 1, κ ≥ 11/25 and every w ≤ 20. **So H_RUNT(w) does
  not lift the margin for any w up to the owner's headline 20 ps: with or without runt filtering the g = 1 margin is
  below 0.44, and the one race that binds it is B's (safe to κ ≤ 0.41).** Audit T37 confirms the run independently.
- **Limit of this witness (checked, shard A 09:5x):** at w = 40 the same adversary at κ = 0.44 is CORRECT (out0 = 21),
  and it is not even admissible there (the slowed pin sits at the top of its window, so it has no room to skip a
  pulse: `INFEASIBLE 1`). At κ = 0.72 the cap is w ≤ 25. So nothing here says the statement is false for w > 20; a
  wider-filter refutation needs an adversary that leaves ≥ w slack on its slow pins. Research question unchanged: what
  is the fabric's real w?
- **Evidence:** `formal/tools-A/target/out/k72w20_dump.json.xz` (every node's flips), from `tools-A/target/simrunt.py`
  (C's simadv.py + `--w`); checked by the independent `tools-A/target/gatecheck_runt.py` (filtered waveforms rebuilt
  separately: all 186,871 gates, 274,930 checks, 0 mismatches, 0 arcs outside Adm, 0 read-lag violations, 0 reads in a
  narrow power-up interval) and C's `tools/huff/envcheck.py` (Env + SeqEnv OK, ArbOK for every T ≥ 61 ps, out0 never rises).
  Reproduce: `python3 formal/tools-A/target/simrunt.py net.json bnd.json --pairs 1071,462 --corner 0 --R 400000 --slow
  SLICE_X36Y47.C6 SLICE_X32Y45.A6 SLICE_X32Y28.A6 SLICE_X37Y47.D6 SLICE_X34Y47.A6 --kappa 0.72 --exact --data0
  --slowroutes --su 1000 --dout 3000 --full --datachange broad --dfall 3000 --nextreq seq --w 20`.
- **For research:** κ = 0.72 is a large within-die scatter; the point is that the runt filter is not what protects the
  circuit here: the binding relative-timing order (umux16.uya before the next token's link stage) is a plain race.

## C3. COUNTEREXAMPLES at much smaller margins: κ = 0.44 (g = 1) LEAN-CHECKED, and g = 1.6 (κ = 0) in simulation, with and without H_RUNT(20) (shard C, 2026-11-07)
- **Lean (standard axioms):** `Formal.Net.CexR44.not_netCorrectSeqRunt20_R` and `not_netCorrectSeq_R`: for every reset
  R = 400 ns + D, every T ≥ 123 ps, su, Δo ≤ 3 ns, THE statement at ⟨g, κ⟩ = ⟨1, 11/25⟩ is false, with H_RUNT(20) and
  without (`lake build Formal.Net.CexR44.AllR`). The g = 8/5, κ = 0 version is also Lean-checked: `Formal.Net.CexRg16.not_netCorrectSeqRunt20_R` (T ≥ 137, every R ≥ 400 ns).
- **What:** ONE C-element, `ulink_n_falseResult_85` stage 0 (SLICE_X32Y45.A6, b = C(x, ¬ack), INIT 0x2200332222003322),
  with its feedback route slow (its pin-0 arc and the 6 pips/hops of its self-loop route at the slow end; 7 arcs), and
  every other arc of the circuit at the fast end. Pair (1071, 462), SeqEnv env (R = 400 ns, su = 1 ns, Δo = 3 ns),
  corner 0: the acknowledge comes back before b's own rise has gone round its feedback route, so b = fb ∧ x reads
  fb = 0 and falls; b oscillates with its loop period (~570 ps), the stage's handshake is lost, out0 never rises.
- **Margins (this adversary):** w = 0: correct at κ ≤ 0.40, livelock at 0.44, quiet deadlock at 0.48 and 0.60; at κ = 0:
  correct at g ≤ 1.58, deadlock at g = 1.59, 1.6, 1.7, 1.8. **w = 20 (H_RUNT(20), the headline):** quiet deadlock at
  κ = 0.44 and at g = 1.6 (pulses here are ~80-570 ps, far wider than 20 ps); correct at κ = 0.40.
- **Meaning:** this is shard B's binding race row (RaceTablePS: safe for g²(1+κ)/(1-κ) ≤ 2.433, i.e. κ ≤ 0.415 at g = 1,
  g ≤ 1.56 at κ = 0). The row bound is tight within ~0.03 in each direction, and the runt filter does not help. If the
  Lean versions check, THE statement's frontier (fast corner) is: g = 1: κ* < 0.44 (w = 20) / < 0.48 (w = 0);
  κ = 0: g* < 1.6. A sound positive theorem must sit below B's bound on this row.
- **Evidence:** formal/tools/huff/cex/{k48_dump, g16_dump, k44w20_dump, g16w20_dump}.json.xz, delay classes
  cex/k48_classes.json. Checked by tools/huff/gatecheck.py (w = 0; per-arc `@classes`, `GFRAC=8/5` for g) and
  tools/huff/gatecheck_runt_c.py (shard A's independent H_RUNT checker + per-arc lists; negative control: the w = 20
  dumps read as w = 0 give 22 / 36 mismatches), envcheck.py (Env + SeqEnv OK, ArbOK T ≥ 113-136 ps, no out0).
  Reproduce: `python3 formal/tools/huff/simadv.py net.json bnd.json --pairs 1071,462 --corner 0 --kappa 0.48 --classes
  formal/tools/huff/cex/k48_classes.json --cdefault F --data0 --full --R 400000 --su 1000 --datachange broad --nextreq seq`
  (add `--w 20`, or `--kappa 0 --gfrac 8/5`). **Lean (building):** Formal/Net/CexPS48 (⟨1, 12/25⟩, w = 0) and
  CexPSg16 (⟨8/5, 0⟩, w = 0); the w = 20 versions need A's GateOKRunt witness check.
- **For research:** the fid GLS at these delays (feedback route of one stage-0 C-element slowed by ~1.5x relative to the
  ack path) would say whether the fabric oscillates the same way; the design-side fix is a longer acknowledge path or a
  shorter feedback route on link stage 0 (the stage reads its ack after one LUT + short routes).
- **Update 2026-11-07 09:5x: Lean-checked, and at a much smaller scatter.** Shard C's κ = 0.44 run (C3: one C-element's
  feedback route slow) is a behaviour under H_RUNT(20) too, and `Formal.Target.CexRunt44.not_netCorrectSeqRunt20`
  (standard axioms) refutes the headline statement at g = 1, κ = 11/25, T ≥ 123; `FrontierRunt.not_seqRunt_le20_above44`
  carries it to every g ≥ 1, κ ≥ 11/25, w ≤ 20. The κ = 0.72 entry above is superseded. For research: the runt filter
  is not the protection the circuit needs; the C3 race (ack faster than the C-element's own loop) is.

## A5. Which races bind THE target's margin (shard A, 2026-11-07; simulation, independently checked)
- **Two races fail below κ = 0.48** (single-pin adversary: one pin's route at the top of its window, every other arc at
  the bottom; H_RUNT(20); pair (1071, 462); all 412 control storage nodes x 1,316 live pins swept at κ = 0.48, and C's
  sweep at 0.40 found none):
  1. `ulink_n_falseResult_85` stage 0 (SLICE_X32Y45.A6): the acknowledge returns before the C-element's own
     feedback loop has gone round. Fails from κ = 0.44 (Lean-refuted, A and C independently); B proved it safe to 0.41.
  2. `ucontrol_merge10.uarb1.ua2` (SLICE_X38Y53.A6), its read of the fork `ucontrol_merge10_f` slowed: fails from
     κ = 0.46 (correct at 0.45; `formal/tools-A/target/out/k48w20_ua2_dump.json.xz`, checked: 0 gate mismatches,
     Env/SeqEnv OK, ArbOK T ≥ 113).
- **What it means for a fix:** both are local loop-versus-acknowledge races. Lengthening the acknowledge path, or
  shortening the loop (an RLOC'd feedback route), of these two cells would move this class's margin to at least
  κ = 0.48. Multi-pin adversaries were not swept.
- **Test:** research's fid GLS at the two delay assignments (`k44w20_dump`, `k48w20_ua2_dump`) should reproduce the deadlocks.

## C4. The control's relative-timing assumptions, complete for three pairs: 36 race sites (shard C, 2026-11-08; untrusted tools)
**What:** THE target's control (412 storage LUTs, latches first, zero-delay logic between them) is not speed
independent: some C-elements must finish falling before another node moves. On 2026-11-06 random walks found 30
such orders. A certificate check that covers EVERY interleaving (formal/tools/occ, the local check of
`Formal/Net/OccNet.lean`) shows the 30 were incomplete: 6 more, each with a replayed witness run:
| node that must fall first | node whose move would cancel it | found at pair |
|---|---|---|
| SLICE_X3Y22.D6 | SLICE_X3Y22.B6 (start_ack) | (12,18) |
| SLICE_X27Y81.A6 | SLICE_X31Y99.C6 | (12,18) |
| SLICE_X31Y59.B6 | SLICE_X33Y61.C6 | (12,18) |
| SLICE_X37Y21.A6 | SLICE_X34Y23.A6 | (12,18) |
| SLICE_X38Y21.B6 | SLICE_X39Y41.D6 | (12,18) |
| SLICE_X12Y45.B6 | SLICE_X19Y46.C6 | (1071,462) |
With the 36 (`formal/tools/occ/rt_final36.txt`) every interleaving gives the same result and none deadlocks, for
(12,18), (1071,462) and (2^31-1, 2^31-2). **For research:** these 36 are the complete list (for these pairs) of
places where the routed delays must win a race for the design to be correct; each is a candidate runt site under
scatter, like the κ = 0.44 one. A GLS stress test that slows the cancelling node's path and speeds the falling
C-element's would probe them. Shard C's timed theorem (`Formal/Net/TimedOccRT.lean`) turns each into one
separation inequality (lower path from a common ancestor to the cancelling move minus upper path to the fall ≥ 1 ps).

## B1. COUNTEREXAMPLE at κ = 0.40 (g = 1, w = 20 and w = 0, every reset ≥ 400 ns), LEAN-CHECKED; a periodic livelock from κ = 0.36 (shard B, 2026-11-08)
**What.** THE statement (and the headline with H_RUNT(20)) is false on THE target (gcd_ps_e6bb4aec) for every g ≥ 1,
κ ≥ 10/25, T ≥ 132 ps, Δo ≤ 3 ns, any su, every reset ≥ 400 ns: `Formal.Cells.CexX16.Frontier.not_seqRunt_le20_above40_R`
and `not_seq_above40_R` (standard axioms, check.sh OK). This moves the Lean-checked g = 1 refutation from κ = 0.44
(C3/A4) down to 0.40.
**The race.** `bridge_i.udut.ucontrol_merge4.uarb1.ua2` (SLICE_X16Y21.A6, the acknowledge C-element of merge4's
arbiter; INIT 0x00fa00a000fa00a0, reset on pin 3, own feedback on pin 4). Its pin 0 reads the fork
`ucontrol_merge4_f` (SLICE_X17Y23.B6) through a 6-arc route (FAST_MIN sum 312 ps, FAST_MAX 407). With that route at
the slow end and everything else at the fast end, the operands (0x49e9c618, 0x35bf992e) deadlock quietly ~84 ns
after reset release. It is the same cell pattern as A5's second race (merge10.uarb1.ua2 reading merge10_f, fails from
0.46), at another arbiter. **Pair-dependent:** (1071, 462) and the small pairs pass, which is why the earlier sweeps
(that pair only) missed it; 16 of the first 60 vectors of gcd_ps_vec1000.hex fail at κ = 0.38 and 0.40, none at 0.35.
**Below 0.40.** At κ = 0.36-0.39 the same adversary gives a livelock (no out0, never quiet); at 0.36 the full-width run
is exactly periodic (period 79 ps from 491 ns, 140 nodes; Env/SeqEnv/ArbOK hold on the prefix). Not Lean-checked.
Simulated margin of this race: (0.35, 0.36].
**For research.** Any single-pair κ sweep under-reports the margin: sweep the adversaries over wide operands. The
ua2-reads-fork pattern of the arbiters (merge4 here, merge10 at 0.46) is the binding race class; giving ua2's fork
input more slack relative to its feedback loop (or placing ua2 next to the fork) is the fix to try first.
Files: `formal/tools-B/target/out/k40w20_x16y21_{dump.json.xz,classes.json}`, `k36w20_x16y21_dump_1200ns.json.xz`;
`formal/tools-B/ps/out/race_x16_k{35,40}_vec60.txt`; JOURNAL-B 2026-11-08.

## A6. The κ = 0.36 livelock is LEAN-CHECKED: THE statement is false for every κ ≥ 0.36 at g = 1 (shard A, 2026-11-09)
B1's livelock is now a theorem. `Formal.Target.Frontier36.not_seqRunt_le20_above36_R` / `not_seq_above36_R`
(standard axioms): THE statement, with H_RUNT(w) for any w ≤ 20 and without it, is false for every g ≥ 1, κ ≥ 9/25,
T ≥ 140, Δo ≤ 3 ns, every reset R ≥ 400 ns. Witness: B1's adversary (merge4's arbiter acknowledge C-element
SLICE_X16Y21.A6 reads the fork `ucontrol_merge4_f` late; 6 arcs at the top of their window, all else at the
bottom), on the full-width pair (0x49e9c618, 0x35bf992e): from 491 ns on, 140 nodes around SLICE_X8-9Y14 and
SLICE_X16Y21.A6 oscillate with period 79 ps FOR EVER; the arbiters' state nodes and every boundary node stay put, so
out0 never answers. B's simulation has the adversary correct at κ = 0.35, so on this race the g = 1 margin is in
(0.35, 0.36]. **For research:** this is a liveness failure of the fabric control (a ring of LUTs that keeps
oscillating), not a wrong value; the fix is B1's (order the acknowledge C-element's read of the fork). A GLS check:
the same adversary in the board-fidelity stack at κ = 0.36 should show the 79 ps oscillation and no out0.
