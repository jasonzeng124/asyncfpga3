# Where the simulation is not the board

Kept by research (PROGRAM.md "The board decides", owner 2026-11-16). One row per known difference between the
simulation that judges a build (cells/gls, GLS_MODEL=fid, run by research/tools/eventgraph/bench_gate.sh) and the board:
what the board showed in August, if anything, and what the simulation does about it. Newest changes at the top of each
row's text. "August" = the owner's board runs, research/board/aug/ (builds, logs) and research/board/ro_many_aug/.

| # | difference | August board evidence | what the simulation does |
|---|---|---|---|
| 1 | **Delay of each arc.** prjxray gives a [FAST_MIN, SLOW_MAX] band per arc, not this die's value. | 128 rings (LUT + wire only): band x = 0.2877 median, p05-p95 0.276-0.303, residual 0.76% per ring (research/data/fid/ring128/fit.txt). Kernel builds (gcd, ipow, isprime, collatz, collatz64; research/data/aug_kernels): x = 0.211-0.225, every result equal to the board's. gcd simulated at 0.288 is 9-10% slower than the board on every vector (research/data/aug_gcd). The ring / kernel gap is not explained. | `worst` corner: delay chains 0.21, rest 0.288, CARRY4 / F7F8 / FF at SLOW_MAX, setting M scatter, one seed. `draw:K` (2026-11-16): chains and rest each uniform over [0.20, 0.31] independently, CARRY4 / F7F8 / FF uniform over [0.20, 1.0], setting M scatter with seed K; a candidate is reported as the fraction of draws that return right answers. |
| 2 | **Cell types the rings never exercised**: CARRY4, MUXF7/F8, slice FF, DSP48. **The gap with the largest effect on the candidates (2026-11-17).** | **No August kernel places this band, at any resolution** (research/data/bandfit, 2026-11-17 evening; section below). On the measured bitstreams, at each kernel's own LUT/routing x, CARRY4 / F7F8 / FF from y 0.2 to 1.0 leave every per-vector latency the same at the bench's 10 ns (collatz 8/8, collatz64 7/8, ipow 7/8, gcd 24/24 at x 0.288) and, in picoseconds, the time per iteration identical (ipow 60.280 ns at y 0.2 / 1.0 / 2.0 / 3.0; collatz64 117.609 at 2.0 / 3.0): y moves only a constant ~0.2 ns per call per unit of y, outside the loop. The matched LUT chains set the cycle; carries and F7 selects only settle inside them (formal A13 / A14 and audit T145 agree). Beyond the band (y 2.0 / 3.0, extrapolated) every board vector stays right on collatz, collatz64, ipow and gcd (10 of its 24 vectors at y 3.0); ipow is still right at y 6 and gives no answer at y 12 (where the bench's own logic is scaled too). So the board's right answers bound y only far above the band, and only a carry-specific measurement can place it: BOARD-QUEUE item 36 (carry_ro_top). Effect on the candidates (unchanged): collatz x0.55 route 30 fails exactly the draws with this band at 0.75 / 0.91 (farm shrink9); item 35's loop-entry race falls to ~0 ps near 0.9 (formal C38, audit T144). The DSP48 band does not move ipow's time either (formal A14). | Their band stays uniform over [0.20, 1.0] per draw (`draw:K`), SLOW_MAX at `worst`: the fit gives nothing to narrow it to (2026-11-17), so it waits for item 36. DSP48: research's own model (cells/gls/dsp_model.py) at the LUT/routing band; formal's decoder now decodes DSP48E1 (C39). |
| 3 | **Within-die variation.** | Residual 0.76% per ring after one global x, i.e. variation + model error together. | Setting M: region factor sigma 0.02 per 10x10 slices, per-pip factor sigma 0.126 averaged along each wire (gives ~1.34% per ring, conservative). No length-dependent offset: the ring fit by length (0.283 / 0.287 / 0.288 / 0.291 for 7 / 15 / 31 / 63 links) shows none worth modelling. **Two models disagree about how far apart two racing paths can sit (2026-11-22):** formal B's race-only adversary and the auditor's T182 split replay set each arc of a race independently at opposite ends of its prjxray range, far outside this model's box; at such splits they fail routes (items 44's thin three, 46's unpadded half) that our gate, formal C's draws (C72 / C73: 64 / 64 on all eight routes of items 44-46) and uniform-corner GLS all pass. The ring data bounds the per-ring residual (0.76 %), not the split between two paths of one race; BOARD-QUEUE items 44-46 are the measurement. |
| 4 | **Narrow pulses (glitches) into LUTs and C-elements.** No published 7-series LUT pulse rejection. | None. BOARD-QUEUE item 2 (H_RUNT, research/board/runt/) measures it. | LUT inputs are transport delays (every pulse passes); a LUT with feedback (latch, C-element) has a resolver: a pulse shorter than its loop delay minus WIN/2 is rejected, longer ones resolve by a noise law (TAU = WIN = 150 ps, unsourced). research/data/fid/runtc.md: 1-40 ps pulses never set a C-element; with the resolver off they oscillate (formal's model). **2026-11-20, a lost race replayed in both simulators:** formal B21's adversary on exit1 varshift s1 (the latch-fed steer ucond_br11, its condition at FAST_MAX and its request at FAST_MIN) replayed here per arc (research/tools/adv_sdf.py): 271 pulses of 19 ps on 22 kernel nets (the steer, both control merges, link stages), 10 / 10 answers right, because the resolver rejects them; formal's simx (transport, 20 ps filter) deadlocks after 2 answers on the same assignment. Same race, same nets; only this row decides the outcome. |
| 5 | **Metastability (arbiters, synchronisers).** | None on kernels. | Resolver on state nodes (above); FF window from SDF TSU / THD with random resolution. Arbiters are emitted unconditionally (CLAUDE.md). |
| 6 | **Start-up.** Silicon has no X; an unreset latch powers up 0 or 1. | None. | Every LUT state node starts X; bd_link's data latch has no reset, so a race against its first value can leave X that spreads. The owner chose to keep this (2026-11-16): +META_INIT=0/1 stays opt-in, used only to tell a real failure from start-up X when a run hangs. **2026-11-18 (subagent hangs, research/data/suite/hangs.md): on flow v1's ipow seed 4 route the start-up x was the ONLY symptom of a real race** -- the loop-exit steer's request arrives 566 ps before its select on every call (40 runts of 17-474 ps on the exit branch in 9 us under +META_INIT=0, all rejected by the gate's runt model, so the answers stayed right); only at start-up, where the stale select is x, does the run hang. The rule had flagged it (A -719, E -734..-1070 ps) on a route shipped NOT CLEAN. So a hang at start-up with +META_INIT passing is evidence of a race, not of a start-up artefact; and the gate's runt model can hide a race that fires on every call. |
| 7 | **The bits.** The board runs what is in the bitstream, not nextpnr's netlist. | Three August failures were bitstream bugs (lut-pinmap, DSP const pins, DSP AREG); reproduced by the full stack (research/data/fid/acceptance_status.md). | The netlist is decoded from the .bit (fasm2net), checked against the routed JSON (fasm_equiv); ffmux_scan; toolchain.sh fingerprint. |
| 8 | **The host.** The board's PS writes operands over AXI and polls; the bench FSM runs each vector N times. | August logs: FIXED mode N = 200, the board script asserts the repeatability latch (mism_st bit 0) and a SIG oracle. | ps7_bench.v (AXI master model, FCLK 83.3 MHz), N = 2 runs per vector. **Until 2026-11-16 the gate read only the last run's result and ignored the repeatability latch**: a build whose result stream lagged one call passed. Now a batch whose runs disagree fails (JOURNAL 2026-11-16). |
| 9 | **Inputs.** The board takes any value of the C signature. | n/a | Gate vectors are a few dozen per kernel, oracle compiled from kernels/*.c (kernel_oracle.sh). collatz / collatz64 vectors had no n = 1 (zero-trip) until 2026-11-16 (col14 / c6415). Paths the vectors cannot reach (32-bit loop counters) are covered only by the static rules, which are now tools, not gates. |
| 10 | **Voltage and temperature.** | One board, room temperature, one supply; x from that. | Covered only by the band ranges in row 1. |
| 11 | **Memory inference.** iverilog cannot see yosys memory inference (CLAUDE.md). | isprime's late read (August). | Kernels here have no memories. |

## ns per iteration on the August bitstreams: the LUT / routing band x and the CARRY / F7 band y (2026-11-17, research/data/bandfit/)
Replaces the 2026-11-16 section (aug_periter.py; its numbers are row collatz / collatz64 / ipow of table A).
What is simulated: the August bench builds whose `.bit` the board measured (research/board/aug/builds =
research/data/board-august byte for byte; their logs match=yes; xorshift below), on the full stack: netlist decoded from
the `.bit` (fasm2net --ps7; fasm_equiv EQUIVALENT, collatz and isprime with benign F7-input differences: aug_kernels
README), the prjxray SDF of the
build's own route (xray_delay.py), GLS_MODEL=fid, ps7_bench.v at FCLK 100 MHz, the board's own vectors (2 runs each),
every result checked against the C oracle (research/tools/fifteen/kernel_oracle.sh) and against the board's. The routes
are the archived August ones (nextpnr d216cb36a370f78a); nothing is re-routed, so each kernel has exactly one route, the
one the board ran (the 4-seed rule does not apply: there is nothing to sample). Two band positions, each in an arc's
[FAST_MIN, SLOW_MAX]: **x** for LUT, routing and DSP48 arcs, **y** for the CARRY4, MUXF7/F8 (SELMUX2_1) and slice-FF
IOPATH arcs (gen.py GLS_SDF_BAND / GLS_SDF_BAND_CELL).

**A. x, the LUT + routing band** (every arc at one band; corner runs research/data/aug_kernels and aug_gcd; numbers
from research/data/bandfit/table.py). "Other four" = the mean x of the other four kernels: the number predicted there
is out of sample for that kernel.

| kernel | metric | board vectors | board | FAST_MIN | SLOW_MAX | x fitted | x of the other four | predicted there | at 0.288 (ring band) | over the draw range x 0.20-0.31 |
|---|---|---|---|---|---|---|---|---|---|---|
| collatz | ns / iteration | 20 | 92.73 | 65.16 | 188.76 | 0.223 | 0.222 | 92.59 (-0.1%) | 100.76 (+8.7%) | 89.9-103.5 |
| collatz64 | ns / iteration | 12 | 117.89 | 83.04 | 237.37 | 0.226 | 0.221 | 117.19 (-0.6%) | 127.49 (+8.1%) | 113.9-130.9 |
| ipow | ns / iteration | 17 | 60.46 | 42.20 | 122.53 | 0.227 | 0.221 | 59.95 (-0.8%) | 65.34 (+8.1%) | 58.3-67.1 |
| gcd | ns / main-loop iteration (cost model: base + k + ctz-pre + main + ctz-in) | 24 | 156.50 | 112.77 | 172.02 at band 0.288 (SLOW_MAX: 10 of 24 hit the harness race) | 0.213 | 0.225 | 158.97 (+1.6%) | 172.02 (+9.9%) | 153.9-176.6 |
| isprime | ns, n = 97 minus n = 2 | 2 | 8050 | 5750 | 16100 | 0.222 | 0.222 | 8049 (-0.0%) | 8731 (+8.5%) | 7820-8959 |

x over the five kernels: mean 0.222, sd 0.006, range 0.213 (gcd) to 0.227 (ipow); within a kernel the per-vector x
spreads ~0.01 (aug_kernels README). Out of sample the model predicts four kernels within 0.8% and gcd at +1.6%. The ring
band (0.288, research/data/fid/ring128) is 8-10% slow on every kernel. The draw range x in [0.20, 0.31] contains the
board on every kernel, in its lower fifth. The ring / kernel gap (0.29 vs 0.22) is the same in formal's RC-tree model
(A18), so it lies in the silicon or the sessions, not in either model; it is unexplained (formal A14 lists candidates).

**Formal's rows** (formal/FOR-RESEARCH.md A14 / A18: formal's simx on the same decoded bitstreams; formal's own board
numbers and metrics; its b is a position in formal's own [FAST_MIN, SLOW_MAX]):

| kernel | formal's metric | formal's board number | formal FAST_MIN / SLOW_MAX | formal, one b = 0.39 for all (default arcs) | formal RC_TREE=1, b fitted (A18) | research x, same build |
|---|---|---|---|---|---|---|
| collatz | ns / iteration | 92.73 | 50.35 / 159.81 | 93.04 (+0.3%) | 0.216 | 0.223 |
| collatz64 | ns / iteration | 117.89 | 64.43 / 204.16 | 118.92 (+0.9%) | 0.223 | 0.226 |
| gcd | (2^31-1, 2^31-2) minus (1, 1), ns | 11695 | 6305 / 19911 | 11611 (-0.7%) | 0.214 | 0.212 (board 11630 by latmin) |
| ipow | ns / iteration | 60.85 | 32.41 / 102.16 | 59.61 (-2.0%) | - | 0.227 |
| isprime | n 97 minus n 2, ns | 8100 | 4411 / 13901 | 8112 (+0.1%) | - | 0.222 (board 8050 by latmin) |
| isprime | n 1009 minus n 2, ns | 40335 | 21972 / 69250 | 40410 (+0.2%) | - | - (no SLOW_MAX run) |
| 128 rings | median period | - | - | +8.8% (the rings sit higher: b 0.465) | 0.286 | 0.288 |

One band for every kernel, fitted in sample, is within 2.0% in formal (b 0.39) and within 1.2% in research (x 0.222:
collatz -0.1, collatz64 -0.5, ipow -0.7, gcd +1.2, isprime -0.0%). Formal's and research's board numbers differ slightly
for ipow and isprime (vector sets and latmin / latmax use differ); neither changes x by more than 0.005.

Formal's earlier x ~0.75-0.9 (A11) came from REBUILDS of the August kernels, whose matched-delay sizes are not the
measured ones; formal withdrew it (A14). On the measured bitstreams all three readings agree: research x 0.213-0.227,
formal 0.214-0.223 with RC_TREE=1 (its default arcs are ~20% fast, which is why its default b is 0.39), the audit's own
GLS 0.223 / 0.226 / 0.230 (T138 / T140 / T145).

**B. Direct runs at each kernel's own x, CARRY4 / F7F8 / FF at y** (run1.sh; bandfit.py; logs in
research/data/bandfit/logs/; ns per iteration on the 8 board vectors of each kernel, board column on the same vectors):

| kernel, x | board, 8 vectors | y 0.2 | y 1.0 | y 2.0 | y 3.0 | per iteration in ps (LATMON) |
|---|---|---|---|---|---|---|
| collatz, 0.222 | 92.76 | 92.68 (-0.09%), 8 / 8 right | 92.68, 8 / 8, latmin = y 0.2's on 8 / 8 | 92.66, 8 / 8, 2 vectors +1 count | 92.66, 8 / 8, = y 2.0's | 92.698 ns at y 2.0 |
| collatz64, 0.224 | 118.04 | 117.61 (-0.36%), 8 / 8 | 117.59 (-0.38%), 8 / 8, 1 vector +1 | 117.59, 8 / 8, = y 1.0's | 117.59, 8 / 8, = y 1.0's | 117.609 ns at y 2.0 and 3.0 (+204 ps per call) |
| ipow, 0.225 | 60.43 | 60.43 (+0.00%), 8 / 8, every latmin = the board's | 60.33 (-0.18%), 8 / 8, 1 vector +1 | 60.19, 8 / 8, 2 vectors +1 | 60.00, 8 / 8, 3 vectors +1 | 60.280 ns at y 0.2, 1.0, 2.0, 3.0 (+176 / +396 / +616 ps per call) |
| gcd, 0.211 (10 of its 24 board vectors) | 157.31 per main-loop iteration (cost model on these 10; 156.50 on all 24) | 159.51 (+1.4%), 10 / 10 right; summed latmin -0.10%, every vector within 3 counts | (at x 0.288: identical to y 0.288 on 24 / 24, research/data/aug_gcd) | - | 159.94 (+1.7%), 10 / 10, latmin = y 0.2's on 9 / 10 (one +1) | +571 ps per call from y 0.2 to 3.0, every vector (204 ps per unit of y), so every loop cost is the same |

Further out, ipow with the bench clocked at 25 MHz (at y 12 the bench's own 100 MHz logic stops meeting timing, since its
CARRY4 counters and flip-flops are in y too: logs/ipow_x0225_y120_bench100MHz_stopped.log; the kernel has no clock, so
the slower bench changes only the counts' unit): y 6.0 8 / 8 right, 60.280 ns per iteration, +1276 ps per call;
y 12.0: no batch completes at either bench clock. During the bench's AXI set-up, before batch 0, out0's request
rises 17 ns after a request the bench raised (one LATMON line, at the same point of the set-up at 100 and at 25 MHz);
at 25 MHz batch 0 then HANGs (0 of 2 calls, odata x, bench FSM X; stopped after it; at 100 MHz stopped after 16 min
with no batch; logs/ipow_x0225_y120_*). At y 12 the
bench's own carries and flip-flops are scaled too, so this run does not say whether the kernel or the bench fails
first.

The bench-level ns per iteration of ipow drifts by up to -0.7% at large y only because the one-count flips land on the
short vectors and tilt the fit; the kernel's own time per iteration is the same to the picosecond.

**The CARRY / F7 band y: no kernel places it.** At each kernel's own x, moving CARRY4, F7/F8 and the slice FFs from
y 0.2 to 1.0 (and on to 2.0 and 3.0) leaves every answer right and the time per iteration unchanged (table B):
- At the bench's resolution (latmin, 10 ns counts) the per-vector latencies are identical at y 0.2 and 1.0 on collatz
  8 / 8, collatz64 7 / 8, ipow 7 / 8 and gcd 24 / 24 (gcd at x 0.288, research/data/aug_gcd); each difference is one
  count on a short vector.
- In picoseconds (lat_mon.py, compiled into every run since 17:38: each call's kernel latency from the request
  flip-flop's output to out0's request; LATMON lines in the logs) the time per iteration does not move at all: ipow
  60.280 ns at y 0.2, 1.0, 2.0 and 3.0, collatz64 117.609 ns at y 2.0 and 3.0 (collatz: 92.698 ns, one y only). What
  moves is a constant per call, the same on every vector and both runs: ipow +176 / +396 / +616 ps at y 1.0 / 2.0 / 3.0
  against 0.2 (220 ps per unit of y), collatz64 +204 ps from 2.0 to 3.0, gcd +571 ps from 0.2 to 3.0 (204 per unit):
  one y-class arc on each call's path, outside the loop. 204 ps per unit of y is exactly one slice-FF clock-to-Q
  spread (99 -> 303 ps), and the kernel has no slice FF (its storage is on LUTs, cells/rtl/bd_latch.v), so it is most
  likely a bench flip-flop launched on the request's aclk edge (not traced). The one-count flips in latmin are this
  offset, plus the bench's own synchroniser flip-flops, crossing a 10 ns sampling edge on a short vector.
- So the board's per-iteration times cannot place y at any resolution: the loops pay the matched LUT chains, and the
  carries and F7 selects only have to settle inside them. The per-call constant (~0.2 ns per unit of y) is 50 times
  below the bench's resolution and inseparable from the bench's own y-dependent synchronisers. Formal A13 / A14
  (collatz, collatz64: 0.00 ns over CARRY / F7 0.2-1.0) and the audit's T145 (0.0 / 0.0 / +0.2%) agree.

**Beyond the band: y 2.0 and 3.0 (an extrapolation of prjxray's band, a correctness bound, not a corner).** y = 2 / 3 put
the median CARRY4 S0->CO3 arc at 0.84 / 1.20 ns (SLOW_MAX 0.49), CIN->CO3 at 0.19 / 0.27 ns (0.12), the F7 select
S0->OUT at 0.50 / 0.70 ns (0.30) and FF clock-to-Q at 0.51 / 0.71 ns (0.30) (ipow's xray.sdf). Every August build
returns every board vector right at both, both runs agreeing, no hang: collatz 8 / 8 and 8 / 8, collatz64 8 / 8 and
8 / 8, ipow 8 / 8 and 8 / 8, and gcd 10 / 10 at y 3.0 (x 0.211; 10 of its 24 board vectors, among them
(2^31-1, 2^31-2), whose first subtraction carries through all 32 bits). The first wrong answer or hang: ipow is still right at y 6.0 (bench at 25 MHz) and gives no answer at y 12.0 (the
bench's own logic is scaled too there); collatz, collatz64 and gcd were not taken past 3.0.
So the August builds carry their carries with a wide margin under their matched delays, and the board's right answers
bound y only far above the band: they do not narrow [0.20, 1.0] from either side. This does not carry over to the shrunk candidates, whose
weakest races close inside the band (formal C36-C38, audit T144).

**Redrawing the candidates "with CARRY / F7 where the fit puts them": the fit puts it nowhere.** No kernel's time
depends on y, and the August answers stay right far beyond the band, so the August data neither place y nor narrow
[0.20, 1.0]. The candidates' draws therefore stay as they are: CARRY4 / F7F8 / FF uniform over [0.20, 1.0] per draw
(bench_gate.sh draw:K; SLOW_MAX at `worst`) until BOARD-QUEUE item 36 (carry_ro_top, two routes, built and checked)
measures the band. No number is put in its place here. For the leads this means:
- Nothing is redrawn, so no pass fraction changes (item 35 128 / 128 on 32 routes; the collatz and ipow leads as
  reported).
- Their weakest races stay in the unmeasured band. Item 35's loop-entry race (ucmpi0 -> ucond_br2) keeps ~0.4-0.5 ns at
  y 0.2 and loses ~55-65 ps per 0.1 of y, reaching ~0 near 0.9 (formal C38, on formal's default arcs, ~20% fast); in
  research's model it keeps 60 ps at chains 0.20 / rest 0.31 / y 1.0 (audit T144). About one draw in eight has y above
  0.9 and passes on tens of ps or absorbed runts. Collatz x0.55 route 30 fails exactly its draws at y 0.75 and 0.91
  (farm shrink9); x0.70 passes 128 / 128. The ipow x0.55 routes keep >= 789 ps at y 1.0 in formal's simx (C40; default
  arcs, being redone with RC_TREE=1 per the C36-C47 caveat).
- So a pass fraction over uniform y says how often a build survives the band, not whether the board's own y lies in
  its safe part. If item 36 bounds y below ~0.6 (formal C38: one median SDF error of margin on item 35's race), item 35
  and the leads stand as reported; if it puts y near 1, item 35 and collatz x0.55 have no margin left, and formal C41's
  fix (UCMPI0 back to 10: entry race >= 916 ps and loop test >= 387 ps at y 1.0 on 3 routes, default arcs, no
  measured speed cost) or the longer sizes are the builds to send.

**xorshift: what can and cannot be compared.** The archived bitstream (604148b326ae, written 2026-08-24 14:42) is newer
than all 25 xorshift logs in research/board/aug/logs (match=NO), so no log is known to have measured it. Two corrections
to earlier readings of those logs:
- The 10 trip_N logs ran FCLK0 at **50 MHz**, not 100: xsdb_rounds_sweep.tcl writes its 4th argument (0x00101400) into
  FPGA0_CLK_CTRL and prints "FCLK0 nominal 50.0 MHz"; its "FCLK0 set (100 MHz nominal)" line is a fixed string. They are
  the 50 MHz section of cells/hw/trip_sweep_results.tsv, which measured the same build at 100 / 83.3 / 50 MHz: 49.66 /
  49.59 / 49.63 ns per round. So the trip logs give 49.6 ns per round, not ~25 (JOURNAL 2026-11-17 20:09), and the 15
  logs at 100 MHz, which only run (48, 18), read 93 cycles, as that sweep predicts (83 at 16 rounds + 2 x 4.97). The
  per-round times do not show two builds.
- The board measured more xorshift builds on 2026-08-24 than the logs show, as tables in cells/hw/ (FIXED N=200,
  100 MHz, seed 2463534242, rounds 0-256; ns per round = slope of latmin, rounds >= 8): xorshift_cost_results 49.60
  (committed 12:29), seed13_tightened 45.52 and seed11_untightened 96.99 (13:06), route1-3 (default path, rule E did
  not settle) 99.6 (14:22), and the two BD_SKIP_RULE_E=1 builds skipE1 / skipE2 49.99 / 49.98 (be314e8c1, committed
  14:47, five minutes after the archived .bit was written). The archived bit is most plausibly skipE2's (the last build,
  measured and committed right after it), but no md5 ties them.
- **Simulated** (research/data/bandfit/logs/xorshift_x0222_y02_cost.log): the archived bit, decoded (EQUIVALENT to its
  routed JSON), at x 0.222 (the mean of the five other kernels: out of sample for xorshift) and y 0.2, on that sweep's
  17 points at 100 MHz: 17 / 17 right, **49.71 ns per round** (49.718 from the picosecond monitor). Against the board
  tables: skipE2 49.98 (-0.5%; every point within -7 .. +1 counts), skipE1 49.99 (-0.6%), xorshift_cost_results 49.60
  (+0.2%; within +3 counts); seed13_tightened 45.52 (+9.2%, 107 counts at 256 rounds) and the untightened builds (97-100
  ns, half) are excluded.
- **What can be compared:** the archived bit behaves like the ~50 ns-per-round builds measured that day (skipE1 / E2,
  cost_results, the trip sweep's 49.7), and the model predicts them within 0.6% at the other kernels' x, the same
  accuracy as for the five kernels whose bitstream is certain. **What cannot:** which of those builds it is (they are
  0.8% apart, inside the model's own x spread), so xorshift gives no fitted x of its own, no new evidence on y, and its
  logs remain soft evidence; README's 47.66 ns per round matches none of the August tables.

**What this does not show.**
- x is fitted per kernel on its board data, so the "x" columns are in sample; only the "other four" column predicts.
  Five kernels, one board, one day, one route each (the routes the board ran; nothing to re-sample).
- Table A interpolates between the corners (latency linear in x); the direct runs check that on three kernels to
  within 0.4%. The board's numbers are latmin over 200 runs in 10 ns aclk cycles (slope quantisation ~0.1 ns per
  iteration); the simulation runs each vector twice.
- LUT and routing are not separated: every kernel and the rings have nearly the same LUT share of their delay
  (formal A14: 0.61-0.69), so no August measurement can tell the two bands apart.
- y: CARRY4, F7/F8 and FF are moved together, as the draws do; the August data cannot place any of them, singly or
  together. y > 1 extrapolates the prjxray band; it is not a corner and says nothing about the silicon at y > 1.
- The ring / kernel gap (0.29 vs 0.22) stays unexplained; formal A14's proposed check (a kernel and the rings in one
  board session, no rebuild) would settle whether it is the day or the builds.
- isprime was not run at any y; gcd's y runs use 10 of its 24 board vectors.
