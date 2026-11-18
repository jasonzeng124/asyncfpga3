# Subagent dynfig (2026-11-18 16:58-18:25 UTC): Dynamatic's figure for each suite kernel (PROGRAM lead 8)

Saved by the bot from the subagent's final message (its harness refused out/REPORT.md). Patches applied as c70e415cd..c39f2c107.

**Summary.** Over suite3a / 3b / 6 / 8 (19 kernels, 18 pass): the per-iteration ratio is filled on 13 kernels (was 9),
geometric mean 1.25 with estimates (3 of the 13 use the new latency fit for our side), 1.40 over the 3 measured
kernels; a latency-per-call ratio (same calls on both sides) on 15 kernels, geometric mean 1.35. No per-iteration
figure: the 4 loop-free kernels (undefined on both sides; latency given), test_bitint (no P on our side), test_int16
(Dynamatic's model gives it no period), quadrec (build failed). **suite8's dot2 P of 156.00 ns was wrong**: it was the
memory port during the host's array fill (13 x 12 ns), not the kernel's loop.

## 1. Memory kernels (dynamatic_est.py)
- The memory model was already there and correct. The gaps: a v2 vector file (arrays) was read as one call per line;
  dot2, gather and fill had never been run; Dynamatic's tests had only run on their own main().
- Now v2 files are read with the bench's layout, each call with its own arrays, every call checked against
  oracle_mem.sh (the result and every array after the call): **66 kernels, 409 / 409 calls right** (was 62 / 310). The
  119 kernels whose vectors did not change are identical in every column.
- The cycle model checked against Dynamatic's own Verilog (dyn_memcosim.py; mem_controller.v, load.v, mc_support.v,
  tehb.v under iverilog, unedited): 8 seeds x 3000 cycles, every port equal in every cycle, BRAM contents equal (15631
  reads, 6144 writes); three injected defects (late read data, reversed read priority, no pending-store decrement)
  each caught on 8 / 8 seeds. test_dynamatic_est.py all pass, incl. 9 memory kernels and three new negative controls.
- New figures (estimated period x simulated cycles): dot2 59.3 ns per iteration (5.98 cycles), latency 1212 ns per call;
  gather 69.2 (6.98), 1510 ns; memsum 59.3 (5.98; 56.9 on main()), 1033 ns; fill 11.0 (1.00), 208 ns.
- Caveat: the ~6 cycles per iteration come from Dynamatic's on-merges buffering waiting for each memory round trip; a
  solver-buffered Dynamatic could reach 1 cycle, so our ratios on these kernels flatter us by up to ~6x.

## 2. Loop-free kernels
- dynamatic_lat.tsv: Dynamatic's cycles per call on the suite's own calls x the period (the routed period for the 3
  measured kernels, tagged). suite_table.py adds three columns at the end: our latency per call, Dynamatic's, ratio.
- straight 1 cycle x 14.92 = 14.9 ns vs ours 72 ns (4.83); test_loop_free 3 x 3.85 = 11.6 vs 72 (6.23); unused_arg
  2 x 0.97 = 1.9 vs 72 (36.9); test_int16 1 cycle, no period in the model, ours 60 ns. The periods of test_loop_free and
  unused_arg are extrapolated far below the calibration points (0.97 ns is not a real clock): marked, left out of the
  geometric mean.
- The right metric is the kernel's own latency from operands to result on both sides; ours is not that yet: the bench
  counts from its issue to its capture in 12 ns host cycles (a constant kernel already takes 60 ns), so for these
  kernels the ratio measures the bench.

## 3. Why our P was missing, and the fixes
| kernel | cause | now |
|---|---|---|
| straight, test_int16, unused_arg | no loop, no marker (eventgraph crashed) | check.txt says why |
| test_loop_free | its marker rises once per call | check.txt says why |
| test_bitint | the marker was the memory port's request (host fill + kernel loads); 10 trips per call | correct marker; no steady state by nature |
| brhash | iteration time depends on the data | fit 32.08 ns (4 routes), ratio 0.88 |
| fold64 | iterations alternate exactly (21529 / 23924 ps) | P = 22726 ps per iteration; fit 23.31 ns, ratio 1.95 |
| dot2 | P was the host's memory fill | P refused; fit 28.50 ns, ratio 0.48 |
- brhash and fold64 confirmed on their exact farm routes, rebuilt (sdf 2744d342, a5c6fab7 = the farm's; nextpnr
  6e5d224472232d5d, seeds 1 and 4): brhash 5 distinct intervals 31.92-32.55 ns, mean 32.13 (1.1 % from the fit);
  fold64 every pair of iterations exactly 45453 ps, both event-graph checks pass.
- eventgraph.py: skips memory-port nets when picking its marker; tries strides 2-4 when single intervals have no
  steady state; writes the reason instead of crashing. Only runs that previously had no P take the new path (on an
  xorshift run all three outputs byte-identical to the old tool's). On suitew's dot2 route it now measures 24504 ps per
  iteration, but the graph's own check fails (memory nets aperiodic); the measured P stands, as for any failed check.
- suite_table.py: refuses a P that is an exact multiple of the host clock; where P is missing, uses the slope of our
  call latencies against the trip counts, marked "fit". Fit vs P on the 42 routes (10 kernels) that have both: median
  1.006, range 0.976-1.052.

## 4. MILP solver: not possible
The installed dynamatic-opt has CBC compiled out (only the stub "CBC not installed!"); dynamatic/ holds no sources to
rebuild it, so a user-space CBC cannot be used without rebuilding Dynamatic.

## Does NOT show
Every Dynamatic period except the three routed ones is the 3-point estimate (worst leave-one-out 16 %), on-merges
buffering only. Our latency per call includes the bench. The fit uses the draws' latencies, not the event graph. The
shortened window for strided runs is tested on dot2 only. The test_bitint route used was built by nextpnr
9c732bc6303458df (it only exercised the marker logic; no number comes from it).

## Open
A named probe for the kernel's input request in the bench (the kernel's own latency per call); suite_one.sh computing
the fit itself; a solver-based Dynamatic buffer placement through an open solver (matters most for memory kernels).
Unfiled: out/suite8b.sh (suite8's 18 skipped tasks + fold64 s1 + test_bitint s3 with the fixed tools). The subagent
ran `git fetch -q origin` in /tmp/bot/repo once (against the preamble; no effect).
