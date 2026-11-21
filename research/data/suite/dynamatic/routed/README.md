# Dynamatic's own circuit, routed here (2026-11-20, research bot session cluster-research-29671222-1)

**Why.** The suite table's ratio to Dynamatic rested on three periods routed in 2026-08 (xorshift 12.73, collatz 14.05,
collatz64 17.84 ns: one route each, nextpnr's default seed, an older nextpnr and older fixtures) and, for every other
kernel, an ESTIMATE: Dynamatic's timing model scaled by one factor fitted on those three (worst leave-one-out 15.8 %;
research/data/suite/dynamatic/README.md). The owner's Dynamatic build on the cluster ($HOME/dynamatic) has
dynamatic-opt (buffer placement, --lower-handshake-to-hw) and the Verilog library, but not export-rtl or its
generators, so no Dynamatic netlist could be made since August.

**Method** (research/tools/suite/dyn_all.sh, per kernel; the fixture is the one our flow builds from,
build/frontend/K/comp/handshake_transformed.mlir):
1. Buffers exactly as research/tools/suite/dynamatic_est.py places them: `--handshake-set-buffering-properties=version=fpga20
   --handshake-place-buffers=algorithm=on-merges` (Dynamatic's own pass; no MILP: the build has no solver), then
   `--handshake-canonicalize --handshake-hoist-ext-instances`, `--handshake-set-unit-impl-attr` (the units' latencies:
   muli 4, div / rem 35, as the estimator models them; on xorshift the lowered file is byte-identical with and without
   it) and `--lower-handshake-to-hw`.
2. research/tools/suite/dyn_export.py: export-rtl for the integer subset, from data/rtl-config-verilog.json and
   data/verilog (generic files copied unchanged; cmpi and constant generated from Dynamatic's own templates as its
   generators write them; a component needing any other generator is refused, not guessed).
3. research/tools/suite/dyn_vsim.py: the exported Verilog in iverilog on the calls dynamatic_est.py ran on the kernel's
   suite vectors (the C checks the estimator's results; memory kernels: a BRAM with a one-cycle read per memref, each
   call's arrays from the v2 vector file, every array compared with the C's after the call). A kernel counts only if
   every call's result (and arrays) and cycle count equal the estimator's. Negative controls on xorshift (a compare
   inverted, two constants with a bit flipped, the loop test inverted): caught on 19 / 16 / 1 / 16 of 19 calls.
4. research/tools/suite/dyn_route.sh: the 2026-08 method (cells/hw/dyn_baseline.sh: an I/O-bound wrapper, inputs off
   registers, outputs XOR-reduced into registers; yosys synth_xilinx -flatten -nosrl -nolutram -nobram -noclkbuf;
   nextpnr-xilinx --ignore-loops --timing-allow-fail --freq 250) on placer seeds 1-4; the period is 1000 / nextpnr's
   final "Max frequency for clock 'clk'".
5. research/tools/suite/dyn_apply.py: ns per iteration = the mean routed period x the estimator's simulated cycles per
   iteration (its fit over the calls; unchanged), tagged "measured, 4 routes"; latency per call = each call's
   simulated cycles x the mean routed period.

**What this is and is not.** The period is a routed figure on our part and toolchain, from Dynamatic's own netlist
for the same fixture; the cycles are simulated (Verilog = model, call for call). Not captured: Dynamatic's MILP buffer
placement (fpga20 / fpl22 need a solver the build lacks; on the memory kernels on-merges waits ~6 cycles per iteration
where a solver placement could reach 1, so those ratios flatter us); a board run of Dynamatic's circuit.
Added 2026-11-21 after audit T173 (numbers confirmed, wording overstated): "Verilog = model" means OUR export
checked against OUR model (dynamatic_est.py), not against Dynamatic's simulator, and 8 kernels have one call; the
period is nextpnr's static timing with --ignore-loops in an I/O wrapper with no BRAM (memory kernels' BRAMs are
not in the routed period), while our own column is the simulated event-graph period with draws -- two different
kinds of measurement. **Every nextpnr log behind a period here:** pnr_logs.tar.xz (248 logs, K/pnr_S.log for each
kernel and seed in K/route.txt); pnr_logs_manifest.tsv: each log's last "Max frequency for clock 'clk'" agrees with
route.txt on all 248.

## Results (2026-11-21 00:55 UTC; nextpnr 6e5d224472232d5d, seeds 1-4; per-kernel records in K/: route.txt, vsim.txt, est_summary.txt, hw_mlir_md5.txt)

**60 of the 62 suite kernels:** export checked exact on every call (results, arrays and cycles), routed on 4 seeds.
Not measured: **divmods** -- Dynamatic's own `data/verilog/arith/remsi.v` wraps an UNSIGNED remainder core
(`dynamatic_units_urem_32ns_32ns_32_36_1_div`): 15 of 24 calls (every one with a negative operand) give a result
different from the C, so its circuit does not compute divmods and has no figure; **test_stdint** -- the estimator
cannot run its v2 vectors (a scalar argument narrower than 32 bits), so there is nothing to check the export against.
Two seeds failed in nextpnr itself ("post-placement validity check failed for Bel ..A5FF (no cell)": twoloops seed 2,
lfsrfind seed 3) and were replaced by seed 5. digitsum and digitdiv are the same circuit (their fixtures are identical
but for the name: LLVM rewrites v % b as v - (v / b) * b).

**Against the estimates they replace** (50 kernels with both; the ratio is routed / estimated ns per iteration):
geometric mean **1.15**, range 0.78-2.25; 28 routed figures more than 10 % slower than the estimate, 8 more than 10 %
faster. So the estimator's one-factor fit flattered Dynamatic on most kernels: our ratios against the estimates were,
on the whole, too pessimistic. gcd keeps its composite unit in dynamatic_ref.tsv ((3.03 + 1.00) simulated cycles x the
routed period = 44.52 ns per main iteration and shift; the column below is the plain fit).

| kernel | Verilog check (calls, all exact) | routed period, mean of 4 (range), ns | simulated cycles per iteration | ns per iteration, routed | the estimate it replaces | routed / estimate |
|---|---|---|---|---|---|---|
| xorshift | 19 | 11.48 (11.11-11.72) | 1.00 | 11.48 | 11.92 | 0.96 |
| collatz | 17 | 13.79 (13.43-14.22) | 1.00 | 13.79 | 15.48 | 0.89 |
| collatz64 | 18 | 16.90 (16.73-17.14) | 1.00 | 16.90 | 17.11 | 0.99 |
| ipow | 17 | 9.12 (8.63-9.40) | 5.00 | 45.58 | 49.98 | 0.91 |
| gcd | 18 | 11.05 (10.09-12.42) | 0.99 | 10.92 | 12.42 | 0.88 |
| isprime | 18 | 11.74 (11.41-12.01) | 1.00 | 11.74 | 9.26 | 1.27 |
| straight | 12 | 14.66 (14.07-15.23) | - (no loop) | - | - | - |
| countloop | 10 | 11.73 (11.09-12.09) | 1.00 | 11.73 | 8.36 | 1.40 |
| sqrtsub | 13 | 12.11 (11.71-12.73) | 1.00 | 12.11 | 8.36 | 1.45 |
| nest3 | 12 | 12.80 (11.90-13.66) | 1.00 | 12.80 | 11.06 | 1.16 |
| twoloops | 11 | 11.81 (11.06-12.54) | 1.00 | 11.81 | 9.09 | 1.30 |
| brhash | 10 | 11.41 (10.95-12.20) | 3.00 | 34.22 | 36.40 | 0.94 |
| lfsrfind | 10 | 7.62 (7.38-8.10) | 2.00 | 15.28 | 19.52 | 0.78 |
| quadrec | 10 | 11.58 (11.24-11.95) | 1.00 | 11.58 | 9.09 | 1.27 |
| horner | 11 | 12.05 (11.62-12.36) | 5.00 | 60.24 | 41.81 | 1.44 |
| fold64 | 10 | 16.72 (15.41-18.08) | 1.00 | 16.72 | 11.93 | 1.40 |
| varshift | 10 | 12.48 (11.99-13.29) | 1.00 | 12.48 | 11.84 | 1.05 |
| cmpchain | 17 | 13.78 (13.37-14.22) | - (no loop) | - | - | - |
| nested | 11 | 13.76 (13.32-14.12) | 1.00 | 13.76 | 9.98 | 1.38 |
| branchloop | 14 | 8.35 (7.64-9.20) | 3.44 | 28.70 | 36.77 | 0.78 |
| digitsum | 18 | 11.91 (10.31-14.22) | 40.00 | 476.35 | - | - |
| digitdiv | 18 | 11.91 (10.31-14.22) | 40.00 | 476.35 | 303.77 | 1.57 |
| divmodu | 20 | 8.59 (7.35-11.27) | - (no loop) | - | - | - |
| divmods | Verilog check not clean (dyn_vsim divmods: 24 calls, 15 differ) | - | - | - | - | - |
| test_divui | 12 | 6.76 (5.95-7.27) | - (no loop) | - | - | - |
| memsum | 5 | 11.51 (11.20-11.81) | 5.98 | 68.88 | 59.33 | 1.16 |
| dot2 | 8 | 10.71 (10.12-11.25) | 5.98 | 64.03 | 59.28 | 1.08 |
| gather | 9 | 11.48 (10.76-12.09) | 6.98 | 80.12 | 69.20 | 1.16 |
| fill | 5 | 12.40 (12.00-12.63) | 1.00 | 12.40 | 10.95 | 1.13 |
| factorial | 12 | 14.05 (13.70-14.52) | 13.00 | 182.64 | 129.79 | 1.41 |
| iterative_division | 15 | 15.81 (15.47-16.25) | 1.00 | 15.83 | 10.23 | 1.55 |
| iterative_sqrt | 12 | 17.90 (17.15-19.65) | 9.98 | 178.63 | 110.84 | 1.61 |
| test_loop_free | 10 | 6.81 (6.37-7.09) | - (no loop) | - | - | - |
| test_int16 | 1 | 1.50 (1.34-1.66) | - (no loop) | - | - | - |
| test_bitint | 6 | 7.08 (6.88-7.24) | 5.44 | 38.52 | 44.32 | 0.87 |
| unused_arg | 6 | 3.36 (3.08-3.67) | - (no loop) | - | - | - |
| if_loop_1 | 8 | 11.71 (11.30-12.38) | 1.99 | 23.34 | 19.90 | 1.17 |
| if_loop_2 | 8 | 11.26 (10.59-11.87) | 1.99 | 22.45 | 16.67 | 1.35 |
| sumi3_mem | 3 | 8.47 (7.73-9.40) | 9.99 | 84.60 | 88.44 | 0.96 |
| fir | 2 | 8.62 (8.45-8.90) | 6.00 | 51.66 | 48.68 | 1.06 |
| simple_example_1 | 4 | 5.63 (5.42-5.83) | - (no loop) | - | - | - |
| while_loop_3 | 7 | 10.12 (9.69-10.55) | 5.00 | 50.60 | 34.00 | 1.49 |
| if_convert | 3 | 13.42 (12.93-14.14) | 6.00 | 80.54 | 65.70 | 1.23 |
| test_memory_1 | 6 | 11.56 (10.51-12.23) | 1.78 | 20.56 | 13.94 | 1.48 |
| test_memory_2 | 7 | 11.49 (10.85-12.19) | 1.78 | 20.41 | 13.94 | 1.46 |
| test_bool_array | 4 | 2.91 (2.86-3.05) | - (no loop) | - | - | - |
| binary_search | 7 | 10.18 (10.00-10.45) | 3.02 | 30.80 | 24.18 | 1.27 |
| mul_example | 3 | 7.18 (6.84-7.36) | 9.91 | 71.10 | 79.88 | 0.89 |
| share_test_2 | 3 | 8.72 (8.10-9.52) | 8.92 | 77.75 | 91.89 | 0.85 |
| test_stdint | Verilog check not clean (['dyn_vsim: no ok call lines in /tmp/bot/dynroute3/test_stdint/es | - | - | - | 80.67 | - |
| spmv | 4 | 13.88 (13.58-14.29) | 6.97 | 96.81 | 43.09 | 2.25 |
| sobel | 3 | 14.56 (13.98-15.06) | 4.67 | 67.97 | 43.37 | 1.57 |
| test_flatten_array | 1 | 7.56 (7.23-7.70) | 1.93 | 14.61 | 15.74 | 0.93 |
| image_resize | 2 | 8.17 (8.11-8.33) | 1.97 | 16.07 | 18.95 | 0.85 |
| vector_rescale | 2 | 8.45 (8.20-9.09) | 6.00 | 50.68 | 48.68 | 1.04 |
| stencil_2d | 1 | 8.12 (8.01-8.25) | 4.66 | 37.83 | 40.43 | 0.94 |
| iir | 1 | 9.25 (8.85-9.62) | 6.00 | 55.47 | 48.68 | 1.14 |
| share_test_1 | 1 | 10.44 (9.87-10.85) | 6.00 | 62.58 | 58.41 | 1.07 |
| single_loop | 1 | 8.57 (8.11-9.17) | 6.00 | 51.41 | 40.32 | 1.27 |
| loop_path | 1 | 14.82 (13.95-16.41) | 2.00 | 29.63 | 32.27 | 0.92 |
| nested_loop | 1 | 8.67 (8.31-9.03) | 6.00 | 52.01 | 44.56 | 1.17 |
| video_filter | 1 | 9.45 (9.30-9.63) | 5.93 | 56.02 | 57.14 | 0.98 |
