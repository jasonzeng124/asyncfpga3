# The compiler suite (PROGRAM "A benchmark suite for the compiler", owner 2026-11-17)

**Status 2026-11-18 07:00 UTC.** The one command works end to end; the first complete run is the six original kernels'
four fast ones (farm suite4, flow v3, 8 seeds, 8 draws per route): every judged route right on every draw.

| kernel | status | routes judged / built | draws passing | ns per iteration (P), median (range) | worst latency per call, ns | kernel LUTs | Dynamatic, ns per iteration | ratio | hand recipe's best, ns |
|---|---|---|---|---|---|---|---|---|---|
| collatz | PASS | 7 / 7 | 56 / 56 | 18.98 (17.71-20.60) | 5436 | 1220 | 14.05 (measured, 1 route) | 1.35 | 21.50 |
| collatz64 | PASS | 5 / 5 | 40 / 40 | 23.71 (21.50-27.86) | 9804 | 1775 | 17.84 (measured, 1 route) | 1.33 | 31.40 |
| ipow | PASS | 8 / 8 | 64 / 64 | 24.10 (21.47-25.00) | 828 | 1317 | 49.98 (ESTIMATE) | 0.48 | 36.20 |
| xorshift | PASS | 7 / 8 | 56 / 56 | 20.11 (18.87-20.49) | 5304 | 1362 | 12.73 (measured, 1 route) | 1.58 | 16.76 |

4 of 4 kernels pass; geometric mean of the ratio (ns per iteration / Dynamatic's) over passing kernels with a MEASURED Dynamatic figure (n = 3): 1.42; including ESTIMATED figures (n = 4): 1.08. Our ns are the simulation's (about 8 % slower per iteration than the August board on the same bitstreams, research/SIM-VS-BOARD.md); Dynamatic's measured figures are single nextpnr routes (Fmax), not board runs.

Pending: the 16 suite kernels (farm suite3), gcd / isprime (suite5 / suite7), flow v6 on the original kernels (suite6),
Dynamatic's integer tests and the read-only memory shapes (subagent suitew). kernels.txt lists 23 kernels today.

## The one command

    RUNS=... research/tools/suite/run_suite.sh [-j JOBS] [-s "SEEDS"] [-d NDRAWS] [-m MAXIT] [KERNEL...]

For every kernel (default: research/tools/suite/kernels.txt) and every seed (default 1 2 3 4), `suite_one.sh`:
1. builds the kernel with `BDC_AUTO=1` (bdc/auto.py: storage rules M and F, ring-floor counting, link fast fall, the
   constant-data fusion, the formally proven MLIR rewrites where they apply) and sizes it with the flow's own loop,
   `research/tools/auto/auto_size.sh`: emit.py's estimates, then the one sizing rule (corner_audit.py `CA_SIZERULE=1`,
   C-element joins) on each route as built, re-routing until the rule is clean on the route it is checking (lines the
   rule ever lengthened are pinned; the loop goes on while a clean route still shortens a line; it ships the last
   clean route). No sizes file, no factor, no instance name, nothing set for the kernel by name;
2. checks the bits (the netlist decoded from the bitstream EQUIVALENT to nextpnr's, `ffmux_scan` clean): a route that
   fails is reported, not judged (it is not what the board would run);
3. runs NDRAWS draws of the delay model (bench_gate.sh draw:K, K = 10000 + 100 * seed + j, so every route gets its own
   model points) on the kernel's vectors, every answer compared with values compiled from the C at run time;
4. records the timed event graph's period P on the kernel's period vector, the worst latency per call, the kernel's
   LUTs.
`suite_table.py` writes one row per kernel (status, routes judged / built, draws passing, P median and range, latency,
LUTs, Dynamatic's figure with how it was obtained, the ratio) and a last line: how many of N pass, and the geometric mean
of the ratio.

## What "pass" means
Every draw on every judged route returned every right answer, and at least one route was judged. A kernel that does not
compile, gives a wrong answer, or never produces a board route stays in the table with that status.

## Not yet
- Kernels beyond the six (the suite subagents are writing about twelve scalar kernels, one per shape; Dynamatic's
  integer tests: 12 emit, 4 fit today's bench -- research/data/suite/dyn/); memory kernels wait for the bench's array
  ABI (cells/hw/gen_bench.py writes invalid Verilog for array arguments today).
- Dynamatic's figure: measured for three kernels only (single 2026-08 routes); an estimator from Dynamatic's own
  buffer placement and timing model is being written (research/data/suite/dynamatic/).
- Full-range paths no vector reaches (loop counters' long carries) are judged by the static rule only, unless a
  preloaded run covers them (research/data/preload/; formal B2/B3).
