# The all-kernel table at DEFAULT settings (PROGRAM "General first", item 3) -- 2026-11-17

Subagent C. The baseline column for BDC_AUTO: every fixture kernel through the bench flow with nothing set per kernel.

## The table

ns per iteration. "default" = this directory's routes (definition below); "hand" = the best hand recipe; Dynamatic from
research/data/dynamatic_ref (measured = 1 route, default seed; EST = cycles x a borrowed clock). Ratios are
time / Dynamatic's time (> 1 = slower than Dynamatic).

TABLE_PLACEHOLDER

## What "default" means here, and what it is not

- `cells/hw/build_bench.sh K` with `BD_NO_TIGHTEN=1 BD_SIZES=none BD_DSP=1 NEXTPNR_SEED=s` (TARGET_MHZ default 83 ->
  `--freq 83`), no `BDC_*` variable, no sizes file, no MLIR pre-pass: every matched delay at bdc's own placeholder
  (`bdc/compute.py default_delay`: "deliberately generous", meant to be shortened by tighten.py after routing).
  Script: `run_default.sh` (lane2.sh's steps without the git worktree: builds in a plain copy of cells/ bdc/
  build/frontend). nextpnr 9c732bc6303458df, toolchain.sh all ok.
- A BARE `build_bench.sh K` does more: it execs `hw/tighten_loop.sh` (rule A outer / rule E inner, up to 6 routes per
  build) and keeps the shortest sizes that pass on their own route. That is automatic (no per-kernel input), so it is
  arguably part of the default compiler; it was NOT run here (>= 2-6 place-and-routes per route; the machine allows one
  at a time). The column is therefore "placeholder sizes", the upper bound the automatic path starts from.
- ns / iteration = the timed event graph's period P (research/tools/eventgraph/eventgraph.py, marker auto) on the
  itercost full stack (fullstack_dump.sh: bits-decoded netlist, prjxray SDF, fid, chains 0.21, CARRY4/F7F8/FF 1, rest
  0.288, no scatter) -- the same stack and method as every hand number in fifteen/README.md and BOARD-QUEUE (median of
  routes there). One iteration = one token round the loop's ring, with the same vector the hand numbers used:
  xorshift one round (vec_xorshift: 92d68ca2 x 256), collatz / collatz64 one Collatz step (vec_collatz n=6171,
  vec_c64_871), ipow one exponent bit (vec_ipow 3^(2^31-1)); checked against the run's own latency / trip count.
- gcd and isprime have nested loops, so one period is not "an iteration". They get the cost model the hand numbers
  use: latency per vector fitted to the replayed loop counters -- gcd: research/tools/aug_cost_fit.py on the 24 August
  (a, b) pairs (aug_gcd/gcdcost_vec.hex; per main subtract iteration, per inner ctz shift; x 1.2 because the fit
  assumes 10 ns host cycles and the sim runs 12 ns), isprime: `isprime_fit.py` (cells/hw/isprime_cost_fit.py's
  model: per outer trial, per inner shift step) on `vec_isprime_cost.hex` (18 n's of cells/hw/isprime_cost_results.tsv
  with board latency <= ~4000 cycles).
- Correctness: research/tools/eventgraph/bench_gate.sh at `worst` (chains 0.21, CARRY4/F7F8/FF 1, rest 0.288, + M
  scatter) on seed 1, with the gate vectors and the oracle compiled from the C (kernel_oracle.sh; gcd_oracle.sh).
  isprime had no gate vectors: `isp17.hex` / `isp17.exp` here (oracle: kernel_oracle.sh, isprime case added today).
  isprime returns only 0 / 1, so the gate's value check is weak (0 = composite = a plausible failure value); a hang
  or wrong-prime still shows.

## Kernels that do not build through the bench flow (default settings)

RESULTS_FLOW

## Shapes missing (for the owner's frontend)

SHAPES
