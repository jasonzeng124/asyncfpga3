# formal/tools/margin: race margins of a routed build (shard C; UNTRUSTED unless a row says Lean)

Goal (formal/PROGRAM.md, first section): `run.sh BUILD.fasm OUT/` reports, at g = 1 with and without H_RUNT(20),
every race that can break the build, kappa* (the smallest failing within-die scatter) with its race in the build's
instance names, and a failing delay assignment just above kappa* (or "none found"). Status: v0 being assembled
(2026-11-15); nothing here is a result yet.

## Run it (from a clean checkout of claude/formal; needs python3, g++, prjxray-db under $TC)
gcd_ps-style build (XDC, yosys JSON and routed JSON next to the FASM):
    SIM=simx LATCH=1 bash formal/tools/margin/run.sh formal/target/gcd_ps_e6bb4aec.fromBit.fasm.xz OUT/
research bench build, from its build tree (cells/build/...):
    SIM=simx LATCH=1 KERNEL=collatz PAIRS="27,27 703,703" TFULL=25000000 KLO=0.0 \
      SYNTH=cells/build/hw/collatz_bench_gen/collatz_bench_gen.json ROUTED=cells/build/hw/collatz_bench_gen/collatz_bench_gen_routed.json \
      KV=cells/build/gen/collatz_kernel_bench.v BV=cells/build/gen/collatz_bench_gen.v \
      bash formal/tools/margin/run.sh cells/build/hw/collatz_bench_gen/collatz_bench_gen.fasm OUT/
Output: OUT/kappa_hi.txt (the result: smallest kappa with an ADMISSIBLE failing run, per runt filter w; kappa_lo is
always "none" here: nothing is proved), OUT/checked.txt (every failing row re-run and checked), OUT/margins.txt (every
candidate row), OUT/witness/ (commands to replay). Knobs in run.sh's header (JOBS, KHI, KLO, W0, PAIRS, KERNEL, TFULL,
SHARD, ONLY). Cost: gcd_ps (16,990 pins) 23 min on 4 cores; bench builds 1-15 min.

## Pipeline
1. Decode the FASM into the gate list with prjxray arcs per pin (shard A's decode_base.py, build_net.py) and name the
   kernel boundary (boundary_ps.py, or boundary_bench.py + mk_bnd_sim.py for bench builds).
2. Candidates: every live pin of every storage LUT (a LUT reading its own output; LATCH=1 includes latch-like ones),
   ranked by a reference run; pins that never move in the reference runs are skipped (a coverage gap).
3. Adversary: the candidate's route at floor((1+k)·FAST_MAX), every other arc at ceil((1-k)·FAST_MIN) (corner 0,
   inside Spec.Adm at g = 1, scatter k), transport, H_RUNT(20) filter and without; one run per kappa with all vectors;
   failing candidates bisected on the 0.01 grid. Runs hitting the event cap are UNDECIDED, not failures.
4. checkrows.py: every failing row re-run with a dump; gatecheck.py (every gate relation, every delay in Adm, the
   H_RUNT read-lag bound) and envcheck.py (Env, SeqEnv, ArbOK T, out0). Only ADMISSIBLE failures enter kappa_hi.

## Results so far (search, untrusted; kappa_hi only)
gcd_ps 0.36 (w 20), 0.44 also; BAD_xf2_1 0.00; item 23 none <= 0.45; item 25 0.44 (w 0). Details: out/<build>/,
JOURNAL-C.md 2026-11-15.

## Simulator
`SIM=simx` (recommended): `simx.cpp` (g++ -O2 -std=c++17), a C++ port of tools/huff/simadv.py's options the sweep
uses, with the net converted once by `simx_conv.py`. Verified identical to simadv (stdout, events, every node's flip
times in the dump) on 7 gcd_ps runs incl. the 0.40 deadlock, the 0.36 livelock and a w = 0 run; 30-58x faster.
`--maxev` (default 1e8 via SIMX_MAXEV) bounds livelocks: a capped run is UNDECIDED, not a pass. Bench kernels:
`KERNEL=collatz|collatz64|xorshift`, expected values from kernels.py (from kernels/*.c).

## Race classes (completeness is the point: a race class missing here is a margin the tool cannot see)
| class | what races | static scan | known instance on gcd_ps |
|---|---|---|---|
| F feedback | a storage LUT's own loop vs the return path of its switch to a forcing pin | tools-B/ps/allpaths.py | 0.44 (SLICE_X32Y45.A6) |
| K fork | a storage LUT's input route vs a detour from the same source to another of its pins | forkrace.py | 0.40 / 0.36 (SLICE_X16Y21.A6 pin 0) |
| L latch capture | latch data vs enable close (setup, hold; rules H/I; select race) | B's select-race work | none found to 0.43 |
| A arbiter | grant/state settling vs H_ARB(T) | arbiter rows | 0.43 livelock (excluded by H_ARB) |
| E boundary | the environment's timing (Δo, su) | envcheck.py | finding 4 of BOUNDARY-ps.md |
Not covered yet: multi-route adversaries (two slow routes at once), glitch (runt) propagation into hold addresses
other than through one slow pin, corners other than 0 and 1.
