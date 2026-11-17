# formal/tools/margin: race margins of a routed build (shard C; UNTRUSTED unless a row says Lean)

Goal (formal/PROGRAM.md, first section): `run.sh BUILD.fasm OUT/` reports, at g = 1 with and without H_RUNT(20),
every race that can break the build, kappa* (the smallest failing within-die scatter) with its race in the build's
instance names, and a failing delay assignment just above kappa* (or "none found"). Status (2026-11-16): in use on
research's builds via the farm; every number is search (kappa_hi), none is a proof (kappa_lo: none).

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
gcd_ps 0.36 livelock / 0.40 finite (w 20); BAD_xf2_1 0.00; item 23 none <= 0.45; item 25 0.42 (w 0); item 26 0.26;
item 28 (collatz board candidate) 0.42; fcsel0-2 0.21-0.32, fcsel3m other seeds 0.27-0.41; item 27 single-pin none <= 0.45,
capture 0.39. The live table is formal/FOR-RESEARCH.md (C items) and formal/target/MARGINS.md. Details: out/<build>/,
JOURNAL-C.md 2026-11-15/16.

## The race in picoseconds (2026-11-16; PROGRAM "A kappa is not a result")
- `explain.py OUT NODE PIN KAPPA [--w W] [--routed R] [--sdf SDF]` (run.sh step 5 runs it on every reported race; give
  `SDF=`): re-runs the witness and an all-fast reference, finds the CAPTURE (the storage LUT where the race bites),
  the two racing arrivals, their common launch (where the two trigger chains -- at each gate the input that fired it --
  meet), and both paths with every LUT, cells / routing apart, at the prjxray fast and slow band midpoints, the worst
  in-band split and nextpnr's SDF; the slack as a multiple of the median (8.5 %) and worst short-ring (47 %) delay
  error of the August ring data. CLASS BOUNDARY when a path crosses the host (the next input released after an
  acknowledge), KERNEL otherwise. Cone rows: aligned by capture count; stalls list the earliest new short pulses.
  Paths that revisit gates are reported UNRELIABLE (no slack).
- `HOSTDELAY=H` (simx `--hostdelay`): the host moves input data H ps after the acknowledge it reacts to (default 1,
  the most adversarial host Spec.Env allows). H = 2000 or 12000 (one PS clock) leaves the kernel's own races.
- `fbslack.py BUILD.sdf [--grep .ctl.]`: static screen from the SDF alone (5 s): for every LUT reading its own output,
  its feedback (A) against the fastest structural return to another of its pins (B). run.sh writes fbslack*.txt.
- `minimize.py OUT NODE PIN KAPPA [--w W]`: delta debugging over a cone row's slowed arcs; the minimal failing set
  becomes row PIN+200 (explain.py / checkrows take it).
- `tcut.py OUT NODE PIN KAPPA [--w W] [--routed R]` (run.sh TCUT=1): WHEN a cone / steer row's slow arcs do the
  damage. simx `--tcut T` keeps the class-S arcs slow for input changes before T and gives them their F delay after
  (FIFO across the cut, so no transition overtakes an earlier one). Bisection gives T* with run(T*) failing and
  run(T*-1) passing. The two runs differ by 1 ps in the transitions in flight at the cut, so their first diverging
  storage LUT is where the race is decided (0 slack). RUNT flags a pulse narrower than H_RUNT's 20 ps at the first
  diverging LUTs. Without `--tcut`, simx output is unchanged (checked event for event on item 25 at w 20).

## The board approximator (2026-11-16; PROGRAM "The board decides"): `DRAWS=N`
`DRAWS=64 run.sh BUILD.fasm OUT/` (bench builds as above) skips the adversary and runs `draws.py`: N random draws of
every arc's delay on the circuit decoded from the bitstream, and the fraction of draws returning the right answers.
Model (research's fid GLS, research/data/fid/f3_model.md + ring128_summary.md, sized on the August ring data): each pin
arc (cell + route) = (FAST_MIN + 0.38 (SLOW_MAX - FAST_MIN)) x exp(0.16 N_region) x exp(0.126 N_arc), N_region one
normal per 10x10-slice region, N_arc one per arc, from a hash of the draw seed (simx `--draw SEED --band --sreg --sarc
--regsize`). H_RUNT(20) (DRAW_W), host 12 ns after each acknowledge (HOSTDELAY), start-up unchanged. Outputs
draws_summary.txt (PASS / FAIL / UNDECIDED, Wilson 95 % interval, last-answer times) and draws.txt (one line a draw).
Checks so far: gcd_ps 4/4 pass and the draws differ (last answer 7.47-7.78 us); with sigma_arc 0.6 / sigma_region 0.3
2 of 15 decided draws fail (the approximator can fail). Differences from research's GLS: scatter per pin arc, not per
pip; transport LUTs with the 20-ps filter instead of research's resolver. Untrusted simulation; no Lean.
`DRAW_MODEL=research` (default since 2026-11-16 20:3x): research's draw K exactly (FOR-FORMAL: bands per class from
Random(7919K+17): delay chains / the rest U[.20,.31], CARRY4/F7/F8 U[.20,1.0]; region 0.02; per-pip 0.126); gate classes
from routed.json (`gclass.txt`). **Host fix (2026-11-16 21:5x):** with `--datachange broad` and HOSTDELAY > the time to
the next offer, simx raised the next request BEFORE its data (a boundary violation by the harness; it produced the
withdrawn FOR-RESEARCH C21). The request now waits for its data + su. Margin-tool runs with HOSTDELAY >= 2000 before this
fix share the defect where an answer came back faster than HOSTDELAY (zero-trip calls); their vectors had none.
**Near misses (2026-11-17, informational, verdicts unchanged):** simx prints `NEARMISS` (storage-LUT output pulses
narrower than NEARMISS_PS = 200 ps after reset; the 3 narrowest) and, with env `RACES=1`, `RACES` lines: at every
evaluation of a storage LUT (class storage) or of a LUT a storage LUT reads (class feeding-storage), each other pin q that
arrived gap < RACES_PS (300) ps earlier and whose old value would have given an output different from both the new and the
previous one (a latch setup / hold, a steer condition against its request); per (gate, pin) the smallest gap, the 5
closest printed. draws.py appends both to each draw line and lists the closest over all draws in draws_summary.txt. Toy
check: `RACES=1 simx test/toy_latch.simx --kernel collatz --want 1,0,1 --pairs 1,1 0,0 1,1 --corner 0 --kappa 0 --classes
/dev/null --data0 --full --R 4000 --su 100 --datachange broad --nextreq seq --tmax 100000 --hostdelay 500` reports the latch's
D arriving 49 ps before its enable closes (with RACES_T0=0; by default the first 5 ns after reset release are skipped, as start-up settling, for RACES and NEARMISS alike). Transparent latches legitimately pass D glitches: a small gap is a pointer
for tracing, not a failure.
**Naming a race and its slack in ps (2026-11-17):** `chainfix.py OUT --kernel K --pairs .. --bands bc,br,bx [--extra PS]
[--only REGEX]`: for a run that fails, adds PS to one delay chain at a time (its g[0] input arcs), uniform bands, no
scatter; the chains that turn it into a PASS are the matched delays that are too short (smallest fixing PS = the
shortfall). `sideslack.py OUT CELLREGEX --kernel K --pairs .. --bands ..`: for a run that passes, adds X to every input arc
of the named LUTs (a race's slow side, e.g. a compare's last LUT) and bisects the first failing X (16 ps): the slack.
Both inject outside the prjxray band (simx `--classes {"I": ...}`); positive injections only. sideslack's number is a
CONSEQUENCE slack (later until a wrong answer), an upper bound of the settle margin. `steermargin.py OUT CONDREGEX --kernel K
--pairs .. --bands b,b,b`: the settle margin itself: every LUT reading the condition, its request pins (sources named
'_j.' / '.ctl.'), and per request rise the time since the condition last arrived, plus how many requests see the condition
move under them (live steer runts). Checked against the audit's T139 on item 35 (ucond_br2: 363 ps at FAST_MIN; T139
264-485 ps).
`diverge.py NET A.json B.json --routed R`: the nodes where two dumps part, LUTs whose flip count differs, with names.

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
| L latch hold | a latch's enable reaches it late (closes after the next data arrives; rules H/I) | single-pin (LATCH=1) | binding on every collatz build (ulink_n13, ulink_n_falseResult_3 st0) |
| C capture (setup / arrival) | a link's whole data cone slow, its request fast: data (incl. a mux SELECT, rule E) arrives after the latch closes | cones.py (`CONES=1`) | gcd_ps 0.61 (wrong values from 0.77); collatz: the select link ulink_n_index_11 st0 first |
| S steer capture | a C-element / steer reading data (a branch condition) through logic, that cone slow | cones.py --steer (`STEER=1`) | item 25 0.62 (w 20) |
| A arbiter | grant/state settling vs H_ARB(T) | arbiter rows | 0.43 livelock (excluded by H_ARB) |
| E boundary | the environment's timing (Δo, su) | envcheck.py | finding 4 of BOUNDARY-ps.md |
Not covered yet: multi-route adversaries other than the C/S cones, glitch (runt) propagation into hold addresses
other than through one slow pin, corners other than 0 and 1.

## What counts as a failure (2026-11-16)
- FAIL-wrong (a wrong value) and FAIL-quiet (quiet with an answer missing): finite witnesses, checked by gatecheck +
  envcheck; only ADMISSIBLE ones give kappa_hi.
- FAIL-livelock: never quiet, never answering, and `simx --periodic` found the run eventually periodic (whole history
  over the longest read look-back repeats with period P, boundary and env idle). Checked to the start of the period;
  the infinite extension rests on the C++ periodicity check (untrusted). Listed on its own kappa_hi.txt line.
  gcd_ps 0.36: period 79 ps, as Lean's Frontier36.
- FAIL-noanswer without a period, UNDECIDED (event/memory cap): not failures.
- INFEASIBLE (w > 0): some LUT read lands in a narrow-pulse chain longer than its delay window; no H_RUNT(w) read map
  exists, so the run is no behaviour; not a failure (the bisection moves on).
- Env rejections: a row whose gate checks are clean but whose simulated harness broke Spec.Env (it released data on an
  acknowledge that then glitched) is re-run with `--datachange next`. PARTIAL-ACK DEADLOCK (the kernel acknowledged
  some input channels of the shared request, not all, and stopped): Spec.Env has no continuation, so the frozen
  statement is vacuous there; listed as PHYSICAL (a real harness hangs), not as a Spec counterexample.

## DSP48E1 (2026-11-17): ipow builds
A FASM with `DSP48.` config lines is decoded by `dsp/decode_dsp.py` (wraps A's decode_base.py; every DSP register must be
off; control pins must be constants; unsupported modes refused) and `dsp/dsp_gates.py` (one combinational `dsp` gate per
read P/PCOUT bit; `--check N`: the decoded multiplies against x*y mod 2^32). Delay arcs from prjxray timings/DSP_{L,R}.sdf
(`DSP_SDF=nextpnr.sdf` widens the slow end to nextpnr's). Negative control knob `DSP_CORRUPT=SITE:opmode|alumode|inmode:BIT`.
`dsp/force_pin.py` ties one decoded cell pin to a constant (what-if). Not covered: simadv.py (adversary), Lean.
