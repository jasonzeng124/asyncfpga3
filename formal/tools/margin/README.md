# formal/tools/margin: race margins of a routed build (shard C; UNTRUSTED unless a row says Lean)

Goal (formal/PROGRAM.md, first section): `run.sh BUILD.fasm OUT/` reports, at g = 1 with and without H_RUNT(20),
every race that can break the build, kappa* (the smallest failing within-die scatter) with its race in the build's
instance names, and a failing delay assignment just above kappa* (or "none found"). Status: v0 being assembled
(2026-11-15); nothing here is a result yet.

## Pipeline (v0)
1. Decode the FASM read back from the `.bit` into the gate list (shard A's `tools-A/target/decode_base.py`,
   `build_net.py`; prjxray arcs per pin: FAST_MIN/FAST_MAX/SLOW_MIN/SLOW_MAX) and name the kernel boundary.
2. Static race scans, each a RANKING (pessimistic: joins are not modelled), one per race class below.
3. Adversary: for the top candidates of each class, transport simulation of the decoded net (tools/huff/simadv.py)
   with the candidate's slow side at (1+k)·slow end and everything else at (1-k)·fast end, over a kappa grid with
   bisection, on several (wide and narrow) vectors; a failing run is checked by gatecheck_runt.py (every delay in
   Spec.Adm, every gate relation) and envcheck.py (Env, SeqEnv, ArbOK) before it is reported.
4. Report: OUT/margins.txt (one row per race: class, node, pin, sources, static kappa, adversary verdict) and
   OUT/summary.txt (kappa*, binding race, trace file).

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
