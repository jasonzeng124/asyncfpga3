# Autonomous research program

You are the only agent working on branch `claude/research`. Nobody will answer
questions: decide, record why in the journal, and keep going. The owner reads
`research/JOURNAL.md` and `research/BOARD-QUEUE.md` and runs the board.

## No board for a long time (owner, 2026-10-25)

Nobody will run anything on silicon for the foreseeable future. Keep adding to
`BOARD-QUEUE.md` (one short entry per candidate; don't commit a bitstream for
each one), but never wait on it and never count it as verification. Goal 1 is
therefore as strong as the evidence available without a board, so make that
evidence stronger:
- more seeds (8+ for anything you ship as a default), with the worst seed
  reported, not just the mean;
- routed GLS at the slow AND fast corners of the SDF, plus delay scatter
  injected around the routed values (at least the measured 8.5% median ring
  scatter, and the tails beyond it), showing which margin fails first;
- negative controls that prove each audit and each GLS check can fail;
- re-checking the August silicon failures (bitstream bugs, memory inference,
  async latch, stale operands) as regression tests, wherever they can be
  reproduced without a board.

## THE priority: a board-fidelity gate-level simulation (owner, 2026-10-27)

The owner considers this the most important thing for developing without a
board. It comes before every speed lead. Give it the main thread, and the most
subagents, until it is done. Other work only fills idle cores.

### The audits are heuristics; an accurate GLS is the ground truth

The post-route rules (A/E/F/H/I/J, `tighten.py`, `skew.py`) are heuristics:
fast screens that say where to look and propose sizes. The ground truth is
meant to be a very accurate gate-level simulation of the routed FPGA. The
data for one exists in prjxray, so build it. This is the top lead under
goal 1, and it also unlocks goal 2: today a rule violation blocks a build
even when routed GLS passes, and that is where most of the remaining speed
is held back.

Why today's GLS is not that ground truth yet: `cells/gls/` simulates
nextpnr's SDF, and nextpnr's `getPipDelay` (`xilinx/arch.h`) is a single
number per pip. It is the pip's max delay plus one lumped RC term, with
the upstream wire length guessed from the Manhattan distance to the driving
pip. There is no fanout loading, no rise/fall, no fast corner, LUT
route-throughs are a flat 300 ps and site pips are 25 ps. The x0.9/x1.1
"corners" only scale those numbers. Silicon already disagreed: 76 of 128
rings ran slower than the SDF, by an offset of about +988 ps.

What prjxray's numbers are, and what they are not: they were extracted from
Vivado's timing model (`prjxray/fuzzers/007-timing`). prjxray's reduced model
matches Vivado to about +/-1.5% on most nets; clock nets are the exception
(`prjxray/minitests/timing/README.md`). Vivado's model is a sign-off model:
fast/slow, min/max corner bounds across PVT for a speed grade. It is not the
delay of this chip. Expect the board to fall inside [fast min, slow max] and
not on any one corner, and expect paths on one die not to sit at the same
point in that band. Check which speed grade the zynq7 data is for (the board
is -1). The ring data says where in the band this board sits. If a ring runs
slower than prjxray's slow max, the model or the comparison is wrong: chase
that before anything else.

Build it:
- A delay calculator that takes the routed design (`*_routed.json`: each
  net's pip list, so the real RC tree) and prjxray-db `zynq7/`
  (`tile_type_*.json`: pip intrinsic delays at 4 corners, pip and wire R/C;
  `timings/*.sdf`: cell arcs with rise/fall, fast/slow). Compute every
  sink's delay with the Elmore RC tree in `prjxray/prjxray/timing.py`
  (Outpin/Buffer/PassTransistor/Wire/Inpin, pi-model wires, `PvtCorner`);
  reuse it, don't rewrite it. Emit an SDF with min:typ:max per arc that
  `gls/gen.py` can read in place of nextpnr's.
- Check it on small cases by hand (one buffered pip; one pass-transistor
  chain; a fanout-of-N net) and against nextpnr's numbers. Explain every
  large disagreement before trusting either.
- **Validate against silicon already in the repo:** the n=128 ring
  measurements and the five rings in `cells/hw/README.md`, plus the
  board-measured kernel timings (gcd 310 ns to 6.34 us, the ns-per-iteration
  table) wherever the measured bitstream's route can be reproduced. Report the
  model's error distribution (median, tails, and whether it depends on length).
  What is left over becomes the scatter that GLS injects, and the measured
  ring scatter remains a floor.

Delay is not the only gap. A board-fidelity sim also needs:
- **The netlist the board actually runs.** Build the simulation netlist from
  the FASM or bitstream (with prjxray-db's segbits; look at existing fasm2bels
  work first) rather than from nextpnr's routed JSON. Three of the four worst
  bugs here were in the bitstream, where the netlist, the SDF and every
  simulation were correct. `fasm_audit.py` checks LUTs and DSPs only. A sim
  built from the FASM covers routing and every other bit.
- **Glitches and pulses as silicon has them.** Wires are already transport
  delays (`prims.v`). LUTs, MUXF7/8 and FF clock/SR pins still use iverilog
  module-path (inertial) delays, which swallow narrow pulses. A LUT is evaluated
  as a zero-time mux tree, so its internal hazards on multi-input changes are
  not modelled. Model what the silicon does (look for published LUT hazard
  behaviour), or show that no C-element or latch in the library depends on it.
- **Metastability.** The arbiter and synchronizers resolve in zero time in sim.
  Model near-simultaneous arrivals: random resolution time, or X, both
  choices exercised.
- **Within-die variation.** Use correlated per-region scatter plus per-wire
  random scatter, both sized from the ring data, not a single global scale.

### Acceptance: the sim must reproduce the board
Before the sim is trusted, it has to reproduce what silicon already showed,
from the same bitstreams or rebuilt identical routes:
- **timings:** the ring periods (n=128) and the board-measured kernel timings,
  within the measured scatter;
- **failures:** each August failure that was observed on silicon, simulated
  from the failing bitstream: gcd's livelock (the lut-pinmap bug), abs going
  negative, the gcd_bench_gen hang (the async latch corrupting the state
  register), the DSP products gated to zero, isprime's late read. A sim that
  passes a bitstream the board failed is not board-fidelity.

The owner is not sure how accurate the statistics on some of those board
failures are. Before using a silicon datum as an acceptance test, grade it
from what is on record: sample size; whether it was reproduced; whether the
instrument was itself verified (two board probes read stale operands, and
one checker was blind at all 24 points); and whether the stated cause was
later revised. Use only the well-established data as hard acceptance tests.
Deterministic bitstream bugs (lut-pinmap, dsp-constpins, dsp-areg) and the
n=128 ring set are good candidates. Treat the rest as soft evidence, and say
which is which in the journal. A soft datum the sim disagrees with is
something to look into, not proof that the model is wrong.

Write down each mismatch against hard data, then fix the model, not the test.

### Once it passes acceptance
A design is verified when this sim passes it: slow and fast corners, the
measured residual as scatter, at least 8 seeds, and derived oracles. **The
rules then do not matter.** They are possibly-inaccurate heuristics. Use them
to propose sizes and to say where to look, and never as a gate. Remove rule
gates from the ship path (keep the scripts as tools). A GLS failure always
blocks. Until acceptance is met, keep the current gates exactly as they are.

## Goals, in strict priority order

1. **Works on hardware, as far as can be verified without a board.** A faster
   design that might fail on silicon is worth less than nothing. The
   verification ladder, weakest to strongest:
   `cells/check.sh` gates, then every post-route audit in `cells/verify/`
   (rules A/E/H, loop audits, `tighten.py`), then routed back-annotated GLS
   (`cells/gls/`) across at least 4 placer seeds, with oracles derived from the
   C in `kernels/`. Anything that reaches the top of this ladder goes into
   `BOARD-QUEUE.md` with the exact command and the pass criterion. Prove that
   each audit can fail before trusting it to pass.
2. **As fast as possible.** The metric is ns per loop iteration (the critical
   cycle; delay sums do not predict it) and transaction latency for each kernel
   in `kernels/`. Report means across seeds, compared against the numbers in
   README.md and the most recent journal entry. Leads already known, in no
   particular order: rule E blocks tightening (rule A alone gave 1.99x on the
   board); enable replication for `bd_mux` control inputs; launch selection in
   rule E; placement (`rloc_stamp.py`); per-kernel RTZ tail (gcd pays 23
   cycles, cause unexplained); two-phase links (`bd_mlink.v`, standalone so
   far). A speedup counts only if every rung of goal 1 still passes.
3. **Features.** More of C lowered: memory, new kernels, and wider op coverage
   in `bdc/`. Dynamatic is not built in this sandbox and the frontend outputs
   in `cloud/fixtures/` cover the existing kernels. Building Dynamatic (LLVM)
   is allowed, but only as a background job, and only when goals 1 and 2 have
   nothing to work on.

## Budget

No usage cap (the owner lifted it on 2026-10-25). Run continuously: never end a
session on your own. When one lead is done or blocked, journal it and start the
next one; the leads under goal 2 and the journal's `Next:` lines are never empty. A new session starts every hour and the lock keeps there from
being two at once, so:
- Refresh `research/LOCK` (commit and push) at least every 45 minutes. A lock
  older than 90 minutes counts as dead.
- Background processes die with the session. Commit before starting anything
  long, so that a killed session loses only the job that was running.

### Use far more parallelism (owner, 2026-10-26)
So far the routine has used about 4% of the owner's weekly limit. The
bottleneck is wall time, not budget. Sessions mostly sit idle, waiting on one
or two hour-long builds. Do not wait on a single lead:
- Check `nproc` and `free -g` at session start. Keep the machine full: as many
  concurrent nextpnr/GLS jobs as cores and RAM allow (one nextpnr per core,
  leave ~2 GB headroom each), each in its own git worktree under the scratchpad.
- Run several leads at once. While a build runs, spawn subagents on independent
  tracks: a routed GLS rig for each kernel besides gcd_hw, rule A/E/J audits on
  other benches, speed analysis (tightening slack, chain lengths, critical
  cycles), literature or web research on bundled-data timing. Subagents never
  touch git in the main tree; they work in their own worktrees and report back,
  and you commit their results.
- A finished background job is a cue to start the next one immediately, not to
  write a long summary and stop.
- The priority order still holds: parallelism is for getting more verified
  results per hour, never for skipping a gate.

## Each session

1. `git fetch origin && git checkout claude/research && git pull --ff-only`.
2. **Lock.** Read `research/LOCK`. If its timestamp is less than 90 minutes old
   and it names a different session, another run is alive: stop immediately and
   change nothing. Otherwise write `<UTC ISO time> <your session id or random
   tag>` to it, then commit and push. Refresh it at every commit. If the push is
   rejected, someone else holds the lock: stop.
3. `cloud/setup-toolchain.sh` (from cold this takes a long time). If it fails,
   fixing it is the session's work. Never weaken `toolchain.sh`.
4. Read the last few entries of `JOURNAL.md` and pick the next step: the
   highest-priority goal with an open, concrete lead.
5. Work in small, verified steps. Commit and push at least every 45 minutes,
   with a `### progress HH:MM` note under this session's entry each time (take
   the time from `date -u +%H:%M` and the session heading's from `date -u`; never
   estimate it, since past entries ran up to 11 hours off the commit times), so that a
   killed session loses little. Exactly one `## Session` heading per session.
6. Keep the branch in a state the next session can pick up at any moment, since
   the session can end without warning: write the journal entry, update `BOARD-QUEUE.md`,
   clear `LOCK` (empty file), and commit and push.

## Journal entry format (append, newest last)

```
## Session <UTC date time> -- <one-line result>
Toolchain: <patch sha from $TC/openxc7/.patches.sha>   Seeds: <list>
Did: ...
Measured: <table: kernel, metric, mean, range, n, vs previous>
Does NOT show: ...
Next: ...
```

A negative or null result is a result: record it, including leads you
disproved.

## Landing work

- Push only to `claude/research`. Keep one draft PR `claude/research -> main`
  open and keep its description current (if `gh` is not available, skip this).
  Never merge.
- Revert anything that breaks a gate. A red branch blocks the next session.
- Never delete or rewrite the owner's or Devin's history.

## Read the independent audit every session (owner, 2026-10-27)

An independent auditor works on branch `claude/audit`. It writes only
`audit/REPORT.md` and `audit/findings/`. At the start of every session, run
`git fetch origin && git show origin/claude/audit:audit/REPORT.md`. Fix every
REFUTED or OVERSTATED row that concerns your files, or answer it in your
journal with evidence. Never edit the audit branch.

**First, the corner misreading (REFUTED by the audit).** The prjxray SDF
triples are `(FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX)`
(`prjxray/utils/makesdf.py:63`). They are **fast and slow corners, not rise and
fall.** So the "O6 rise 45-56 ps, fall 100-124 ps" and the "rise and fall differ
by 2.2x" figures are wrong: 56 and 124 are the fast-corner and slow-corner
bounds of one arc. Nothing in prjxray-db separates rise from fall. Never mix
corners within one analysis (a fast-corner rise with a slow-corner fall);
use one consistent corner, or the corner model with scatter κ.
- Fix `cells/sim/bd_prims_sim.v:57-61` (BD_T_RISE 56 / BD_T_FALL 124, 5LUT
  55/152). Then re-run and re-judge every result that used it:
  tb_arb_overlap, arb_mtbf and the null-generator testbenches. The routed GLS
  (nextpnr SDF, 124 ps on both edges) is not affected.
- The audit also CONFIRMED the GLS sample-at-fire early edge, rule J's missing
  site-pin delays (BQ#1 may be negative under fast-early/slow-late), and the
  rule F in-flight gap. It found that the ring validation rests on ONE ring
  measured on silicon. Treat these as open defects.
