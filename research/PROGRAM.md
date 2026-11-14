# Autonomous research program

You are the only agent working on branch `claude/research`. Nobody will answer
questions: decide, record why in the journal, and keep going. The owner reads
`research/JOURNAL.md` and `research/BOARD-QUEUE.md` and runs the board.

## FIRST: xorshift at 15 ns per iteration, in four-phase (owner, 2026-11-12)

The owner read `research/data/eventgraph/README.md` and decided two things:

- **The protocol stays four-phase for now.** Do not start a two-phase rewrite.
- **About 15 ns per iteration on xorshift is doable in four-phase, and the owner wants a
  harder push for it.** Do not stop at the knobs bdc already has.

Where it stands (bench top, simulation). The best gated xorshift is board item 14, about
30 ns (28.5 to 32.4 by seed). Dynamatic is 12.73. Two gaps separate 30 from 15:

1. **30 to 20: return-to-zero is still on the critical cycle.** The worst cycle with no
   polarity change is 19.2 to 20.7 ns. The step-4 search had three edits only (link depth,
   merge-output link, fast fall). What binds after them is the falling pass of handshake
   cells (9.08 ns of the x0.5 period), with the polarity changes at the merge and at the
   merge-output link's fork.
2. **20 to 15: the rising pass itself.** On x0.5 seed 1 it is excess delay 11.79, req/ack
   wires 7.85, handshake cells 1.23, logic 1.03. At least 5 ns has to come out of excess
   delay and wires.

**Every kernel is judged over its full input range (owner, 2026-11-14).** The owner read
the hold on item 18 and the finding on the x0.5 xorshift family, and decided: xorshift must
be correct for any 32-bit `rounds`, not only the bench's 12-bit range. The same holds for
every kernel and every input its C signature allows. From now on:

- **A gate pass is not enough where the vectors cannot reach a path.** For every path whose
  data range the gate's vectors do not span (loop counters and what compares them first),
  rules A and E must hold statically, at nominal and at the worst corner with the usual
  guards, for the longest carry the input type allows. Run this check before reading the
  gate, on every candidate.
- **Re-baseline the x0.5 xorshift family** (board items 4, 11, 14, 17, and 18 on hold). Give
  the counter's add and compare the sizes the static check asks for, measure again, gate
  again. In `BOARD-QUEUE.md`, mark every item that holds only on the bench's range as
  that, and say which items pass over the full range.
- **The headline of `research/data/fifteen/README.md` is the best xorshift build that passes
  both the gate and the static check over the full range.** Expect it to get slower first.
  Report both numbers once, so the cost of the full range is on record.
- **Check the other kernels the same way** (ipow's and gcd's counters and compares too), and
  the board items already listed for them.
- **A large static miss on a spanned path still needs an explanation** (2026-11-14, on the
  flag in the journal). ipow item 19's `umux3` misses rule A by 1.7 ns at nominal, and the
  select race traced on 2026-11-10 was on the same mux. Before the item stays on the list,
  either name the false path that makes the rule pessimistic there and show it with a trace,
  or restore the size and gate again. Do the same for any miss over 0.5 ns at nominal on a
  board item, whether or not the vectors span the path.
- **Then win the time back with a delay that depends on the data.** For `i + 1` the carry is
  as long as the run of trailing ones in `i`, so almost every iteration needs only a short
  delay and a rare one needs the long one. Choosing the delay from the operands is the known
  technique (speculative completion, Nowick and others); read it before designing. A delay
  that merely copies the carry chain tracks process and voltage but still pays the full
  length every time. This is a cell-level change under CLAUDE.md's rule, and it needs the
  static check above to cover both the short and the long case.

- **The `!=` loop test: yes, and LLVM already does it** (answer to the journal's question,
  2026-11-14). The owner's point: the kernel goes through LLVM first. It does, and
  `bdc/frontend.sh` step 4 runs `indvars`, whose exit-test rewrite turns `i + 1 < rounds`
  into `i + 1 != rounds` with LLVM's own proof. It does not fire because step 3 strips
  `target datalayout` (copied from Dynamatic's `compile.sh`): without it no integer width
  is legal, and `indvars` finds no loop counter to rewrite. Checked on xorshift's
  `clang.opt.ll` with LLVM 18: `-passes='function(loop(indvars))'` leaves `icmp slt`; the
  same command with a data layout line gives `%exitcond = icmp ne i32 %10, %1`. With the
  data layout through the whole step-4 pass list, the result is `icmp ne` against
  `smax(rounds, 0)` computed once before the loop.
  So this is a frontend fix, not a bdc rewrite and not a change to the loop lowering:
  - add it as an opt-in knob in `bdc/frontend.sh`, default off and byte-identical;
  - prefer the narrow form: one extra `indvars` after `loop-rotate`, with a data layout
    whose only native width is 32 bits, so that nothing is widened to 64 bits;
  - a data layout can change other passes' output, so diff the handshake MLIR of every
    kernel with the knob on and say what else moved;
  - then the usual: simcheck with `rounds` at 0, 1 and INT_MAX, the static check over the
    full range, the gate.

The 15 ns target stands, under this rule.

What to do, in this order:

1. **The budget, from the graph, before any build.** For item 14's routes:
   - every falling arc on a critical or near-critical cycle, by cell, and the edit that would
     take it off the cycle;
   - every delay on the rising ring: what it is, what its data needed in the worst iteration
     and corner, and what the rules (A, E, the select rule) require. That makes the removable
     part of the 11.8 ns a number;
   - every req/ack wire on the ring: its routed delay against the shortest it could be with
     the two cells adjacent. That makes the removable part of the 7.85 ns a number.
   Then the predicted period with all three taken. If it is not under 15, say what it is and
   what blocks it, and carry on with the levers anyway.
2. **New levers, the largest first.** Anything four-phase is allowed. That includes changing
   or adding cells under CLAUDE.md's rule (a stated reason and a routed-GLS check); new
   variants are opt-in and off by default. Ideas, not a list to follow:
   - return-to-zero off the cycle: storage at sites the search could not use (mux, steer and
     fork outputs, acknowledge paths); handshake cells whose falling arc is short where the
     protocol allows it (read the notes on `bd_join`'s acknowledge before trying); letting
     the counter ring's handshake stop waiting on the datapath;
   - a shorter rising pass: fewer handshake stages on the counter ring (13 today), by fusing
     its mux, add, compare and steer; per-instance sizing of the ring's delays under the
     select rule; a delay built from the same primitive as the data it bundles, so it tracks
     the data instead of covering it with margin;
   - shorter wires: place the ring's cells together (`RLOC_GROUP`, `PLACE_WEIGHT`).
3. **Predict, build, measure, gate, as in the event-graph work.** Write every prediction
   before the build. The graph under-charges an inserted stage by 1 to 3 ns of wire, so add
   that. The correctness bar does not move: the full gate, the select rule, `ffmux_scan.py`.
4. **Keep going.** A lever that fails is a journal entry, not a stopping point: take the
   next one. Stop only when the budget shows no lever left, and then say what 15 ns would
   need.
5. **Then the other kernels.** Apply what worked to collatz, ipow and collatz64, and report
   each beside Dynamatic's number (collatz 14.05, collatz64 17.84). They have no target yet.

The loop lowering stays as it is (owner). If the budget shows that 15 ns cannot be reached
without changing it, say so with the number.

Report in `research/data/fifteen/README.md`: one table, a row per lever in the order
applied, with predicted and measured period on four seeds and the gate status. Its first
line is the best gated xorshift period and the gap to 15.

## Done (kept for the record; do not redo)

- **Where one iteration's time goes** (owner, 2026-11-06): `research/data/itercost/README.md`.
  xorshift x0.5 is 39.06 ns: logic 1.03, excess delay 11.79, handshake 1.23, routing 7.85,
  RTZ 17.15. The critical cycle is the loop-control ring, not the datapath.
- **A second latch where the cycle waits on a handshake** (owner, 2026-11-09):
  `research/data/itercost/second_latch/README.md`. xorshift p8mo is 1.25-1.27x per round and
  passed the full gate (board item 11). collatz gained 1.8 ns only.
- **Storage chosen from the event graph** (owner, 2026-11-10): `research/data/eventgraph/README.md`.
  The graph reproduces all 26 itercost runs exactly and predicts new builds to about 1.4 ns.
  Storage plus fast fall: xorshift 1.34x, ipow 1.18x, collatz 1.13x (board items 13 to 15).
  Two-phase bound 1.78x on xorshift, 1.40 to 1.46x on collatz and ipow; the decoupled
  controller buys nothing. The owner chose to stay four-phase (2026-11-12).

## Effort and subagents (owner, 2026-11-05)

The owner raised the budget to about twice the single-thread, high-effort level.
Sessions run at max effort (`.claude/settings.json`). **You may use subagents,
but at most 4 at a time** (raised from 2, owner, 2026-11-07). Wait for one to finish before starting another. A
subagent never touches git: it works in its own worktree or scratch directory
and reports back, and you review and commit what it found. Use them for
independent work that would otherwise wait (a second sweep while a build runs, a
proof while a check builds, a claim to reproduce), never to run the same work
twice. Never create scheduled routines or reminders.

The limit on progress is now memory and disk, not usage: the session has logged OOM kills
and disk-full restarts. Before starting a job, check `free -g` and `df -h`, and do not
run more than fits. A killed job is a lost result.

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

## Next, now that ring128 matches (owner, 2026-11-04)

Every runnable hard acceptance item matches, ring128 included at band 0.288 with a
0.76% residual. The gap left is the cell types the rings do not exercise, and only
the board can close it. The owner's rule for gaps like this: **pick a reasonable
parametric model, say what it is, run with it, and measure more later.** Do not
wait on data the project cannot get.

1. **The sim is the gate** (see "Once it passes acceptance"). For the cell types
   ring128 does not calibrate (CARRY4, MUXF7/F8, the slice output muxes), the
   default is the same band as LUT + wire, 0.288: same die, same process. Keep it a
   parameter (`GLS_SDF_BAND_CELL`), and also gate every design at the corner
   where those cells are at SLOW_MAX while everything else is at 0.288 (you
   already ran that check). Flops: none in the kernels, and the harness's flops
   are clocked logic covered by nextpnr STA plus the synchronizer rule, so they
   need no calibration.
2. **Fit the datapath band on the August gcd build.** The owner committed the
   August board builds and logs: `research/board/aug/` (README.md pairs each log with
   the `.bit` it programmed). `gcd_bench_gen` is the build behind the gcd cost model's
   board column (54-72% of the band on the datapath, against 0.288 from the rings).
   Run that exact build in the full stack, fit the per-iteration costs against
   `logs/gcd_cost.tsv` and `_gcdcost_*.log`, and do the same for the other matched
   kernels (collatz, collatz64, ipow, isprime, and their null builds for the
   harness overhead). If one band fits rings and kernels, the cell default
   stands. If the datapath sits slower, set the cell band from the fit, say so,
   and keep it a parameter.
3. **Speed: shrink the matched delays to what the sim proves.** The sizing guards
   were set for ~8.5% scatter, and the board shows 0.76%. A matched delay and the
   path it tracks are on the same die, so the shared corner cancels and only the
   residual and the cell-type mismatch need a guard. Shrink in small steps and run
   the full stack after each one (both corners, the measured residual as scatter,
   >= 8 seeds, derived oracles). A step that fails is reverted. Never go below
   what the sim proves at the slow-cell corner of item 1. Report the per-kernel
   speedup against BOARD-QUEUE #1/#2.
4. **Run every other kernel through the full stack** (ipow, xorshift, collatz,
   collatz64, isprime). So far only the rules have judged them.
5. **One ordered board list** at the top of BOARD-QUEUE.md for when the board is
   back, best first: gcd_ps with the 1000 vectors; the short-pulse C-element test
   (H_RUNT); the fastest design the sim accepts; a ring set on a second route, which
   would test the band transfer. Each item judges itself.

## First lead: a full-width gcd target for formal (owner, 2026-11-01)

Formal is proving that a gcd_hw bitstream is correct (claude/formal,
`formal/PROGRAM.md`, "THE goal"). Its current target, the BOARD-QUEUE #1
build, takes inputs from a 16-entry vector table, so "every a, b" cannot be
stated for it (`formal/FOR-RESEARCH.md` section 1). Build the same kernel
inside `cells/hw/gcd_ps.v` (32-bit operand registers from the PS, no vector
table), with the same flags and sizing flow as BOARD-QUEUE #1, put it through
the full stack (every audit, the fid GLS at both corners on >=4 seeds, with
operands from outside the 16 vectors and a derived oracle), and add it to
BOARD-QUEUE.md as a new item. Name one seed's `.bit` and `.fasm`, with md5s,
as "formal target" in that item. Check how the STATUS bits (i_ack, o_req)
cross from the async kernel into the PS clock domain; if there is no
synchronizer, that is a finding to fix first (see the async-latch lesson in
the journal). Do this before other leads. Also read FOR-RESEARCH sections 2
and 3: the kernel reorders pipelined pairs (the board harnesses must stay
sequential; check gcd_ps's FSM does), and the ua1 runt test is a cheap fid
GLS experiment.

## THE priority: a board-fidelity gate-level simulation (owner, 2026-10-27)

The owner considers this the most important thing for developing without a
board. It comes before every speed lead. Give it the main thread until it is done. Other work only fills idle cores.

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

One session starts per day (owner, 2026-10-29). Run continuously: never end a
session on your own. When one lead is done or blocked, journal it and start the
next one; the leads under goal 2 and the journal's `Next:` lines are never empty. The lock keeps there from being two sessions at once, so:
- Refresh `research/LOCK` (commit and push) at least every 45 minutes. A lock
  older than 90 minutes counts as dead.
- Background processes die with the session. Commit before starting anything
  long, so that a killed session loses only the job that was running.

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
