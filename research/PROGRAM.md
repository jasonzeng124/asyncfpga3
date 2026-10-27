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

## The audits are heuristics; an accurate GLS is the ground truth (owner, 2026-10-27)

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

Once it is validated, a design is verified when routed GLS on the new model
passes at the slow and fast corners, with the measured residual injected as
scatter, on at least 8 seeds. A rule violation on a route whose accurate GLS
passes is no longer a blocker. Record it as a disagreement and work out which
one is wrong; a negative control that GLS must catch is the way to decide. A
GLS failure blocks, whatever the rules say. Until the model is validated, keep
the current gates exactly as they are.

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
