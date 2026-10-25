# Autonomous research program

You are the only agent working on branch `claude/research`. Nobody will answer
questions: decide, record why in the journal, and keep going. The owner reads
`research/JOURNAL.md` and `research/BOARD-QUEUE.md` and runs the board.

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
   with a `### progress` note under this session's entry each time, so that a
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
