# The farm

A machine with thousands of cores runs jobs for this branch. You cannot log in to it. You ask by
committing a request here. A runner there sees the request within a few minutes, runs it as an
array of independent tasks, and pushes what the tasks left behind to the branch `claude/cluster`.

It runs the same toolchain image as the cloud, so a given `NEXTPNR_SEED` gives the same route
there and here (checked on 2026-11-14 on `xfr` seed 1: routed SDF `90890b3b`, period 22523 ps, both as in `graphs/xfr_1`). The farm does not send back bitstreams or SDF
files. When a seed is interesting, rebuild it here; you get the same route.

Use it for anything wide: a gate over 24 routes, an 8-route or 64-route mean, a sizing round
checked on many routes, a lever screened on 32 seeds instead of 2. Keep the small, quick
experiments local, where there is no round trip.

## A request

`research/cluster/requests/NAME.sh`, with NAME from `a-z 0-9 _ -`, up to 40 characters.

```
#!/bin/bash
#CLUSTER array=1-24 cores=4 mem=16G time=90
set -uo pipefail
N=myname_$TASK
research/tools/fifteen/lane.sh "myL$TASK" "$N" xorshift research/data/xorshift_sizes_T3s50_fr_bench.vh \
    "$TASK" research/data/fifteen/vec_xorshift.hex BDC_LINK_FASTFALL=1 > "$OUT/summary.txt" 2>&1
rc=$?
G=research/data/eventgraph/graphs/$N
cp "$G"/check.txt "$G"/benchres.txt "$G"/build.txt "$G"/provenance.txt "$OUT/" 2>/dev/null
exit $rc
```

The `#CLUSTER` line must be in the first five lines. `array` is the list of task numbers (`1-24`,
or `1,3,5-7`), `time` is minutes per task. The defaults are 4 cores, 16G and 90 minutes.

The script runs once per task. Each task has a checkout of its own, of this branch at the commit
that was its head when the runner picked the request up, and runs from its root. So push the
tools and data a request needs before the request, or in the same push. A task sees:

| Variable | Meaning |
| --- | --- |
| `TASK` | this task's number; use it as the seed |
| `JOBS` | the cores it may use |
| `OUT` | a directory of its own; the text files left here come back |
| `RUNS` | working space of its own, in place of `/home/user/runs`; it is deleted when the task ends |
| `SHARED` | space that stays, shared by every task and request; nothing here comes back |
| `TC`, `XRAY_DB` | the toolchain and the prjxray database; they are not under `/root` there |

`build/frontend` is already filled from `cloud/fixtures/frontend`. The checkout and `/tmp` are
the task's own and are deleted with it, so tasks cannot disturb each other. A task can be stopped
and started again from the top at any moment; it must be safe to rerun. It cannot reach a
route another task built unless that task copied it to `$SHARED`; a route is cheap to rebuild
from its seed, so keep `$SHARED` small.

A name runs once. To run something again, use a new name.

## Results

```
git fetch origin claude/cluster
git show origin/claude/cluster:results/NAME/status.txt
git show origin/claude/cluster:results/NAME/7/summary.txt
```

| Path | Holds |
| --- | --- |
| `results/NAME/status.txt` | `submitted`, `done` or `rejected: reason`; when done, one line per task with its state, run time and exit code |
| `results/NAME/TASK/...` | the files the task left in `$OUT` |
| `results/NAME/TASK/log.txt` | the last 150 lines of the task's output |
| `results/NAME/TASK/SKIPPED.txt` | files that were left out, if any |

Only text comes back: up to 1 MB per file and 4 MB per task, in at most three levels of
directories, with names from letters, digits, `.`, `_` and `-`. Paths and machine names in it are
replaced by placeholders.

## Limits

One request: 256 tasks, 8 cores and 32G per task, 240 minutes per task. All requests together:
512 tasks queued or running; a request over that waits. A request over a per-request limit is
rejected, and `status.txt` says why.

## Do not wait on it

The farm is a help, not a dependency. `status.txt` says `submitted` within about five minutes of
your push. If it has not appeared after 30 minutes, the runner is down: note it in the journal,
do the work locally, and try again in a later session. A request that was submitted normally
finishes within its time limit plus a few minutes of queueing. Do other work in the meantime and
look again later; never sit in a loop waiting for it.
