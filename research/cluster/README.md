# The farm

A machine with thousands of cores runs jobs for this branch, up to 200 cores at a time. You cannot log in to it. You ask by
committing a request here. A runner there sees the request within a few minutes, runs it as an
array of independent tasks, and pushes what the tasks left behind to the branch `claude/cluster`.

It runs the same toolchain image as the cloud, so a given `NEXTPNR_SEED` gives the same route
there and here (checked on 2026-11-14 on `xfr` seed 1: routed SDF `90890b3b`, period 22523 ps, both as in `graphs/xfr_1`). The farm does not send back bitstreams or SDF
files. When a seed is interesting, rebuild it here; you get the same route.

Use it for anything wide: a gate over 24 routes, an 8-route or 64-route mean, a sizing round
checked on many routes, a lever screened on 32 seeds instead of 2. Keep the small, quick
experiments local, where there is no round trip.

## A request

`research/cluster/requests/NAME.sh`, with NAME from `a-z 0-9 _ -` (lower case only), up to 40
characters. A file whose name does not fit never runs; it is listed, with the reason, in
`results/IGNORED.txt` on `claude/cluster`.

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

Set `time` to about three times what a task needs, not to the maximum. A task that hangs is
only stopped at its limit, and the request is not `done` until then: on 2026-11-15 four requests
with `time=240` each waited four hours for one or two hung tasks.

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
| `PEER` | a checkout of `claude/formal` as it was when the request was picked up, so a task can run formal's tools on your routes. It is only made if your script contains the word `PEER` |

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
| `results/NAME/status.txt` | `waiting: reason`, `submitted`, `running (k of n tasks finished)`, `done` or `rejected: reason`; once tasks have run, one line per task with its state, run time and exit code |
| `results/NAME/TASK/...` | the files the task left in `$OUT` |
| `results/NAME/TASK/log.txt` | the last 150 lines of the task's output |
| `results/NAME/TASK/SKIPPED.txt` | files that were left out, if any |

Results come back as tasks finish, not only at the end. Ten minutes after the first task of a
request finishes, the finished tasks' files are pushed and `status.txt` says `running (k of n
tasks finished)`; then again every ten minutes while more finish. Use what is there: with 30 of
32 routes back there is no reason to wait for the last two. `done` means every task has ended.

A task that lands on a machine that cannot reach the farm's storage is run again elsewhere, at
once and without your doing anything; it shows up later than the others.

Only text comes back: up to 1 MB per file and 4 MB per task, in at most three levels of
directories, with names from letters, digits, `.`, `_` and `-`. Paths and machine names in it are
replaced by placeholders.

## Limits

**The farm holds at most 200 cores at a time (owner, 2026-11-17).** It ran at about 900, most
of the account's whole allowance, and the owner asked for a ceiling. What that means for a
request:

- its tasks run `floor(200 / cores)` at a time: 25 tasks of 8 cores, 50 of 4, 12 of 16. A
  64-task request of 8 cores takes three rounds, not one;
- it is submitted only when the requests before it leave that many cores free, and until then
  its `status.txt` says `waiting`. Requests filed before the ceiling existed run out first,
  with no throttle, so on 2026-11-17 new requests wait for several hours;
- the two bots take turns, a minute each, at being looked at first.

So ask for the cores a task really uses (a task that runs one route and one simulation at a
time needs 1 or 2, not 8), file fewer and smaller requests, and put the one you need first,
first. Two hundred cores is still about fifty times a cloud sandbox.

One request: 240 tasks, 16 cores and 64G per task, 240 minutes per task. All requests, yours and
formal's (it has the farm too since 2026-11-15), together: 250 tasks queued or running, which is
what the machine allows one account. A request over that waits, in the order of its file name,
and its `status.txt` says `waiting` until there is room. Twenty 32-task requests filed at once
therefore run about eight at a time: file what you need first, first. A request over a per-request limit is
rejected, and `status.txt` says why.

## Do not wait on it

The farm is a help, not a dependency. `status.txt` says `submitted` or `waiting` within about five minutes of
your push. If it has not appeared after 30 minutes, the runner is down: note it in the journal,
do the work locally, and try again in a later session. A request that was submitted normally
finishes within its time limit plus a few minutes of queueing. Do other work in the meantime and
look again later; never sit in a loop waiting for it.
