# The farm

A machine with thousands of cores runs jobs for this branch, up to 200 cores at a time. You cannot log in to it. You ask
by committing a request here. A runner there sees the request within a few minutes, runs it as
an array of independent tasks, and pushes what the tasks left behind to the branch
`claude/cluster`. Research uses the same farm from its own branch.

Use it for what the cloud sandbox is short of: memory (up to 64G a task), cores (16 a task) and
width (256 tasks at once). A full `lake build`, `check.sh`, a sweep over kappa points or operand
pairs, the margin tool over 32 routes. Keep quick things local, where there is no round trip.

## A request

`formal/cluster/requests/NAME.sh`, with NAME from `a-z 0-9 _ -` (lower case only), up to 40
characters. A file whose name does not fit never runs; it is listed, with the reason, in
`results/IGNORED.txt` on `claude/cluster`. The three
shards share this directory and a name runs once, ever: start yours with your shard's letter
(`a_`, `b_`, `c_`).

```
#!/bin/bash
#CLUSTER array=1-8 cores=8 mem=32G time=120
set -uo pipefail
key=$(cat formal/lean/lean-toolchain formal/lean/lake-manifest.json | md5sum | cut -c1-12)
tar -C formal/lean -xf "$SHARED/lake/$key.tar"        # Lean's build directory: see "Lean" below
formal/slot.sh lake build Formal.Some.Module > "$OUT/build.txt" 2>&1
exit $?
```

The `#CLUSTER` line must be in the first five lines. `array` is the list of task numbers (`1-24`,
or `1,3,5-7`), `time` is minutes per task. The defaults are 4 cores, 16G and 90 minutes. Set
`time` to about three times what a task needs: a task that hangs holds its request until then.

The script runs once per task. Each task has a checkout of its own, of this branch at the commit
that was its head when the runner picked the request up, and runs from its root. So push what a
request needs before the request, or in the same push. A task sees:

| Variable | Meaning |
| --- | --- |
| `TASK` | this task's number |
| `JOBS` | the cores it may use; `LEAN_NUM_THREADS` is set to the same |
| `FORMAL_SLOTS` | what `formal/slot.sh` should use here: it would otherwise size itself from the whole machine's memory, not the task's |
| `OUT` | a directory of its own; the text files left here come back |
| `RUNS` | working space of its own on the machine's disk; deleted when the task ends |
| `SHARED` | space that stays, shared by every task and request of both bots; nothing here comes back |
| `PEER` | a checkout of `claude/research` as it was when the request was picked up. It is only made if your script contains the word `PEER` |
| `TC`, `XRAY_DB` | research's FPGA toolchain and the prjxray database, as in the cloud but not under `/root` |

The checkout and `/tmp` are the task's own and are deleted with it, so tasks cannot disturb each
other. A task can be stopped and started again from the top at any moment: it must be safe to
rerun. The machine has the same toolchain image as the cloud, so research's build commands give
the same routes there (`$PEER/research/cluster/README.md`).

## Lean

- Lean lives under `$HOME/.elan`, installed by the first task that ran `formal/setup.sh`, and is
  on `PATH`. `$HOME` is shared by all tasks and stays.
- Every task's checkout is at the same path, `/tmp/task/repo`. So a `.lake` directory built in
  one task is valid in any other, and it is kept as one file: `$SHARED/lake/KEY.tar`, where KEY
  is the first 12 characters of the md5 of `lean-toolchain` followed by `lake-manifest.json`.
  Unpack it as in the example and `lake build` only builds what changed since it was saved.
- `requests/lean_prime.sh` makes that file: it runs `formal/setup.sh` (Mathlib, then this
  project, for at most 200 minutes) and saves `.lake`, starting from the saved one if there is
  one. Run a copy of it under a new name after the toolchain or the manifest changes, or to
  bring the saved oleans up to date. Its results (`results/fm_lean_prime/1/env.txt`) say how
  long the build took and how big it is.
- Write the tar under a temporary name and `mv` it into place, as `lean_prime.sh` does. Two
  tasks writing it at once would leave a broken file.

## Results

```
git fetch origin claude/cluster
git show origin/claude/cluster:results/fm_NAME/status.txt
git show origin/claude/cluster:results/fm_NAME/3/build.txt
```

Your request NAME is `fm_NAME` there, so that it cannot collide with one of research's.

| Path | Holds |
| --- | --- |
| `results/fm_NAME/status.txt` | `waiting: reason`, `submitted`, `running (k of n tasks finished)`, `done` or `rejected: reason`; one line per task with its state, run time and exit code |
| `results/fm_NAME/TASK/...` | the files the task left in `$OUT` |
| `results/fm_NAME/TASK/log.txt` | the last 150 lines of the task's output |
| `results/fm_NAME/TASK/SKIPPED.txt` | files that were left out, if any |

Results come back as tasks finish: ten minutes after the first one, then every ten minutes.
Only text comes back: up to 1 MB per file and 4 MB per task, in at most three levels of
directories, with names from letters, digits, `.`, `_` and `-`. Paths and machine names in it
are replaced by placeholders. A proof term or a large trace goes to `$SHARED`, and the next
request reads it there.

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

One request: 240 tasks, 16 cores and 64G per task, 240 minutes per task. All requests of both
bots together: 250 tasks queued or running, which is what the machine allows one account. A
request over that waits, and its `status.txt` says `waiting` until there is room. Research
often fills the farm, so keep requests narrow when you want them soon. A request over a
per-request limit is rejected, and `status.txt` says why.

## Do not wait on it

The farm is a help, not a dependency. `status.txt` says `submitted` or `waiting` within about five minutes of
your push. If it has not appeared after 30 minutes, the runner is down: note it in the journal,
do the work locally, and try again in a later session. Do other work in the meantime and look
again later; never sit in a loop waiting for it.
