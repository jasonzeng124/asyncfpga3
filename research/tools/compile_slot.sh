#!/usr/bin/env bash
# compile_slot.sh CMD... -- run CMD while holding one of COMPILE_SLOTS machine-wide compile slots.
# Slot 0 is /tmp/eventgraph_compile.lock, the one lock every tool used before ("one compile at a time on the machine":
# build_ps.sh's iverilog peaks at several GB, gcd's at 9.4 GB, and OOM kills lose runs).  With COMPILE_SLOTS unset or 1
# (and no /tmp/eventgraph_compile.slots file) this is exactly `flock /tmp/eventgraph_compile.lock CMD...`, as before
# (the farm, the cloud sandbox).  The cluster node (16 cores, 64 GB) writes 4 into /tmp/eventgraph_compile.slots: four
# compiles at once, at most ~40 GB at gcd's peak; the file is read at every call, so running jobs follow a change.
n=${COMPILE_SLOTS:-$(cat /tmp/eventgraph_compile.slots 2>/dev/null || echo 1)}
if [ "$n" -le 1 ]; then exec flock /tmp/eventgraph_compile.lock "$@"; fi
while :; do
  for i in $(seq 0 $((n - 1))); do
    f=/tmp/eventgraph_compile.lock; [ "$i" -gt 0 ] && f=/tmp/eventgraph_compile.lock.$i
    exec {fd}>>"$f"
    if flock -n "$fd"; then "$@"; rc=$?; exec {fd}>&-; exit $rc; fi
    exec {fd}>&-
  done
  sleep 3
done
