#!/usr/bin/env bash
# Driver: rebuild all 6 kernels' real + null bench_gen bitstreams on the
# CURRENT toolchain, serially (one nextpnr, no parallel builds).
# Not part of the owned/frozen script set -- lives in cells/hw/, written by
# the agent doing this measurement pass, safe to remove afterward.
set -u
cd "$(dirname "$0")/.."   # -> cells/

LOG=build/hw/_batch_build_all.log
: > "$LOG"

KERNELS="gcd ipow collatz collatz64 isprime xorshift"

for k in $KERNELS; do
    for variant in real null; do
        if [ "$variant" = "null" ]; then
            TOP="${k}_null_bench_gen"
            ARGS="$k --null"
        else
            TOP="${k}_bench_gen"
            ARGS="$k"
        fi
        echo "=== START $TOP $(date -Iseconds) ===" | tee -a "$LOG"
        t0=$(date +%s)
        if bash hw/build_bench.sh $ARGS > "build/hw/_last_${TOP}.log" 2>&1; then
            t1=$(date +%s)
            echo "=== PASS $TOP  $((t1-t0))s ===" | tee -a "$LOG"
        else
            t1=$(date +%s)
            echo "=== FAIL $TOP  $((t1-t0))s -- see build/hw/_last_${TOP}.log ===" | tee -a "$LOG"
            tail -40 "build/hw/_last_${TOP}.log" | tee -a "$LOG"
        fi
    done
done

echo "=== BATCH DONE $(date -Iseconds) ===" | tee -a "$LOG"
