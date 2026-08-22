#!/usr/bin/env bash
# Drive xsdb_bench_gen.tcl for every kernel's real + null bench_gen
# bitstream, serially, each under the board lock. Captures one log per
# target under build/hw/_run_<top>.log. Not a frozen/owned script --
# written for this measurement pass.
#
#   hw/run_all_bench.sh [n_uniform]
set -u
cd "$(dirname "$0")/.."   # -> cells/

N_UNIFORM=${1:-3000}
XSDB=${XSDB:-/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab/bin/xsdb}
KERNELS="gcd ipow collatz collatz64 isprime xorshift"

RESULTLOG=build/hw/_run_all_bench.log
: > "$RESULTLOG"

for k in $KERNELS; do
    for variant in real null; do
        if [ "$variant" = "null" ]; then
            TOP="${k}_null_bench_gen"
        else
            TOP="${k}_bench_gen"
        fi
        BIT=build/hw/$TOP/$TOP.bit
        LOG=build/hw/_run_${TOP}.log
        if [ ! -e "$BIT" ]; then
            echo "=== SKIP $TOP: no bitstream at $BIT ===" | tee -a "$RESULTLOG"
            continue
        fi
        echo "=== RUN $TOP $(date -Iseconds) ===" | tee -a "$RESULTLOG"
        if hw/board.sh "$XSDB" hw/xsdb_bench_gen.tcl "$BIT" "$k" "$N_UNIFORM" > "$LOG" 2>&1; then
            echo "=== PASS $TOP ===" | tee -a "$RESULTLOG"
        else
            echo "=== FAIL $TOP -- see $LOG ===" | tee -a "$RESULTLOG"
            tail -30 "$LOG" | tee -a "$RESULTLOG"
        fi
    done
done

echo "=== ALL RUNS DONE $(date -Iseconds) ===" | tee -a "$RESULTLOG"
