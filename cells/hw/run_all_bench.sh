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
# BSTATUS reports runs_done[15:0] -- a larger batch wraps the completion
# count and the completed==n check then fails for a reason that is not the
# hardware. Refuse it here rather than mis-attributing it to the board.
if [ "$N_UNIFORM" -gt 65535 ]; then
    echo "n_uniform=$N_UNIFORM exceeds the 16-bit runs_done field in BSTATUS (max 65535)" >&2
    exit 2
fi
XSDB=${XSDB:-/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab/bin/xsdb}
# Overridable so a subset can be measured while the rest are still building.
# Measuring a STALE bitstream is worse than measuring nothing: it reports a
# number that looks like data but describes a design that no longer exists.
# hw/_rebuild_benches.sh prints which targets are stale.
KERNELS="${KERNELS:-gcd ipow collatz collatz64 isprime xorshift}"

RESULTLOG=build/hw/_run_all_bench.log
: > "$RESULTLOG"

for k in $KERNELS; do
    for variant in real null; do
        if [ "$variant" = "null" ]; then
            TOP="${k}_null_bench_gen"
            # The label selects the tcl's oracle.  Passing the bare kernel name
            # here made it check the NULL kernel -- an xor-fold pass-through --
            # against gcd(12,18)=6, which errored out before any measurement
            # ran.  A non-"gcd" label falls through to the tcl's generic smoke
            # branch, which asserts no oracle.
            LABEL="${k}_null"
        else
            TOP="${k}_bench_gen"
            LABEL="$k"
        fi
        BIT=build/hw/$TOP/$TOP.bit
        LOG=build/hw/_run_${TOP}.log
        if [ ! -e "$BIT" ]; then
            echo "=== SKIP $TOP: no bitstream at $BIT ===" | tee -a "$RESULTLOG"
            continue
        fi
        echo "=== RUN $TOP $(date -Iseconds) ===" | tee -a "$RESULTLOG"
        if hw/board.sh "$XSDB" hw/xsdb_bench_gen.tcl "$BIT" "$LABEL" "$N_UNIFORM" > "$LOG" 2>&1; then
            echo "=== PASS $TOP ===" | tee -a "$RESULTLOG"
        else
            echo "=== FAIL $TOP -- see $LOG ===" | tee -a "$RESULTLOG"
            tail -30 "$LOG" | tee -a "$RESULTLOG"
        fi
    done
done

echo "=== ALL RUNS DONE $(date -Iseconds) ===" | tee -a "$RESULTLOG"
