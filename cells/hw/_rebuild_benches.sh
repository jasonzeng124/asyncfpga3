#!/usr/bin/env bash
# Rebuild every generated bench whose Verilog is older than hw/gen_bench.py.
#
#   hw/_rebuild_benches.sh [--dry-run]
#
# gen_bench.py emits the bench for ALL six kernels, real and null, so a change
# there (the FSM synchroniser, say) leaves eleven of twelve bitstreams silently
# carrying the old bug while only the one you happened to rebuild is fixed.
# Staleness is decided by mtime against gen_bench.py itself rather than by a
# hand-kept list, so this cannot drift out of date the way a list would.
#
# SKIP_TOPS exists because a bitstream that is currently loaded on the board is
# not safe to overwrite -- a rebuild reroutes, and any board run in flight would
# silently change design underneath itself.  Name such a target here.
set -u
cd "$(dirname "$0")/.."

DRY=0
[ "${1:-}" = "--dry-run" ] && DRY=1

SKIP_TOPS="${SKIP_TOPS:-}"
GEN=hw/gen_bench.py
LOG=build/hw/_rebuild_benches.log
mkdir -p build/hw
[ $DRY -eq 1 ] || : > "$LOG"

gt=$(stat -c %Y "$GEN")
todo=()
for k in gcd ipow collatz collatz64 isprime xorshift; do
    for suffix in "" "--null"; do
        if [ -z "$suffix" ]; then TOP="${k}_bench_gen"; else TOP="${k}_null_bench_gen"; fi
        case " $SKIP_TOPS " in *" $TOP "*)
            echo "SKIP    $TOP (named in SKIP_TOPS)"; continue ;;
        esac
        v="build/gen/$TOP.v"
        if [ -f "$v" ] && [ "$(stat -c %Y "$v")" -ge "$gt" ]; then
            echo "current $TOP"
        else
            echo "STALE   $TOP"
            todo+=("$k|$suffix|$TOP")
        fi
    done
done

echo "${#todo[@]} target(s) to rebuild"
[ $DRY -eq 1 ] && exit 0
[ ${#todo[@]} -eq 0 ] && { echo "nothing to do"; exit 0; }

fails=0
for item in "${todo[@]}"; do
    IFS='|' read -r k suffix TOP <<< "$item"
    echo "=== START $TOP $(date -Iseconds) ===" | tee -a "$LOG"
    t0=$(date +%s)
    if bash hw/build_bench.sh "$k" $suffix > "build/hw/_last_${TOP}.log" 2>&1; then
        echo "=== PASS $TOP $(( $(date +%s) - t0 ))s ===" | tee -a "$LOG"
    else
        fails=$((fails+1))
        echo "=== FAIL $TOP $(( $(date +%s) - t0 ))s ===" | tee -a "$LOG"
        tail -40 "build/hw/_last_${TOP}.log" | tee -a "$LOG"
    fi
done
echo "=== DONE $(date -Iseconds): ${#todo[@]} attempted, $fails failed ===" | tee -a "$LOG"
[ $fails -eq 0 ] || exit 1
