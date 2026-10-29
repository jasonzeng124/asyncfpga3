#!/usr/bin/env bash
# Build one generated design namespace ONE MODULE AT A TIME (never let lake build
# chunks in parallel: an earlier probe was OOM-killed that way). Stops on the first error.
#     formal/tools/fasm2lean3/build.sh Gcd2 [FirstChunk]
# Logs and peak RSS (KB) per module go to build/lb_<NS>_<mod>.log / build/mem_<NS>_<mod>.
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
FORMAL=$(cd "$HERE/../.." && pwd); LEAN=$FORMAL/lean
NS=$1; FROM=${2:-}
export PATH=$HOME/.elan/bin:$PATH
mkdir -p "$HERE/build"
D=$LEAN/Formal/Net/FasmDesign/$NS
MODS="Rho $(ls "$D" | sed -n 's/^\(C[0-9]*\)\.lean$/\1/p' | sort) All"
go=1; [ -n "$FROM" ] && go=0
for m in $MODS; do
    [ "$m" = "$FROM" ] && go=1
    [ $go = 1 ] || continue
    t0=$(date +%s)
    # one Lean process at a time for this probe: other ad-hoc checks take the same lock
    ( cd "$LEAN" && FORMAL_SLOT_CWD=$LEAN flock "$HERE/build/.lean.lock" /usr/bin/time -f %M -o "$HERE/build/mem_${NS}_$m" \
        "$FORMAL/slot.sh" lake build "Formal.Net.FasmDesign.$NS.$m" ) > "$HERE/build/lb_${NS}_$m.log" 2>&1
    rc=$?
    echo "$NS.$m rc=$rc $(( $(date +%s) - t0 ))s $(tail -1 "$HERE/build/mem_${NS}_$m") KB"
    if [ $rc != 0 ] || ! grep -q "Build completed" "$HERE/build/lb_${NS}_$m.log"; then
        grep -E "error" "$HERE/build/lb_${NS}_$m.log" | head -5; echo "STOP at $NS.$m"; exit 1
    fi
done
echo "$NS built"
