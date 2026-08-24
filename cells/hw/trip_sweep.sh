#!/usr/bin/env bash
# Per-iteration cost of a bundled-data loop, measured on silicon.
#
#   hw/trip_sweep.sh [seed]
#
# xorshift(seed, rounds) is the only kernel in the suite whose TRIP COUNT is a
# runtime operand, so its loop cost can be measured by sweeping an input rather
# than by rebuilding anything.  Each point is a FIXED-mode N=200 batch driven
# through hw/xsdb_bench_gen.tcl at (seed, rounds), and each point asserts its
# OWN result oracle: the expected value is computed here from the C in
# kernels/xorshift/xorshift.c and folded the way the RTL folds it, so a point
# that lands on the wrong answer is an error rather than a data row.  Without
# that, a loop that exits early reads as a fast loop -- which is exactly how an
# under-delayed xorshift build once passed every check in the bench.
#
# Raw data from both sweeps is committed as hw/trip_sweep_results.tsv.
#
# What the numbers separate: latency(rounds) = fixed_overhead + rounds * cost.
# The slope is what one iteration of a bundled-data while-loop costs on this
# fabric, and the intercept is what the handshake wrapper costs around it.
set -u
cd "$(dirname "$0")/.."

SEED=${1:-2463534242}
XSDB=${XSDB:-/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab/bin/xsdb}
BIT=build/hw/xorshift_bench_gen/xorshift_bench_gen.bit
OUT=build/hw/trip_sweep_${SEED}.tsv
[ -e "$BIT" ] || { echo "no bitstream at $BIT"; exit 2; }

printf 'rounds\tlatmin\tlatmax\tresult\tsig\n' > "$OUT"
echo "trip sweep: seed=$SEED, FIXED N=200 per point, oracle asserted at every point"

for R in 0 1 2 4 8 16 32 64 128 256; do
    read -r WANT SIG <<<"$(python3 - "$SEED" "$R" <<'PY'
import sys
seed, rounds = int(sys.argv[1]), int(sys.argv[2])
M = 0xffffffff
x = seed & M
for _ in range(max(rounds, 0)):
    x = (x ^ (x << 13)) & M
    x ^= x >> 17
    x = (x ^ (x << 5)) & M
sig = 0
for _ in range(200):
    sig = (((sig << 1) & M) | (sig >> 31)) ^ x
print(x, "0x%08x" % sig)
PY
)"
    LOG=build/hw/_trip_${R}.log
    if ! hw/board.sh "$XSDB" hw/xsdb_bench_gen.tcl "$BIT" xorshift 200 0x00100A00 "$SIG" "$SEED" "$R" > "$LOG" 2>&1; then
        echo "  rounds=$R FAILED -- see $LOG"
        tail -5 "$LOG"
        continue
    fi
    LINE=$(grep -m1 "completed=200" "$LOG")
    LATMIN=$(sed -E 's/.*latmin=([0-9]+).*/\1/' <<<"$LINE")
    LATMAX=$(sed -E 's/.*latmax=([0-9]+).*/\1/' <<<"$LINE")
    ODATA=$(sed -E 's/.*odata=([0-9]+).*/\1/' <<<"$LINE")
    printf '%d\t%s\t%s\t%s\t%s\n' "$R" "$LATMIN" "$LATMAX" "$ODATA" "$SIG" >> "$OUT"
    printf '  rounds=%-4d latmin=%-6s latmax=%-6s result=%-12s (oracle %s)\n' \
        "$R" "$LATMIN" "$LATMAX" "$ODATA" "$([ "$ODATA" = "$WANT" ] && echo PASS || echo "MISMATCH want=$WANT")"
done
echo "wrote $OUT"
