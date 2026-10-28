#!/usr/bin/env bash
# Per-iteration cost of each kernel's loop, measured on silicon by sweeping an
# input rather than by rebuilding anything.
#
#   hw/loop_cost.sh <kernel>        kernel in {xorshift ipow collatz collatz64}
#
# Generalises hw/trip_sweep.sh, which did this for xorshift only.  Each kernel
# needs a different trick to make its TRIP COUNT a function of an operand:
#
#   xorshift   rounds is literally an argument
#   ipow       the loop runs once per bit of e, so e = 2**k - 1 gives exactly k
#              iterations AND sets every bit, so both variable*variable
#              multiplies execute every iteration (the expensive path)
#   collatz    n = 2**k reaches 1 in exactly k steps, all of them the even
#              branch -- so this measures the SHIFT path, not the 3n+1 path
#   collatz64  same construction; op1=0 keeps the 64-bit n inside 32 bits
#
# MIND THE DOMAIN MASKS.  gen_bench.py's DOMAIN_RESTRICTIONS apply in FIXED
# mode, not only to the uniform generator: collatz's n is masked to 16 bits
# (so 3n+1 cannot overflow int32) with zero mapped to 1, and xorshift's rounds
# to 12 bits.  Sweeping collatz past k=15 therefore feeds it n=0 -> n=1 and it
# returns 0 steps.  That is not a kernel bug and it is not a fast loop; it is
# an out-of-domain input, and the per-point oracle is what caught it -- the
# k>=16 points failed with "folded to 0x00000000, expected 0x00000ff0" instead
# of quietly contributing four fast rows to a slope.
#
# Every point asserts a DERIVED oracle: the expected result is computed here
# from the kernel's C and folded the way the RTL folds it.  A loop that exits
# early otherwise reads as a fast loop, which is how an under-delayed build
# once passed every check in this bench.  Points are also NOT comparable across
# kernels as absolute speed -- they measure different loop bodies -- the useful
# comparison is the SLOPE, which is what one iteration of that body costs.
set -u
cd "$(dirname "$0")/.."

K=${1:?usage: hw/loop_cost.sh <xorshift|ipow|collatz|collatz64>}
CLK=${CLK:-0x00100A00}
XSDB=${XSDB:-/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab/bin/xsdb}
BIT=build/hw/${K}_bench_gen/${K}_bench_gen.bit
OUT=build/hw/loop_cost_${K}.tsv
[ -e "$BIT" ] || { echo "no bitstream at $BIT"; exit 2; }

case "$K" in
    xorshift)  POINTS="1 2 4 8 16 32 64 128 256" ;;
    ipow)      POINTS="1 2 4 6 8 12 16 20 24 28 31" ;;
    collatz)   POINTS="1 2 4 6 8 10 12 14 15" ;;   # n=2**k, k<=15: the 16-bit domain mask
    collatz64) POINTS="1 2 4 8 12 16 20 24 28 30" ;;
    *) echo "unknown kernel $K"; exit 2 ;;
esac

printf 'iters\tlatmin\tlatmax\tresult\tsig\n' > "$OUT"
echo "loop cost: $K, clk=$CLK, FIXED N=200 per point, oracle asserted at every point"

for I in $POINTS; do
    read -r OP0 OP1 WANT SIG <<<"$(python3 - "$K" "$I" <<'PY'
import sys
k, i = sys.argv[1], int(sys.argv[2])
M = 0xffffffff
if k == "xorshift":
    op0, op1 = 2463534242, i
    x = op0
    for _ in range(i):
        x = (x ^ (x << 13)) & M; x ^= x >> 17; x = (x ^ (x << 5)) & M
    want = x
elif k == "ipow":
    op0, op1 = 3, (1 << i) - 1          # e = 2**i - 1 -> exactly i iterations
    want = pow(op0, op1, 1 << 32)
else:                                    # collatz / collatz64: n = 2**i -> i steps
    op0, op1 = 1 << i, 0
    want = i
sig = 0
for _ in range(200):
    sig = (((sig << 1) & M) | (sig >> 31)) ^ (want & M)
print(op0, op1, want, "0x%08x" % sig)
PY
)"
    LOG=build/hw/_loop_${K}_${I}.log
    if ! hw/board.sh "$XSDB" hw/xsdb_bench_gen.tcl "$BIT" "$K" 200 "$CLK" "$SIG" "$OP0" "$OP1" > "$LOG" 2>&1; then
        echo "  iters=$I FAILED (op0=$OP0 op1=$OP1 want=$WANT) -- see $LOG"
        grep -m1 "ORACLE FAILED\|ERROR" "$LOG" || tail -3 "$LOG"
        continue
    fi
    LINE=$(grep -m1 "completed=200" "$LOG")
    LATMIN=$(sed -E 's/.*latmin=([0-9]+).*/\1/' <<<"$LINE")
    LATMAX=$(sed -E 's/.*latmax=([0-9]+).*/\1/' <<<"$LINE")
    ODATA=$(sed -E 's/.*odata=([0-9]+).*/\1/' <<<"$LINE")
    printf '%d\t%s\t%s\t%s\t%s\n' "$I" "$LATMIN" "$LATMAX" "$ODATA" "$SIG" >> "$OUT"
    printf '  iters=%-4d latmin=%-6s latmax=%-6s result=%-12s\n' "$I" "$LATMIN" "$LATMAX" "$ODATA"
done
echo "wrote $OUT"
