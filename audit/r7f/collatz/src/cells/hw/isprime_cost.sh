#!/usr/bin/env bash
# isprime is the only kernel with NESTED loops and an early return, and it was
# the one loop_cost.sh could not sweep: its trip count is not an argument.  It
# does not have to be.  The C is deterministic, so python replays it exactly and
# counts each n's outer trials and inner shift steps, and the two per-step costs
# are fitted from the measured batches.
#
# The three natural counts are linearly dependent -- the shift-down loop runs
# exactly one more step per trial than the shift-up loop, so down == up + outer
# -- and fitting all three would silently invent a decomposition the data does
# not contain.  Regress on (outer, inner) instead, which is a full-rank basis
# for the same span.
#
# Leverage comes from the design, not the count: n = 2 and 3 exit before the
# outer loop (outer == 0, inner == 0) and pin the base directly, while
# 1000/5000/60000 are even so they take exactly ONE outer trial with a varying
# number of inner shifts, which separates the two coefficients.  Primes run the
# outer loop to sqrt(n).
set -u
cd "$(dirname "$0")/.."
XSDB=${XSDB:-/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab/bin/xsdb}
CLK=${CLK:-0x00100A00}
BIT=build/hw/isprime_bench_gen/isprime_bench_gen.bit
OUT=build/hw/isprime_cost.tsv
[ -e "$BIT" ] || { echo "no bitstream at $BIT"; exit 2; }

POINTS="2 3 4 9 15 25 35 49 121 143 169 289 1000 5000 60000 1009 2003 4001 7919 10007 65521 99991 47 97"
printf 'n\touter\tinner\tresult\tcycles\tlatmin\tlatmax\n' > "$OUT"
echo "isprime cost: FIXED N=200 per point, 3 batches each, oracle at every point"
for N in $POINTS; do
    read -r OUTER INNER RES SIG <<<"$(python3 - "$N" <<'PY'
import sys
n0=int(sys.argv[1]); n=n0
outer=up=down=0; res=1
if n<2: res=0
else:
    d=2
    while d*d<=n:
        outer+=1
        r=n; s=d; half=n>>1
        while s<=half: s<<=1; up+=1
        while s>=d:
            if r>=s: r-=s
            s>>=1; down+=1
        if r==0: res=0; break
        d+=1
sig=0
for _ in range(200): sig=(((sig<<1)&0xffffffff)|(sig>>31))^res
print(outer, up+down, res, "0x%08x"%sig)
PY
)"
    LOG=build/hw/_isprime_cost_${N}.log
    if ! hw/board.sh "$XSDB" hw/xsdb_bench_gen.tcl "$BIT" isprime 200 "$CLK" "$SIG" "$N" 0 3 > "$LOG" 2>&1; then
        echo "  n=$N FAILED"; grep -m1 "ORACLE FAILED\|ERROR" "$LOG" || tail -3 "$LOG"; continue
    fi
    read -r CYC LO HI <<<"$(awk '/^[0-9]+\t[0-9]+\t/ {c++; s+=$2; if(lo==""||$4<lo)lo=$4; if($5>hi)hi=$5} END {printf "%.1f %s %s", s/c, lo, hi}' "$LOG")"
    printf '%d\t%d\t%d\t%d\t%s\t%s\t%s\n' "$N" "$OUTER" "$INNER" "$RES" "$CYC" "$LO" "$HI" >> "$OUT"
    printf '  n=%-6d outer=%-4d inner=%-5d isprime=%d cycles/batch=%-10s lat=%s..%s\n' "$N" "$OUTER" "$INNER" "$RES" "$CYC" "$LO" "$HI"
done
echo "wrote $OUT"
python3 hw/isprime_cost_fit.py "$OUT"
