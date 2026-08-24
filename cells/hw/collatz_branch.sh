#!/usr/bin/env bash
# What does the EXPENSIVE branch of a bundled-data loop cost?
#
# hw/loop_cost.sh measured collatz with n = 2**k, which reaches 1 by halving
# every step -- so every number it produced is the cost of the CHEAP branch
# (a shift and a compare) and the 3n+1 branch was never executed once.  That
# is fine for a slope but it is not the loop's cost.
#
# Here the trip count is decomposed instead of controlled: for each n, python
# counts how many steps are even and how many are odd, the board measures the
# batch, and the two per-step costs are fitted jointly.  Powers of two (odd
# count exactly zero) pin the even coefficient on their own, so the odd
# coefficient is not being extracted from a collinear design matrix -- the two
# counts are otherwise correlated (o ~ 0.53e) and a fit over mixed n alone
# would not separate them.
#
# n is masked to 16 bits in FIXED mode (DOMAIN_RESTRICTIONS), so every point
# here is <= 65535 by construction, and each asserts its own derived oracle.
set -u
cd "$(dirname "$0")/.."
XSDB=${XSDB:-/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab/bin/xsdb}
CLK=${CLK:-0x00100A00}
K=${K:-collatz}
BIT=build/hw/${K}_bench_gen/${K}_bench_gen.bit
OUT=build/hw/collatz_branch_${K}.tsv
[ -e "$BIT" ] || { echo "no bitstream at $BIT"; exit 2; }

POINTS="16 256 4096 32768 32 1024 20480 3584 14592 61504 28704 40288 56496 26482 37167 52207 78 51968 111"
printf 'n\teven\todd\tsteps\tcycles\tlatmin\tlatmax\n' > "$OUT"
echo "collatz branch cost: $K, FIXED N=200 per point, 3 batches each"
for N in $POINTS; do
    read -r EV OD ST SIG <<<"$(python3 - "$N" <<'PY'
import sys
n=int(sys.argv[1]); e=o=0
while n!=1:
    if n%2: n=3*n+1; o+=1
    else: n//=2; e+=1
s=0; v=e+o
for _ in range(200): s=(((s<<1)&0xffffffff)|(s>>31))^v
print(e,o,e+o,"0x%08x"%s)
PY
)"
    LOG=build/hw/_cbranch_${K}_${N}.log
    if ! hw/board.sh "$XSDB" hw/xsdb_bench_gen.tcl "$BIT" "$K" 200 "$CLK" "$SIG" "$N" 0 3 > "$LOG" 2>&1; then
        echo "  n=$N FAILED"; grep -m1 "ORACLE FAILED\|ERROR" "$LOG" || tail -3 "$LOG"; continue
    fi
    read -r CYC LO HI <<<"$(awk '/^[0-9]+\t[0-9]+\t/ {n++; s+=$2; if(lo==""||$4<lo)lo=$4; if($5>hi)hi=$5} END {printf "%.1f %s %s", s/n, lo, hi}' "$LOG")"
    printf '%d\t%d\t%d\t%d\t%s\t%s\t%s\n' "$N" "$EV" "$OD" "$ST" "$CYC" "$LO" "$HI" >> "$OUT"
    printf '  n=%-6d even=%-3d odd=%-3d steps=%-4d cycles/batch=%-9s lat=%s..%s\n' "$N" "$EV" "$OD" "$ST" "$CYC" "$LO" "$HI"
done
echo "wrote $OUT"
python3 hw/collatz_branch_fit.py "$OUT"
