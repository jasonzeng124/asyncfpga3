#!/usr/bin/env bash
# gcd's cost model.  It is the flagship kernel and the only one whose
# per-iteration cost was never measured, because it is the awkward case: four
# loops, one of them nested inside another, and no argument that controls any
# of them.
#
# Same method as hw/isprime_cost.sh -- replay the C, count each loop's
# iterations for a chosen operand pair, and fit the per-iteration costs from
# measured batches.  The operand pairs are chosen to move the counters
# independently, which for gcd means deliberately covering:
#
#   shared powers of two   (1024,1024) drives the k loop and nothing else
#   one-sided even         (3<<20, 5) drives the pre-ctz and nothing else
#   both odd, coprime      (999983,999979) drives the main loop
#   (2^31-1, 1)            31 main iterations, the worst case in the domain
#
# gcd's operands are masked NONNEGATIVE in FIXED mode (DOMAIN_RESTRICTIONS), so
# every pair here stays under 2^31; the C is int32 and the masking is what
# keeps `a - b` and `-diff` representable.  Every point asserts its own derived
# oracle.
set -u
cd "$(dirname "$0")/.."
XSDB=${XSDB:-/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab/bin/xsdb}
CLK=${CLK:-0x00100A00}
BIT=build/hw/gcd_bench_gen/gcd_bench_gen.bit
OUT=build/hw/gcd_cost.tsv
[ -e "$BIT" ] || { echo "no bitstream at $BIT"; exit 2; }

PAIRS="1,1 3,3 97,89 255,254 1023,1 46341,46337 999983,999979 123456789,987654321
       1431655765,858993459 2147483647,1 1,2147483647 2147483647,2147483646
       1024,1024 65536,32768 268435456,268435456 1048576,3145728 50331648,83886080
       3145728,5 163840,7 12,18 48,18 786432,262144 6291456,11 2097152,1"
printf 'a\tb\tk\tctzpre\tmain\tctzin\tresult\tcycles\tlatmin\tlatmax\n' > "$OUT"
echo "gcd cost: FIXED N=200, 3 batches per point, oracle at every point"
for P in $PAIRS; do
    A=${P%,*}; B=${P#*,}
    read -r K CP MN CI RES SIG <<<"$(python3 - "$A" "$B" <<'PY'
import sys
a=int(sys.argv[1]); b=int(sys.argv[2])
k=cp=mn=ci=0
if a==0: res=b
elif b==0: res=a
else:
    while ((a|b)&1)==0: a>>=1; b>>=1; k+=1
    while a>0 and (a&1)==0: a>>=1; cp+=1
    while b>0 and (b&1)==0: b>>=1; cp+=1
    while a!=0:
        mn+=1
        diff=a-b
        if a<b: b=a
        a=diff if diff>=0 else -diff
        while a>0 and (a&1)==0: a>>=1; ci+=1
    res=b<<k
sig=0
for _ in range(200): sig=(((sig<<1)&0xffffffff)|(sig>>31))^(res&0xffffffff)
print(k,cp,mn,ci,res,"0x%08x"%sig)
PY
)"
    LOG=build/hw/_gcdcost_${A}_${B}.log
    if ! hw/board.sh "$XSDB" hw/xsdb_bench_gen.tcl "$BIT" gcd 200 "$CLK" "$SIG" "$A" "$B" 3 > "$LOG" 2>&1; then
        echo "  ($A,$B) FAILED"; grep -m1 "ORACLE FAILED\|ERROR\|TIMEOUT" "$LOG" || tail -3 "$LOG"; continue
    fi
    read -r CYC LO HI <<<"$(awk '/^[0-9]+\t[0-9]+\t/ {n++; s+=$2; if(lo==""||$4<lo)lo=$4; if($5>hi)hi=$5} END {printf "%.2f %s %s", s/n, lo, hi}' "$LOG")"
    printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$A" "$B" "$K" "$CP" "$MN" "$CI" "$RES" "$CYC" "$LO" "$HI" >> "$OUT"
    printf '  (%s,%s) k=%-3s ctzpre=%-3s main=%-3s ctzin=%-3s gcd=%-11s cycles/run=%.3f\n' \
        "$A" "$B" "$K" "$CP" "$MN" "$CI" "$RES" "$(python3 -c "print($CYC/200)")"
done
echo "wrote $OUT"
python3 hw/gcd_cost_fit.py "$OUT"
