#!/usr/bin/env bash
# xorshift's per-iteration cost, measured the way the other kernels now are.
#
# hw/loop_cost.sh already sweeps this kernel, but it records LATMIN/LATMAX --
# a per-run register with a +-1 sampling ambiguity -- and fits one slope with
# no error bar.  ipow turned out to be bit-exact in its batch total while
# reporting latmin != latmax, which is what showed the batch total to be the
# statistic worth fitting.  So: same sweep, CYCLES/completed instead, three
# batches per point, and a standard error on the slope.
#
# rounds is an explicit argument here, so no replay is needed to know the trip
# count -- but it is masked to 12 bits (DOMAIN_RESTRICTIONS), so every point
# stays under 4096 and each still asserts its own derived oracle.
set -u
cd "$(dirname "$0")/.."
XSDB=${XSDB:-/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab/bin/xsdb}
CLK=${CLK:-0x00100A00}
BIT=${BIT:-build/hw/xorshift_bench_gen/xorshift_bench_gen.bit}
OUT=${OUT:-build/hw/xorshift_cost.tsv}
[ -e "$BIT" ] || { echo "no bitstream at $BIT"; exit 2; }

POINTS="0 1 2 3 4 6 8 12 16 24 32 48 64 96 128 192 256"
printf 'rounds\tcycles\tlatmin\tlatmax\tresult\n' > "$OUT"
echo "xorshift cost: FIXED N=200, 3 batches per point, oracle at every point"
for R in $POINTS; do
    read -r WANT SIG <<<"$(python3 - "$R" <<'PY'
import sys
M = 0xffffffff
x = 2463534242
for _ in range(int(sys.argv[1])):
    x = (x ^ (x << 13)) & M; x ^= x >> 17; x = (x ^ (x << 5)) & M
s = 0
for _ in range(200): s = (((s << 1) & M) | (s >> 31)) ^ x
print(x, "0x%08x" % s)
PY
)"
    LOG=build/hw/_xcost_${R}.log
    if ! hw/board.sh "$XSDB" hw/xsdb_bench_gen.tcl "$BIT" xorshift 200 "$CLK" "$SIG" 2463534242 "$R" 3 > "$LOG" 2>&1; then
        echo "  rounds=$R FAILED"; grep -m1 "ORACLE FAILED\|ERROR" "$LOG" || tail -3 "$LOG"; continue
    fi
    read -r CYC LO HI <<<"$(awk '/^[0-9]+\t[0-9]+\t/ {n++; s+=$2; if(lo==""||$4<lo)lo=$4; if($5>hi)hi=$5} END {printf "%.2f %s %s", s/n, lo, hi}' "$LOG")"
    printf '%d\t%s\t%s\t%s\t%s\n' "$R" "$CYC" "$LO" "$HI" "$WANT" >> "$OUT"
    printf '  rounds=%-5d cycles/batch=%-11s cycles/run=%-8.3f lat=%s..%s\n' "$R" "$CYC" "$(python3 -c "print($CYC/200)")" "$LO" "$HI"
done
echo "wrote $OUT"
python3 - "$OUT" <<'PY'
import sys, math
rows=[]
for ln in open(sys.argv[1]).readlines()[1:]:
    r,c,lo,hi,w=ln.split(); rows.append((int(r), float(c)/200))
n=len(rows); sx=sum(r for r,_ in rows); sy=sum(y for _,y in rows)
sxx=sum(r*r for r,_ in rows); sxy=sum(r*y for r,y in rows)
d=n*sxx-sx*sx; a=(n*sxy-sx*sy)/d; b=(sy-a*sx)/n
res=[y-(a*r+b) for r,y in rows]; s2=sum(e*e for e in res)/(n-2)
sea=math.sqrt(s2*n/d); seb=math.sqrt(s2*sxx/d)
print()
print(f"  per ROUND      {a:>8.4f} +- {sea:.4f} cycles   ({a*10:>7.2f} +- {sea*10:.2f} ns at 100 MHz)")
print(f"  base           {b:>8.4f} +- {seb:.4f} cycles   ({b*10:>7.2f} +- {seb*10:.2f} ns)")
print(f"  residual RMS {math.sqrt(s2):.4f} cycles over {n} points, {n-2} dof")
print()
print("  rounds  measured   fitted    resid")
for (r,y),e in zip(rows,res): print(f"  {r:>6} {y:>9.3f} {y-e:>8.3f} {e:>+8.3f}")
PY
