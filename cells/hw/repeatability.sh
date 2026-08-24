#!/usr/bin/env bash
# How much does a measured latency move if nothing changes?
#
#   hw/repeatability.sh [kernel ...]
#
# Every latency in hw/README.md is one batch from one programming, quoted to
# three or four digits with no error bar.  Two different noise terms sit under
# those digits and neither has been measured:
#
#   WITHIN  repeat the same FIXED batch without reprogramming.  The DUT is
#           bundled-data and has no clock, so this is PVT drift plus the
#           +-1 cycle quantisation of a 100 MHz counter -- nothing else can
#           move.
#   ACROSS  reprogram the SAME bitstream and measure again.  Same route, same
#           sizes, same silicon; only configuration and PS state differ.
#
# Both are reported as ppm of the mean, because that is the unit the claims
# are in: the clock sweep concluded ns/iter was constant "to 0.1%", which is
# only meaningful against a noise floor.
set -u
cd "$(dirname "$0")/.."

XSDB=${XSDB:-/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab/bin/xsdb}
CLK=${CLK:-0x00100A00}
WITHIN=${WITHIN:-8}      # batches per programming
ACROSS=${ACROSS:-4}      # programmings
KERNELS=${*:-xorshift ipow collatz collatz64 isprime}
OUT=build/hw/repeatability.tsv

printf 'kernel\tprog\trep\tcycles\tprepcyc\tlatmin\tlatmax\tsig\n' > "$OUT"
for K in $KERNELS; do
    BIT=build/hw/${K}_bench_gen/${K}_bench_gen.bit
    [ -e "$BIT" ] || { echo "$K: no bitstream, skipped"; continue; }
    read -r GOLD OP0 OP1 <<<"$(awk -v k="$K" '$1==k {print $2, $3, $4; exit}' hw/golden_sig.txt)"
    echo "=== $K  op0=$OP0 op1=$OP1 gold=$GOLD  ${ACROSS}x programming, ${WITHIN}x batch ==="
    for P in $(seq 0 $((ACROSS - 1))); do
        LOG=build/hw/_repeat_${K}_${P}.log
        if ! hw/board.sh "$XSDB" hw/xsdb_bench_gen.tcl "$BIT" "$K" 200 "$CLK" "$GOLD" "$OP0" "$OP1" "$WITHIN" > "$LOG" 2>&1; then
            echo "  prog $P FAILED -- see $LOG"; grep -m1 "ORACLE FAILED\|ERROR" "$LOG" || tail -3 "$LOG"; continue
        fi
        awk -v k="$K" -v p="$P" '/^[0-9]+\t[0-9]+\t/ {print k "\t" p "\t" $0}' "$LOG" >> "$OUT"
        echo "  prog $P: $(awk '/^[0-9]+\t[0-9]+\t/ {c[NR]=$2} END {n=0;s=0;mn=1e18;mx=0; for(i in c){n++;s+=c[i]; if(c[i]<mn)mn=c[i]; if(c[i]>mx)mx=c[i]} printf "%d batches, cycles mean %.1f spread %d (%.0f ppm)", n, s/n, mx-mn, (mx-mn)/(s/n)*1e6}' "$LOG")"
    done
done
echo "wrote $OUT"
python3 hw/repeatability_report.py "$OUT"
