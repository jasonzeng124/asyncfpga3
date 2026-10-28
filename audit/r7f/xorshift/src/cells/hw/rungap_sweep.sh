#!/usr/bin/env bash
# Two questions, one sweep.
#
# (1) gen_bench.py documents CYCLES as EXCLUDING the S_PREP settling gap, with
#     PREPCYC counting it separately.  Every per-run cost quoted in this file
#     rests on that being true.  Sweeping RUNGAP checks it: CYCLES should be
#     flat and PREPCYC should be exactly (gap+1) per run.
#
# (2) RUNGAP=0 is the bench's maximum issue rate, and that is the regime where
#     batches used to park forever in S_WAIT_RES.  That was root-caused to an
#     unsynchronised async-SET flop gating the 3-bit state register and fixed
#     with a synchroniser -- not a delay -- but the fix has never been re-run
#     at the rate that exposed it.  A clean oracle-checked batch at gap 0 is
#     that regression test.
set -u
cd "$(dirname "$0")/.."
XSDB=${XSDB:-/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab/bin/xsdb}
CLK=${CLK:-0x00100A00}
K=${K:-xorshift}
BIT=build/hw/${K}_bench_gen/${K}_bench_gen.bit
OUT=build/hw/rungap_${K}.tsv
[ -e "$BIT" ] || { echo "no bitstream at $BIT"; exit 2; }
read -r GOLD OP0 OP1 <<<"$(awk -v k="$K" '$1==k {print $2, $3, $4; exit}' hw/golden_sig.txt)"

printf 'gap\trep\tcycles\tprepcyc\tlatmin\tlatmax\n' > "$OUT"
echo "RUNGAP sweep: $K op0=$OP0 op1=$OP1, 3 batches of 200 per gap, oracle at every batch"
for G in 0 1 2 4 8 15 31 63 127; do
    LOG=build/hw/_rungap_${K}_${G}.log
    if ! hw/board.sh "$XSDB" hw/xsdb_bench_gen.tcl "$BIT" "$K" 200 "$CLK" "$GOLD" "$OP0" "$OP1" 3 "$G" > "$LOG" 2>&1; then
        echo "  gap=$G FAILED"; grep -m1 "ORACLE FAILED\|ERROR\|TIMEOUT" "$LOG" || tail -3 "$LOG"; continue
    fi
    awk -v g="$G" '/^[0-9]+\t[0-9]+\t/ {print g "\t" $0}' "$LOG" >> "$OUT"
    echo "  gap=$G  $(awk '/^[0-9]+\t[0-9]+\t/ {n++; c+=$2; p+=$3} END {printf "cycles/run %.3f   prepcyc/run %.3f", c/n/200, p/n/200}' "$LOG")"
done
echo "wrote $OUT"
