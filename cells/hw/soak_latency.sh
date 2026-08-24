#!/usr/bin/env bash
# Long-run stability of the measured latency, with the oracle asserted.
#
# The repeatability study covers minutes: 4 programmings x 8 batches, taken
# back to back, showed <= 0.06% across-programming scatter and no trend against
# repeat index.  It cannot say anything about hours -- die temperature, the
# JTAG/PS state a long session accumulates, or a kernel that only goes wrong
# occasionally.  This samples one kernel per tick, rotating, and writes a row
# per sample so the answer is a time series rather than a verdict.
#
# Each tick reprograms.  That is deliberate: it is the path a real measurement
# takes, and configuration noise belongs inside the number rather than being
# excluded from it.
#
#   INTERVAL=600 HOURS=6 hw/soak_latency.sh
set -u
cd "$(dirname "$0")/.."
XSDB=${XSDB:-/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab/bin/xsdb}
CLK=${CLK:-0x00100A00}
INTERVAL=${INTERVAL:-600}
HOURS=${HOURS:-6}
KERNELS=${KERNELS:-xorshift ipow collatz collatz64 isprime}
OUT=build/hw/soak_latency.tsv
END=$(( $(date +%s) + HOURS * 3600 ))

# Pin the bitstreams.  A soak runs for hours next to a toolchain that is very
# likely rebuilding something, and build_bench.sh writes straight over
# build/hw/<top>/<top>.bit.  A rebuild landing mid-soak does not corrupt the
# run in any way the oracle can see -- the new route computes the same answers
# -- it silently changes what is being soaked, which is worse: the time series
# gets a step in it that looks like drift.  Copy once, program from the copy.
PIN=build/hw/soak_pinned
mkdir -p "$PIN"
for K in $KERNELS; do
    SRC=build/hw/${K}_bench_gen/${K}_bench_gen.bit
    [ -e "$SRC" ] && cp "$SRC" "$PIN/${K}.bit"
done

[ -e "$OUT" ] || printf 'unix\tiso\tkernel\trep\tcycles\tprepcyc\tlatmin\tlatmax\tsig\tstatus\n' > "$OUT"
echo "soak: ${HOURS}h, one kernel per ${INTERVAL}s tick, rotating over: $KERNELS"
set -- $KERNELS
i=0
while [ "$(date +%s)" -lt "$END" ]; do
    n=$#; idx=$(( i % n )); K=$(eval echo "\${$((idx + 1))}"); i=$((i + 1))
    BIT=$PIN/${K}.bit
    if [ ! -e "$BIT" ]; then continue; fi
    read -r GOLD OP0 OP1 <<<"$(awk -v k="$K" '$1==k {print $2, $3, $4; exit}' hw/golden_sig.txt)"
    LOG=build/hw/_soak_${K}.log
    NOW=$(date +%s); ISO=$(date -Iseconds)
    if hw/board.sh "$XSDB" hw/xsdb_bench_gen.tcl "$BIT" "$K" 200 "$CLK" "$GOLD" "$OP0" "$OP1" 3 > "$LOG" 2>&1; then
        awk -v u="$NOW" -v t="$ISO" -v k="$K" \
            '/^[0-9]+\t[0-9]+\t/ {print u "\t" t "\t" k "\t" $0 "\tOK"}' "$LOG" >> "$OUT"
        echo "$ISO $K $(awk '/^[0-9]+\t[0-9]+\t/ {n++; c+=$2} END {printf "%.1f cycles/batch over %d", c/n, n}' "$LOG")"
    else
        printf '%s\t%s\t%s\t-\t-\t-\t-\t-\t-\tFAIL\n' "$NOW" "$ISO" "$K" >> "$OUT"
        echo "$ISO $K FAILED -- $(grep -m1 'ORACLE FAILED\|ERROR\|TIMEOUT' "$LOG" | cut -c1-120)"
    fi
    sleep "$INTERVAL"
done
echo "soak done $(date -Iseconds); $(( $(grep -c FAIL "$OUT") )) failing sample(s) in $(( $(wc -l < "$OUT") - 1 )) rows"
