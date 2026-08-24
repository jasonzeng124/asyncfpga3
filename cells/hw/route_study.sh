#!/usr/bin/env bash
# How much of a per-iteration cost number is the route?
#
# Every per-iteration figure in hw/README.md comes from one bitstream.  A
# bitstream is one place-and-route, and the tightening loop then sizes each
# matched delay FROM that route -- so two default builds of the same RTL
# disagree twice over: different routing, and different delay sizes derived
# from it.  This runs the default path repeatedly with NO seed pinned (pinning
# a seed sets PNR_TRIES=1 and removes the retry the default path relies on)
# and keeps each bitstream, so hw/xorshift_cost.sh can measure all of them.
#
# Usage: N=3 K=xorshift bash hw/route_study.sh
set -u
K=${K:-xorshift}
N=${N:-3}
OUTDIR=${OUTDIR:-build/hw/routestudy}
mkdir -p "$OUTDIR"
BIT=build/hw/${K}_bench_gen/${K}_bench_gen.bit
for i in $(seq 1 "$N"); do
    echo "=== route $i/$N: default rebuild of ${K}_bench_gen $(date -Is) ==="
    rm -f "$BIT"
    if bash hw/build_bench.sh "$K" > "$OUTDIR/_build_$i.log" 2>&1 && [ -e "$BIT" ]; then
        cp "$BIT" "$OUTDIR/${K}_route$i.bit"
        grep -E '^final:' "$OUTDIR/_build_$i.log" | tail -1
        echo "    saved $OUTDIR/${K}_route$i.bit"
    else
        echo "    BUILD FAILED -- see $OUTDIR/_build_$i.log"
        grep -E 'TIMING FAILED|RESULT:|NOT CONVERGING' "$OUTDIR/_build_$i.log" | head -3
    fi
done
echo "=== route study done $(date -Is) ==="
