#!/bin/bash
#CLUSTER array=1-8 cores=2 mem=16G time=240
# muxn1: the kernels with an N-way mux (bdc_muxnN) through the automatic flow now that the sizing rule measures the
# mux's select decode race (BD_SKEW_MUXN=1, on by default in auto_size.sh since 51ce3b921; subagent muxsel): cmpchain
# seeds 1-4 (its loops shrank the guarding select links to 1 element; GLS showed runts on the decode outputs), and
# iterative_sqrt / sobel seeds 1-2. Flow v7 (CA_FAST, the search phase, the RAM guard, the seed fallback), 4 draws with
# the runt monitor reporting (GATE_RUNTS=1). gcd / isprime are left to a later round (8 cores each).
# PREDICTION (05:47 UTC): cmpchain's select links end at 5-8 elements (not 1), no draw shows a pulse under 1 ns, every
# draw passes; P a little above suite9's (the guard is on the cycle only where the mux is).
set -uo pipefail
SPEC=(cmpchain_1 cmpchain_2 cmpchain_3 cmpchain_4 iterative_sqrt_1 iterative_sqrt_2 sobel_1 sobel_2)
KS=${SPEC[$((TASK - 1))]}; K=${KS%_*}; S=${KS##*_}
export CA_JOBS=2 DRAW_JOBS=2 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0
echo "muxn1 kernel $K seed $S" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
( while sleep 300; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 4 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
