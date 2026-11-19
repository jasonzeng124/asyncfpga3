#!/bin/bash
#CLUSTER array=1-4 cores=2 mem=16G time=240
# ifl1: if_loop_1 seeds 1-4 from scratch with the flow at this commit (v7 + rule B's RAM guard 400 ps, the default since
# 34c90ae2d; subagent ifloop showed the host fill's WE race on seed 1 that the unguarded rule passed at +79 ps, fixed on
# that route by the guard's raise, 8 / 8 draws). Its suite8 / suite9 / suite9r3 routes were sized without the guard.
# 4 draws, the runt monitor reporting.
# PREDICTION (12:48 UTC): every route passes its draws; the host-slot setup lines end longer than suite9's (USETUP >= 5).
set -uo pipefail
K=if_loop_1; S=$TASK
export CA_JOBS=2 DRAW_JOBS=2 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0
echo "ifl1 kernel $K seed $S" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
( while sleep 300; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 4 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
