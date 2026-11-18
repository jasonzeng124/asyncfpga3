#!/bin/bash
#CLUSTER array=1-8 cores=8 mem=24G time=240
# suite7: gcd and isprime x seeds 1-4 on 8 cores, flow v5 (as suite6); 4 draws each.
set -uo pipefail
KS=(gcd isprime)
K=${KS[$(( (TASK - 1) / 4 ))]}; S=$(( (TASK - 1) % 4 + 1 ))
export CA_JOBS=4 DRAW_JOBS=2 PNR_TIMEOUT=7200
echo "suite7 kernel $K seed $S" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
( while sleep 600; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
ND=8; export AUTO_FINISH=3
case $K in gcd|isprime) ND=4; AUTO_FINISH=1;; esac   # their simulations are slow: keep the task under its 240 min
research/tools/suite/suite_one.sh "$K" "$S" $ND 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
