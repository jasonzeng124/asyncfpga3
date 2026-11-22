#!/bin/bash
#CLUSTER array=1-9 cores=2 mem=16G time=240
# suite9r4: suite9r3's 9 loops that ran out of time again (memsum s1, sumi3_mem s1-4, fir s1-4: 1000-element arrays,
# refilled through the host port before every call, so the final stack and the draws are slow), resumed from what came
# back (research/data/suite/resume/suite9r3/K_S/), the loop they started with (AUTO_SEARCH=0: finish, not a new phase),
# 2 draws instead of 4 so the draws fit.
# PREDICTION (09:14 UTC): the loops stop at once (6-7 ratchet steps done), rebuild their route with the same sdf md5, and
# both draws pass on every route.
set -uo pipefail
SPEC=(memsum_1 sumi3_mem_1 sumi3_mem_2 sumi3_mem_3 sumi3_mem_4 fir_1 fir_2 fir_3 fir_4)
KS=${SPEC[$((TASK - 1))]}; K=${KS%_*}; S=${KS##*_}
D=$PWD/research/data/suite/resume/suite9r3/$KS
echo "suite9r4 kernel $K seed $S" > "$OUT/task.txt"
[ -f "$D/sizes_1.vh" ] || { echo "nothing to resume ($D)" >> "$OUT/task.txt"; exit 0; }
mkdir -p "$RUNS/state" && cp "$D"/* "$RUNS/state/"
export CA_JOBS=2 DRAW_JOBS=2 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0 AUTO_SEARCH=0 AUTO_RESUME=$RUNS/state
mkdir -p "$OUT/auto"
( while sleep 300; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 2 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
