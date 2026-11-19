#!/bin/bash
#CLUSTER array=1-7 cores=3 mem=16G time=240
# suite10d: loops whose 7 ratchet steps were done but whose final stack and draws ran out of time again (suite10c: sobel
# s1 / s2, video_filter s1 / s2, share_test_1 s2, single_loop s2; divres1: digitdiv s2), resumed from what came back
# (research/data/suite/resume/{suite10c,divres1}/K_S/) with BDC_RING_FUSE=0 (they are v7 loops: flow v8's ring fusion
# would rebuild a different circuit) and 2 draws, three cores, so the final stack and the draws fit.
# PREDICTION (18:01 UTC): every loop stops at once, rebuilds its route with the same sdf md5, and passes both draws.
set -uo pipefail
SPEC=(suite10c/sobel_1 suite10c/sobel_2 suite10c/video_filter_1 suite10c/video_filter_2 suite10c/share_test_1_2
      suite10c/single_loop_2 divres1/digitdiv_2)
RK=${SPEC[$((TASK - 1))]}; KS=${RK#*/}; K=${KS%_*}; S=${KS##*_}
D=$PWD/research/data/suite/resume/$RK
echo "suite10d kernel $K seed $S" > "$OUT/task.txt"
[ -f "$D/sizes_1.vh" ] || { echo "nothing to resume ($D)" >> "$OUT/task.txt"; exit 0; }
mkdir -p "$RUNS/state" && cp "$D"/* "$RUNS/state/"
CJ=2; [ "$K" = digitdiv ] && CJ=3
export CA_JOBS=$CJ DRAW_JOBS=2 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0 BDC_RING_FUSE=0 AUTO_RESUME=$RUNS/state
mkdir -p "$OUT/auto"
( while sleep 300; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 2 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
