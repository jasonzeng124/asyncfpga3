#!/bin/bash
#CLUSTER array=1-12 cores=2 mem=16G time=240
# suite10c: suite10b's loops that ran out of time, resumed from what came back (research/data/suite/resume/suite10b/K_S/)
# at this commit (flow v7 + the N-way mux select rule, which sobel needs). The divider kernels (digitdiv, digitsum,
# divmods) are NOT resumed: the automatic flow undersizes the divider's matched delay (test_divui: wrong answers on
# clean routes; subagent divsize), so their routes would only repeat that until it is fixed.
# PREDICTION (10:12 UTC): the loops with 6-7 ratchet steps stop at once and pass their draws; nest3 (3-5 steps) and
# sobel (5) finish their loops; every judged route passes.
set -uo pipefail
SPEC=(nest3_1 nest3_2 nest3_3 nest3_4 sobel_1 sobel_2 stencil_2d_1 share_test_1_2 single_loop_1 single_loop_2
      video_filter_1 video_filter_2)
KS=${SPEC[$((TASK - 1))]}; K=${KS%_*}; S=${KS##*_}
D=$PWD/research/data/suite/resume/suite10b/$KS
echo "suite10c kernel $K seed $S" > "$OUT/task.txt"
[ -f "$D/sizes_1.vh" ] || { echo "nothing to resume ($D)" >> "$OUT/task.txt"; exit 0; }
mkdir -p "$RUNS/state" && cp "$D"/* "$RUNS/state/"
export CA_JOBS=2 DRAW_JOBS=2 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0 AUTO_RESUME=$RUNS/state
mkdir -p "$OUT/auto"
( while sleep 300; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 4 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
