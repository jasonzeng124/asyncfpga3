#!/bin/bash
#CLUSTER array=1-4 cores=8 mem=32G time=240
# divres1: suite10b's divider loops that ran out of time (digitdiv s1 / s2, digitsum s2, divmods s1), resumed from what
# came back (research/data/suite/resume/suite10b/K_S/) at this commit: rule A's peers confined to the cell (subagent
# divsize, 1daa7efd4; it changes no rule output on these kernels, whose dividers reach the bench through a fork / pipe /
# link, but it is the head's rule), flow v7 + the N-way mux rule. 8 cores (CA_JOBS=4): a 2000-LUT divider makes every
# sensitivity run slow (~2.5 min each at one job per corner).
# PREDICTION (10:52 UTC): the divider line ends near 300-350 links (divmodu's suite10b routes: 319 / 345), every draw
# passes, no runt.
set -uo pipefail
SPEC=(digitdiv_1 digitdiv_2 digitsum_2 divmods_1)
KS=${SPEC[$((TASK - 1))]}; K=${KS%_*}; S=${KS##*_}
D=$PWD/research/data/suite/resume/suite10b/$KS
echo "divres1 kernel $K seed $S" > "$OUT/task.txt"
[ -f "$D/sizes_1.vh" ] || { echo "nothing to resume ($D)" >> "$OUT/task.txt"; exit 0; }
mkdir -p "$RUNS/state" && cp "$D"/* "$RUNS/state/"
export CA_JOBS=4 DRAW_JOBS=3 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0 AUTO_RESUME=$RUNS/state
mkdir -p "$OUT/auto"
( while sleep 300; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 4 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
