#!/bin/bash
#CLUSTER array=1-24 cores=3 mem=16G time=240
# norw1r2: norw1's tasks that hit the 240-min limit (the automatic column with no kernel list: BDC_AUTO=1, rewrites
# off), continued from the loop state they sent back (research/data/suite/resume/norw1/K_S/; auto_size.sh AUTO_RESUME)
# at this commit: the same rule (now CA_FAST=1 -- identical proposals, faster) and the bench-clock seed fallback; the
# draws three at a time (norw1 ran them one at a time, which is where most collatz64 tasks ran out: 6-7 ratchet steps
# done). A task with no state exits at once. 8 draws per route at suite6's / norw1's draw points.
# PREDICTION (01:31 UTC): the resumed loops that had finished rebuild their shipped route with the same sdf md5 (log.txt
# says so) and pass all 8 draws; collatz64 without its rewrite lands well above suite6's 23.01 ns (the hand recipes'
# rewrite was worth ~9 ns on collatz64: ~28-32 ns).
set -uo pipefail
KS=(xorshift collatz collatz64)
K=${KS[$(( (TASK - 1) / 8 ))]}; S=$(( (TASK - 1) % 8 + 1 ))
D=$PWD/research/data/suite/resume/norw1/${K}_$S
echo "norw1r2 kernel $K seed $S" > "$OUT/task.txt"
[ -f "$D/sizes_1.vh" ] || { echo "nothing to resume ($D)" >> "$OUT/task.txt"; exit 0; }
mkdir -p "$RUNS/state" && cp "$D"/* "$RUNS/state/"
export CA_JOBS=2 DRAW_JOBS=3 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0 AUTO_RESUME=$RUNS/state
mkdir -p "$OUT/auto"
( while sleep 300; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" 8 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$OUT/auto/" 2>/dev/null
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
