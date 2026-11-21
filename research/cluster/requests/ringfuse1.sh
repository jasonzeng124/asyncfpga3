#!/bin/bash
#CLUSTER array=1-44 cores=3 mem=16G time=240
# ringfuse1 (subagent ringfuse, 2026-11-19): BDC_RING_FUSE=2 -- the loop's update and test fused into one cell with two
# results (bdc/emit.py _ring_merge: a fork that splits a fused region's result between a fusable reader and anything
# else is absorbed; refused across basic blocks, above 8 members, or where a result re-enters the region without an
# iteration boundary), and a link on the cell's 1-bit test output -- through the WHOLE automatic flow (BDC_AUTO=1, no
# kernel list, flow v7 with its search phase), 8 draws (countloop 4, as nsearch1), on the four kernels whose counter /
# test ring it changes: xorshift, collatz, countloop, ipow x seeds 1-8 (tasks 1-32). Tasks 33-44: the SAME flow v7
# WITHOUT the switch where no v7 column exists yet (countloop seeds 5-8; ipow seeds 1-8: suite6 is flow v6), so every
# kernel has a v7 baseline per seed: xorshift / collatz from nsearch1 (+ norw1r2 for xorshift s7, collatz s1),
# countloop s1-4 from nsearch1.
# Local (ringfuse, nextpnr 6e5d224472232d5d, 4 draws): =2 xorshift s1 18.79 (base 20.55), countloop s1 19.58 (base
# v7 20.92); see research/data/ringfuse/README.md for every seed run and the =1 column (the merge without the link:
# return-to-zero binds, worse on 3 of 4).
# PREDICTION (written with the request): medians xorshift and countloop 0.5-1.5 ns below the v7 column, collatz and
# ipow within +-1 ns of it (their floors are not the counter / test ring: collatz couples through the shared source,
# ipow's floor is the multiply ring); every judged route passes its draws, 0 runts under 1 ns.
set -uo pipefail
if [ "$TASK" -le 32 ]; then
  KS=(xorshift collatz countloop ipow); K=${KS[$(( (TASK - 1) / 8 ))]}; S=$(( (TASK - 1) % 8 + 1 )); ARM=rf2
  export BDC_RING_FUSE=2
else
  SPEC=(countloop_5 countloop_6 countloop_7 countloop_8 ipow_1 ipow_2 ipow_3 ipow_4 ipow_5 ipow_6 ipow_7 ipow_8)
  KS=${SPEC[$((TASK - 33))]}; K=${KS%_*}; S=${KS##*_}; ARM=v7
  unset BDC_RING_FUSE
fi
ND=8; [ "$K" = countloop ] && ND=4
export CA_JOBS=2 DRAW_JOBS=1 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0
echo "ringfuse1 arm $ARM kernel $K seed $S" > "$OUT/task.txt"
mkdir -p "$OUT/auto"
( while sleep 300; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$RUNS/auto/su_${K}_$S/"*.env "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" $ND 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$RUNS/auto/su_${K}_$S/"*.env "$OUT/auto/" 2>/dev/null
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
for g in research/data/eventgraph/graphs/su_${K}_${S}_*; do [ -f "$g/check.txt" ] && cp "$g/check.txt" "$OUT/check_$(basename "$g").txt"; done
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
