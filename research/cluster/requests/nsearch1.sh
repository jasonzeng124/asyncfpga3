#!/bin/bash
#CLUSTER array=1-18 cores=3 mem=16G time=240
# nsearch1: the event graph's storage search INSIDE the automatic flow, on the column with no kernel list. Each task
# resumes a finished loop (research/data/suite/resume/norw1s/K_S: norw1's xorshift / collatz routes, rewrites off;
# suite3a's countloop routes, which no rewrite ever touched), so the replay stops, final() rebuilds the shipped route
# (same sdf md5, checked in log.txt) and runs the full stack, then auto_size.sh's search phase (AUTO_SEARCH=1, xorgap)
# with AUTO_SEARCH_ARGS="--all-sites --buildable-only --wire 1000" (graphsearch: a latch on any fork output or merge
# output as well as +1 link depth; 1 ns of wire charged per inserted stage), raise-only from the shipped sizes for at
# most 4 routes, the new route shipped only if clean and faster; then 8 draws (countloop 4) at the original draw points.
# A per-seed A/B against the shipped route of the same loop. CA_FAST, the RAM guard and the seed fallback are on.
# PREDICTION (02:29 UTC): xorshift: the search picks p8 or the n32__2 fork latch on most seeds, P -2.5..-4.5 ns from
# norw1's 22.19 median; countloop: the fork latch n24__3, -3..-4 ns from 24.30; collatz: nothing or < 0.5 ns. Every draw
# passing.
set -uo pipefail
SPEC=(xorshift_1 xorshift_2 xorshift_3 xorshift_4 xorshift_5 xorshift_6 xorshift_8 collatz_2 collatz_3 collatz_4
      collatz_5 collatz_6 collatz_7 collatz_8 countloop_1 countloop_2 countloop_3 countloop_4)
KS=${SPEC[$((TASK - 1))]}; K=${KS%_*}; S=${KS##*_}
D=$PWD/research/data/suite/resume/norw1s/$KS
echo "nsearch1 kernel $K seed $S" > "$OUT/task.txt"
mkdir -p "$RUNS/state" && cp "$D"/* "$RUNS/state/"
ND=8; [ "$K" = countloop ] && ND=4
export CA_JOBS=2 DRAW_JOBS=3 PNR_TIMEOUT=3600 BDC_AUTO_REWRITES=0 AUTO_RESUME=$RUNS/state AUTO_SEARCH=1 \
       AUTO_SEARCH_MAXIT=4 AUTO_SEARCH_ARGS="--all-sites --buildable-only --wire 1000"
mkdir -p "$OUT/auto"
( while sleep 300; do cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$RUNS/auto/su_${K}_$S/"*.env "$OUT/auto/" 2>/dev/null; done ) & BG=$!
research/tools/suite/suite_one.sh "$K" "$S" $ND 4 > "$OUT/summary.txt" 2>&1
kill $BG 2>/dev/null
cp "$RUNS/suite/${K}_$S/"*.txt "$OUT/" 2>/dev/null
cp "$RUNS/auto/su_${K}_$S/"*.txt "$RUNS/auto/su_${K}_$S/"*.vh "$RUNS/auto/su_${K}_$S/"*.env "$OUT/auto/" 2>/dev/null
cp "$RUNS/r/su_${K}_${S}_"*/fid/equiv.txt "$OUT/" 2>/dev/null
cat "$OUT/result.txt" >> "$OUT/task.txt" 2>/dev/null
exit 0
