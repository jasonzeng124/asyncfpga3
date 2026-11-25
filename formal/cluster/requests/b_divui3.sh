#!/bin/bash
#CLUSTER array=1-12 cores=4 mem=16G time=240
# b_divui3: UDIVUI0 272 / 288 / 320 / 384 on seeds 1-3 (b_divui2: 16-128 fail every draw, 528 passes; same-placement edge 268).
# Shard B (b_divui3; b_divui decoded nothing: the boundary missed test_divui's pass-through start_ack, fixed in tools-B/auto/boundary_bench.py): research's 2026-11-19 06:54 finding -- the automatic flow (suite10b) shrank test_divui's divider line
# UDIVUI0 to 5 / 6 on rule-CLEAN routes and every research draw fails. Tasks 1-2: those two routes rebuilt from PEER
# (sdf md5 checked), bits read back and decoded by formal, 32 draws of research's model (same K) + 32 slow-carry draws,
# research's C oracle. Tasks 3-8: what-if rebuilds with UDIVUI0 at 16 / 32 / 64 / 128 / 528 (seed 1) and 64 (seed 2),
# 16 + 16 draws: how long the line must be in formal's simx. Untrusted simulation.
set -uo pipefail
L=$(sed -n "$((TASK + 1))p" formal/tools-B/auto/suite/divui3_routes.txt); set -- $L; K=$1; S=$2; Z=$3; M8=$4; ND=$5
echo "$L" > $OUT/task.txt
mkdir -p $PEER/build/frontend; [ -d $PEER/build/frontend/$K ] || cp -r $PEER/cloud/fixtures/frontend/* $PEER/build/frontend/
RS=$PEER JOBS=4 TMPDIR=$RUNS bash formal/tools-B/auto/suite/task.sh $K $S formal/tools-B/auto/suite/$Z $M8 $RUNS/o $ND > $OUT/log.txt 2>&1
cp $RUNS/o/summary.txt $RUNS/o/exp.txt $RUNS/o/draws_summary_*.txt $OUT/ 2>/dev/null
for f in $RUNS/o/d*.log; do tail -40 $f > $OUT/$(basename $f .log)_tail.txt; done 2>/dev/null
tail -30 $RUNS/o/build.log > $OUT/build_tail.txt 2>/dev/null
exit 0
