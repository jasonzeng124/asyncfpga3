#!/bin/bash
#CLUSTER array=1-2 cores=2 mem=16G time=240
# b_hl3: divmodu / straight again after a third boundary fix (out0_data read straight off a CARRY4).
# b_hl3: b_hl1 rerun after two formal harness fixes (fold64 fed the low word twice; start_ack pass-through); see hl3_routes.txt.
# Shard B (b_hl3): research's headline (38 of 62 kernels pass, research/data/fifteen/README.md 2026-11-19) judged
# independently: one route per kernel (NOT CLEAN preferred) not covered by B8 / B11, plus two known-bad controls
# (if_loop_1 s1 b2ad5a7b, research's WRONG ANSWER; divmodu s1, a divider route the flow sized like test_divui's).
# Each: rebuilt from PEER with the route's own sizes_<it>.vh and seed, sdf md5 checked, bits read back and decoded by
# formal, 16 draws of research's model (research's suite K) + 16 slow-carry draws, research's C oracle. Memory-vector
# kernels print SKIP (formal's bench boundary has no RAM host yet). Untrusted simulation.
set -uo pipefail
L=$(sed -n "$((TASK + 1))p" formal/tools-B/auto/suite/hl3_routes.txt); set -- $L; K=$1; S=$2; Z=$3; M8=$4; ND=$5
echo "$L" > $OUT/task.txt
mkdir -p $PEER/build/frontend; [ -d $PEER/build/frontend/$K ] || cp -r $PEER/cloud/fixtures/frontend/* $PEER/build/frontend/
RS=$PEER JOBS=2 TMPDIR=$RUNS bash formal/tools-B/auto/suite/task.sh $K $S formal/tools-B/auto/suite/$Z $M8 $RUNS/o $ND > $OUT/log.txt 2>&1
cp $RUNS/o/summary.txt $RUNS/o/exp.txt $RUNS/o/draws_summary_*.txt $OUT/ 2>/dev/null
for f in $RUNS/o/d*.log; do tail -40 $f > $OUT/$(basename $f .log)_tail.txt; done 2>/dev/null
tail -30 $RUNS/o/build.log > $OUT/build_tail.txt 2>/dev/null
exit 0
