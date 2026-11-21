#!/bin/bash
#CLUSTER array=1-24 cores=4 mem=16G time=200
# Shard B (b_lsj): board item 39's automatic collatz sizes (research collatz_v3_s6_sizes.vh, odd tasks) vs the same with the
# operator lines shortened to formal's linescale STRICT joint result on item 39's own placement (tools-B/auto/sizes/
# collatz_v3_s6_lsj.vh: UCMPI0 13->7, UCMPI2 11->9, UADDI0 6->3, UADDI1 / UMUX0-2 / USELECT0 -> 0; even tasks), placer
# seeds 1-8 (task 2s-1 / 2s); tasks 17-24: the shortened sizes with UCMPI0 back at 13 (collatz_v3_s6_lsj_c0.vh), seeds 1-8
# (added 18:4x: the shortened seed-6 rebuild failed at its entry compare in the cloud). Per route (tools-B/auto/coltask.sh): col18 32 draws + 32 slow-carry draws with NEARMISS sums
# and last-answer means, c32hi, preloaded steps counter, carry slacks. Untrusted simulation; one A/B per seed.
set -uo pipefail
SEED=$(( (TASK + 1) / 2 )); V=$(( TASK % 2 ))
if [ $V = 1 ]; then Z=$PEER/research/data/suite/board/collatz_v3_s6_sizes.vh; else Z=formal/tools-B/auto/sizes/collatz_v3_s6_lsj.vh; fi
if [ $TASK -gt 16 ]; then SEED=$((TASK - 16)); Z=formal/tools-B/auto/sizes/collatz_v3_s6_lsj_c0.vh; fi
mkdir -p $PEER/build/frontend; [ -d $PEER/build/frontend/collatz ] || cp -r $PEER/cloud/fixtures/frontend/* $PEER/build/frontend/
RS=$PEER JOBS=4 TMPDIR=$RUNS bash formal/tools-B/auto/coltask.sh $Z $SEED $RUNS/o > $OUT/log.txt 2>&1
cp $RUNS/o/summary.txt $RUNS/o/draws_*.txt $OUT/ 2>/dev/null
exit 0
