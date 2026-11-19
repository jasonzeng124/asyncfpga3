#!/bin/bash
#CLUSTER array=1-3 cores=4 mem=16G time=180
# Shard B (b_muxn): research's muxsel finding (2026-11-19 05:47): bdc_muxnN's index-vs-ctl_req race at the decode LUTs, line
# shrunk to 1 on cmpchain s2 it5 (1c13ff02) / s3 it2 (1994ab81), runts on the decode outputs in research's GLS (draws 20001 /
# 20002), none with the line at 7 (a44b35aa). Formal's simx on the decoded bits, research's draws from K 20001 (8) + 8
# slow-carry: answers, NEARMISS on storage LUTs. Untrusted simulation.
set -uo pipefail
L=$(sed -n "$((TASK + 1))p" formal/tools-B/auto/suite/muxn_routes.txt); set -- $L; K=$1; S=$2; Z=$3; M8=$4; ND=$5; K0=$6
echo "$L" > $OUT/task.txt
mkdir -p $PEER/build/frontend; [ -d $PEER/build/frontend/$K ] || cp -r $PEER/cloud/fixtures/frontend/* $PEER/build/frontend/
RS=$PEER JOBS=4 TMPDIR=$RUNS bash formal/tools-B/auto/suite/task.sh $K $S formal/tools-B/auto/suite/$Z $M8 $RUNS/o $ND $K0 > $OUT/log.txt 2>&1
cp $RUNS/o/summary.txt $RUNS/o/exp.txt $RUNS/o/draws_summary_*.txt $OUT/ 2>/dev/null
for f in $RUNS/o/d*.log; do tail -40 $f > $OUT/$(basename $f .log)_tail.txt; done 2>/dev/null
tail -30 $RUNS/o/build.log > $OUT/build_tail.txt 2>/dev/null
exit 0
