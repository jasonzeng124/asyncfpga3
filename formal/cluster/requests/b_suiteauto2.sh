#!/bin/bash
#CLUSTER array=1-16 cores=4 mem=16G time=240
# Shard B (b_suiteauto2; b_suiteauto was rejected for time=300): research's automatic suite routes (farm suite3a / 3b / 7: BDC_AUTO=1, the sizing loop's sizes for
# the route it judged; 11 of 16 NOT CLEAN by research's own rule, judged on 4 draws) rebuilt from PEER, sdf md5 checked
# against research's, the bits read back and decoded by formal, then 32 draws of research's model + 32 slow-carry draws
# (CARRY4 / F7F8 / FF 0.8-1.0, B7's failure mode) on the kernel's own vectors with research's C-derived oracle.
# tools-B/auto/suite/routes.txt line TASK+1 (line 1, countloop 1, ran in the cloud: 32 + 32 PASS). Untrusted simulation.
set -uo pipefail
L=$(sed -n "$((TASK + 1))p" formal/tools-B/auto/suite/routes.txt); set -- $L; K=$1; S=$2; Z=$3; M8=$4
echo "$L" > $OUT/task.txt
mkdir -p $PEER/build/frontend; [ -d $PEER/build/frontend/$K ] || cp -r $PEER/cloud/fixtures/frontend/* $PEER/build/frontend/
RS=$PEER JOBS=4 TMPDIR=$RUNS bash formal/tools-B/auto/suite/task.sh $K $S formal/tools-B/auto/suite/$Z $M8 $RUNS/o 32 > $OUT/log.txt 2>&1
cp $RUNS/o/summary.txt $RUNS/o/exp.txt $RUNS/o/draws_summary_*.txt $OUT/ 2>/dev/null
tail -30 $RUNS/o/build.log > $OUT/build_tail.txt 2>/dev/null
exit 0
