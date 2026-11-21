#!/bin/bash
#CLUSTER array=1-4 cores=2 mem=16G time=240
# b_hl5: suite10b's four new non-array routes (nested s1, fold64 s1, iterative_division s1, quadrec s3): 16 + 16 draws + outsafe.py.
# rebuild (sdf checked), decode from the bits, 1 + 1 draws (sanity), then tools-B/auto/outsafe.py (Lean SettleAll +
# ChainHold logic; untrusted extraction). Lines from tools-B/auto/suite/hl5_routes.txt.
set -uo pipefail
L=$(sed -n "$((TASK + 1))p" formal/tools-B/auto/suite/hl5_routes.txt); set -- $L; K=$1; S=$2; Z=$3; M8=$4; ND=$5
echo "$L" > $OUT/task.txt
mkdir -p $PEER/build/frontend; [ -d $PEER/build/frontend/$K ] || cp -r $PEER/cloud/fixtures/frontend/* $PEER/build/frontend/
RS=$PEER JOBS=2 TMPDIR=$RUNS bash formal/tools-B/auto/suite/task.sh $K $S formal/tools-B/auto/suite/$Z $M8 $RUNS/o $ND > $OUT/log.txt 2>&1
cp $RUNS/o/summary.txt $RUNS/o/draws_summary_*.txt $OUT/ 2>/dev/null
[ -f $RUNS/o/w/m/net.json ] && timeout 3000 python3 formal/tools-B/auto/outsafe.py $RUNS/o/w/m > $OUT/outsafe.txt 2>&1
exit 0
