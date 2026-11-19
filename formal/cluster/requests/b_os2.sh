#!/bin/bash
#CLUSTER array=1-38 cores=2 mem=16G time=120
# b_os2: b_os1 again with outsafe.py fixed (constant pins, a mux uor with the other joins at 0 as premises, the worst launching join).
# Shard B (b_os2): the output-capture race's proved-structure lower bound (kappa_lo) on every non-array headline route:
# rebuild (sdf checked), decode from the bits, 1 + 1 draws (sanity), then tools-B/auto/outsafe.py (Lean SettleAll +
# ChainHold logic; untrusted extraction). Lines from tools-B/auto/suite/os_routes.txt.
set -uo pipefail
L=$(sed -n "$((TASK + 1))p" formal/tools-B/auto/suite/os_routes.txt); set -- $L; K=$1; S=$2; Z=$3; M8=$4; ND=$5
echo "$L" > $OUT/task.txt
mkdir -p $PEER/build/frontend; [ -d $PEER/build/frontend/$K ] || cp -r $PEER/cloud/fixtures/frontend/* $PEER/build/frontend/
RS=$PEER JOBS=2 TMPDIR=$RUNS bash formal/tools-B/auto/suite/task.sh $K $S formal/tools-B/auto/suite/$Z $M8 $RUNS/o $ND > $OUT/log.txt 2>&1
cp $RUNS/o/summary.txt $OUT/ 2>/dev/null
[ -f $RUNS/o/w/m/net.json ] && timeout 3000 python3 formal/tools-B/auto/outsafe.py $RUNS/o/w/m > $OUT/outsafe.txt 2>&1
exit 0
