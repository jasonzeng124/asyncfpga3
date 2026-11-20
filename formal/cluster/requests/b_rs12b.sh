#!/bin/bash
#CLUSTER array=1-23 cores=2 mem=16G time=240
# b_rs12b: RERUN of b_rs12 with steersafe.py fixed (B27: compare-with-join bounds were unsound); the steer races (FOR-RESEARCH B20-B24) on research's suite12 routes (flow v8, seed 1; formal judged their draws
# as B19): rebuild at research 1b47b72a7 (sdf checked against the farm's), decode from the bits, 1 + 1 draws (sanity),
# then tools-B/auto/steersafe.py --auto (every steer's structural kappa_lo), ctlsweep.sh (B21's latch-fed race under its
# race-only adversary), trim/xtol.sh (the weakest steer's opposite-path-error tolerance at research's bands).
# Lines from tools-B/auto/suite/rs12_routes.txt. Untrusted simulation / extraction; bound logic in Lean.
set -uo pipefail
L=$(sed -n "$((TASK + 1))p" formal/tools-B/auto/suite/rs12_routes.txt); set -- $L; K=$1; S=$2; Z=$3; M8=$4; shift 4; EV="$*"
echo "$L" > $OUT/task.txt
( cd $PEER && git checkout -q 1b47b72a7 2>/dev/null || git fetch -q origin 1b47b72a7 && git checkout -q 1b47b72a7 ) >> $OUT/task.txt 2>&1
git -C $PEER log -1 --format='research %h' >> $OUT/task.txt 2>&1
mkdir -p $PEER/build/frontend; [ -d $PEER/build/frontend/$K ] || cp -r $PEER/cloud/fixtures/frontend/* $PEER/build/frontend/
env $EV RS=$PEER JOBS=2 TMPDIR=$RUNS bash formal/tools-B/auto/suite/task.sh $K $S formal/tools-B/auto/suite/$Z $M8 $RUNS/o 1 > $OUT/log.txt 2>&1
cp $RUNS/o/summary.txt $OUT/ 2>/dev/null
if [ -f $RUNS/o/w/m/net.json ]; then
  timeout 3000 python3 formal/tools-B/auto/steersafe.py $RUNS/o/w/m --auto > $RUNS/o/steersafe.txt 2>&1; cp $RUNS/o/steersafe.txt $OUT/

  bash formal/tools-B/auto/ensure_m.sh $RUNS/o > /dev/null 2>&1; timeout 5000 bash formal/tools-B/auto/weaksweep.sh $RUNS/o $K > $OUT/weaksweep.txt 2>&1
fi
exit 0
