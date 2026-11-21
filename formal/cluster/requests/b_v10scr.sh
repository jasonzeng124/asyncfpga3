#!/bin/bash
#CLUSTER array=1-155 cores=2 mem=16G time=360
# b_v10scr (shard B, 2026-11-21): research FOR-FORMAL 04:00 #4 -- "is collatz64 one route or a pattern?": B24's steer
# screen on EVERY rule-CLEAN, PASS, EQUIVALENT, ffmux-clean route of flow v10 (all seeds; 155 routes, 90 of them memory kernels: shard C memtask decode + steersafe only;
# specs from formal/tools-B/auto/suite/mk_specs_all.py over claude/cluster results/suite13t_s5a_v10_*). Each task:
# research's board_rebuild.sh (sdf checked against the farm's), the trimmed bits, racescreen.sh (decode from the bits,
# 2 + 2 draws, steersafe --auto, ctlsweep, xtol at research's bands, outsafe), weaksweep.sh; dout 23 ns (CA_BENCHCAP).
# Untrusted simulation / extraction; bound logic in Lean (SteerSettle, SettleAll, ChainHold, CtlChain).
set -uo pipefail
NM=$(sed -n "${TASK}p" formal/tools-B/auto/suite/v10/list.txt); echo "$NM" > $OUT/task.txt
( cd $PEER && (git checkout -q c4fdc9d23 2>/dev/null || (git fetch -q origin c4fdc9d23 && git checkout -q c4fdc9d23)) ) >> $OUT/task.txt 2>&1
git -C $PEER log -1 --format='research %h' >> $OUT/task.txt 2>&1
mkdir -p $PEER/build/frontend; [ -d $PEER/build/frontend/collatz ] || cp -r $PEER/cloud/fixtures/frontend/* $PEER/build/frontend/
RS=$PEER JOBS=2 TMPDIR=$RUNS BQ_RUNS=$RUNS/bq bash formal/tools-B/auto/suite/v10screen.sh formal/tools-B/auto/suite/v10/$NM.spec $RUNS/o > $OUT/log.txt 2>&1
for f in screen.txt rebuild.txt steersafe.txt memtask.txt; do cp $RUNS/o/$f $OUT/ 2>/dev/null; done
cp $RUNS/o/mt/summary.txt $OUT/mt_summary.txt 2>/dev/null; cp $RUNS/o/rs/racescreen.txt $RUNS/o/rs/j/summary.txt $RUNS/o/rs/j/outsafe.txt $OUT/ 2>/dev/null
exit 0
