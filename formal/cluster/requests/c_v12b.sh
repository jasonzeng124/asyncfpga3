#!/bin/bash
#CLUSTER array=1-56 cores=4 mem=16G time=240
# Shard C (c_v12b, replaces c_v12a before it started): formal's board approximator on every flow-v12 spec shard B wrote
# (tools-B/auto/suite/v12, mk_specs_all.py --stagefix), rebuilt by research's board_rebuild.sh (sdf checked, trimmed fasm
# md5 reported): 32 + 32 draws of research's model, then the scatter stress test of C76 (per-arc sigma x3 / x4 / x5, 32
# draws each). Untrusted simulation.
set -uo pipefail
SP=$(sed -n "${TASK}p" formal/tools/margin/spec/specs_v12b.txt)
echo "$SP" > $OUT/task.txt
SWEEP="0.378 0.504 0.630" SWEEPN=32 RS=$PEER JOBS=4 bash formal/tools/margin/spec/drawspec.sh "$SP" $RUNS/o 32 > $OUT/log.txt 2>&1
cp $RUNS/o/summary.txt $RUNS/o/line.txt $RUNS/o/rebuild.txt $OUT/ 2>/dev/null
cp $RUNS/o/t/draws_summary_*.txt $RUNS/o/mt/draws_summary_*.txt $OUT/ 2>/dev/null
for f in $RUNS/o/sweep_draws_*.txt; do [ -f "$f" ] && cut -c1-600 "$f" > $OUT/$(basename $f); done
tail -40 $RUNS/o/task.log > $OUT/task_tail.txt 2>/dev/null; tail -30 $RUNS/o/memtask.log > $OUT/memtask_tail.txt 2>/dev/null
exit 0
