#!/bin/bash
#CLUSTER array=1-21 cores=4 mem=16G time=240
# Shard C (c_v13a): formal's board approximator on research's flow v13 (AUTO_RACE_KAPPA) seed-2 routes, specs made here
# with B's mk_specs_all.py --mem --stagefix from farm suite13t_s5a_v13_2a (formal/tools/margin/spec/v13): research's
# board_rebuild.sh (sdf checked), 32 + 32 draws of research's model, then the scatter stress test (x3 / x4 / x5, 32 draws
# each). Untrusted simulation.
set -uo pipefail
SP=$(sed -n "${TASK}p" formal/tools/margin/spec/specs_v13a.txt)
echo "$SP" > $OUT/task.txt
SWEEP="0.378 0.504 0.630" SWEEPN=32 RS=$PEER JOBS=4 bash formal/tools/margin/spec/drawspec.sh "$SP" $RUNS/o 32 > $OUT/log.txt 2>&1
cp $RUNS/o/summary.txt $RUNS/o/line.txt $RUNS/o/rebuild.txt $OUT/ 2>/dev/null
cp $RUNS/o/t/draws_summary_*.txt $RUNS/o/mt/draws_summary_*.txt $OUT/ 2>/dev/null
for f in $RUNS/o/sweep_draws_*.txt; do [ -f "$f" ] && cut -c1-600 "$f" > $OUT/$(basename $f); done
tail -40 $RUNS/o/task.log > $OUT/task_tail.txt 2>/dev/null; tail -30 $RUNS/o/memtask.log > $OUT/memtask_tail.txt 2>/dev/null
exit 0
