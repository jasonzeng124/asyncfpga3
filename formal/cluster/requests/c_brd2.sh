#!/bin/bash
#CLUSTER array=1-10 cores=4 mem=16G time=240
# Shard C (c_brd2): formal's board approximator (simx on the bits, research's draw model, 64 + 64 slow-carry draws) on
# research's board items 42 / 43 / 45 (guarded + unguarded partners) / 46 (race pair), each rebuilt by research's own
# board_rebuild.sh from its spec (sdf and trimmed fasm checked). Untrusted simulation.
set -uo pipefail
SP=$(sed -n "${TASK}p" formal/tools/margin/spec/specs_brd1.txt)
echo "$SP" > $OUT/task.txt
RS=$PEER JOBS=4 bash formal/tools/margin/spec/drawspec.sh "$SP" $RUNS/o 64 > $OUT/log.txt 2>&1
cp $RUNS/o/summary.txt $RUNS/o/line.txt $RUNS/o/rebuild.txt $OUT/ 2>/dev/null
cp $RUNS/o/t/draws_summary_*.txt $RUNS/o/mt/draws_summary_*.txt $OUT/ 2>/dev/null
for f in $RUNS/o/t/d1*.log $RUNS/o/mt/draws_1*.txt; do [ -f "$f" ] && cut -c1-600 "$f" > $OUT/$(basename $f); done
tail -40 $RUNS/o/task.log > $OUT/task_tail.txt 2>/dev/null; tail -30 $RUNS/o/memtask.log > $OUT/memtask_tail.txt 2>/dev/null
exit 0
