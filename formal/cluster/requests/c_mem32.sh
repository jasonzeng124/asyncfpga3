#!/bin/bash
#CLUSTER array=1-18 cores=2 mem=16G time=240
# Shard C (c_mem32): 18 memory routes (suite12 image_resize / share_test_1 / stencil_2d 1; capfix1 mul_example, test_memory_1/2,
# test_stdint, test_bool_array 4; all flow v8, fused), host port, 16 + 16 draws, hostrace. Untrusted simulation.
set -uo pipefail
L=$(sed -n "$((TASK + 1))p" formal/tools/margin/bram/routes_mem32.txt | sed 's/ *#.*//'); set -- $L; K=$1; S=$2; Z=$3; M8=$4; ND=$5; shift 5
echo "$L" > $OUT/task.txt
for e in "$@"; do export "$e"; done
RS=$PEER JOBS=2 TREE=$RUNS/tree bash formal/tools/margin/bram/memtask.sh $K $S $Z $M8 $RUNS/o $ND > $OUT/log.txt 2>&1
cp $RUNS/o/summary.txt $RUNS/o/draws_summary_*.txt $RUNS/o/v/exp.txt $OUT/ 2>/dev/null
for f in $RUNS/o/draws_1*.txt; do cut -c1-600 $f > $OUT/$(basename $f); done 2>/dev/null
tail -30 $RUNS/o/build.log > $OUT/build_tail.txt 2>/dev/null; tail -20 $RUNS/o/decode.out > $OUT/decode_tail.txt 2>/dev/null
exit 0
