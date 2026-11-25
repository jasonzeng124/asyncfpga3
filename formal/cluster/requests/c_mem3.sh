#!/bin/bash
#CLUSTER array=1-7 cores=4 mem=16G time=180
# Shard C (c_mem3): c_mem2 rows that needed the void-kernel bench (bench completion join as out0) and boundary fixes: formal's simx with RAMB18E1 decoded from the bits (margin/bram/).
# research's headline memory routes (BDC_AUTO=1, the farm's sizes, sdf md5 checked), 16 draws of research's model + 16
# slow cell/RAM draws each, fills / read-back of every array per call against the C (oracle_mem.sh). Tasks 18-19: the
# capture latch removed (BDC_MEM_NOCAP=1, research's own negative control) on two arbitrated-port kernels: must fail.
# The host's port is not simulated (fills written into the RAMs directly). Untrusted simulation.
set -uo pipefail
L=$(sed -n "$((TASK + 1))p" formal/tools/margin/bram/routes_mem3.txt); set -- $L; K=$1; S=$2; Z=$3; M8=$4; ND=$5; shift 5
echo "$L" > $OUT/task.txt
for e in "$@"; do export "$e"; done
RS=$PEER JOBS=4 TREE=$RUNS/tree bash formal/tools/margin/bram/memtask.sh $K $S $Z $M8 $RUNS/o $ND > $OUT/log.txt 2>&1
cp $RUNS/o/summary.txt $RUNS/o/draws_summary_*.txt $RUNS/o/v/exp.txt $OUT/ 2>/dev/null
for f in $RUNS/o/draws_1*.txt; do cut -c1-600 $f > $OUT/$(basename $f); done 2>/dev/null
tail -30 $RUNS/o/build.log > $OUT/build_tail.txt 2>/dev/null; tail -20 $RUNS/o/decode.out > $OUT/decode_tail.txt 2>/dev/null
exit 0
