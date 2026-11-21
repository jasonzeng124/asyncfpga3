#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=240
# fc64eq2: fc64eq with sizes h3 (umux0 1 -> 2, ucmpi2 14 -> 15, falseResult_9 pads from fc64eq): the four routes with small rule A rows and one hold row.
set -uo pipefail
export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/collatz64_preeq2.mlir
export HOLD_VEC=research/data/fifteen/vec_collatz_hold.hex
research/tools/fifteen/eval_task.sh fc64eq2_$TASK collatz64 research/data/collatz64_sizes_T4cdb_h3_bench.vh $TASK research/data/fifteen/vec_collatz.hex research/data/eventgraph/gate/c6414.hex research/data/eventgraph/gate/c6414.exp BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
