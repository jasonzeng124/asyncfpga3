#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=90
# fcsel3b: item 31 (nl6s3a) + mux delays sized by rule M and two datapath lines (nl6s3b: umux1 3, umux2 6, uselect0 6, ucmpi2 15; see the file's first line). Every check. Compare with fcsel3a seed by seed.
set -uo pipefail
export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/collatz_preeq2.mlir HOLD_VEC=research/data/fifteen/vec_collatz_hold.hex TSE_VEC=research/data/fifteen/vec_collatz.hex
research/tools/fifteen/eval_task.sh fcsel3b_$TASK collatz research/data/collatz_sizes_T3cdb_nl6s3b_bench.vh $TASK research/data/fifteen/vec_collatz.hex research/data/eventgraph/gate/col13.hex research/data/eventgraph/gate/col13.exp BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
