#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=90
# fcsel3p: collatz item 28 + the 32-route per-cell max of corner_audit proposals with the A' fix (nl6s3p: uselect0 16 -> 9, acks trimmed; uaddi0 12). Every check incl. hold_bits and TSE. Compare with fcsel3m seed by seed. The sized version of fcsel3a (one route's proposal).
set -uo pipefail
export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/collatz_preeq2.mlir HOLD_VEC=research/data/fifteen/vec_collatz_hold.hex TSE_VEC=research/data/fifteen/vec_collatz.hex
research/tools/fifteen/eval_task.sh fcsel3p_$TASK collatz research/data/collatz_sizes_T3cdb_nl6s3p_bench.vh $TASK research/data/fifteen/vec_collatz.hex research/data/eventgraph/gate/col13.hex research/data/eventgraph/gate/col13.exp BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
