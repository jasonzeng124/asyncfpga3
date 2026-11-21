#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=90
# fc64sel3o: fc64sel3n + UMUX2 1 -> 6 (h4s3o: the result mux's A' miss from its data links, off the loop). Every check incl. rule M. The collatz64 candidate if every static row is clean.
set -uo pipefail
export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/collatz64_preeq2.mlir HOLD_VEC=research/data/fifteen/vec_collatz_hold.hex TSE_VEC=research/data/fifteen/vec_collatz.hex
research/tools/fifteen/eval_task.sh fc64sel3o_$TASK collatz64 research/data/collatz64_sizes_T4cdb_h4s3o_bench.vh $TASK research/data/fifteen/vec_collatz.hex research/data/eventgraph/gate/c6414.hex research/data/eventgraph/gate/c6414.exp BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
