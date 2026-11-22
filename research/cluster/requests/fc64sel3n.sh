#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=90
# fc64sel3n: collatz64 h4s3q with rule M's umux0 miss fixed per launch (h4s3n: UMUX0 4, entry link ULINK_N_FALSERESULT_3 DELAY 4). Every check incl. rule M. Compare with fc64sel3q and fc64sel3m (UMUX0 16) seed by seed.
set -uo pipefail
export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/collatz64_preeq2.mlir HOLD_VEC=research/data/fifteen/vec_collatz_hold.hex TSE_VEC=research/data/fifteen/vec_collatz.hex
research/tools/fifteen/eval_task.sh fc64sel3n_$TASK collatz64 research/data/collatz64_sizes_T4cdb_h4s3n_bench.vh $TASK research/data/fifteen/vec_collatz.hex research/data/eventgraph/gate/c6414.hex research/data/eventgraph/gate/c6414.exp BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
