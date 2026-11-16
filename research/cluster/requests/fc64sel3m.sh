#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=90
# fc64sel3m: fc64sel3q with umux0 padded to rule M's need (h4s3m: UMUX0 2 -> 16, the 32-route max of the A'm proposal). Every check (rule M included). Compare with fc64sel3q seed by seed: the cost of the mux data contract.
set -uo pipefail
export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/collatz64_preeq2.mlir HOLD_VEC=research/data/fifteen/vec_collatz_hold.hex TSE_VEC=research/data/fifteen/vec_collatz.hex
research/tools/fifteen/eval_task.sh fc64sel3m_$TASK collatz64 research/data/collatz64_sizes_T4cdb_h4s3m_bench.vh $TASK research/data/fifteen/vec_collatz.hex research/data/eventgraph/gate/c6414.hex research/data/eventgraph/gate/c6414.exp BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
