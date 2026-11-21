#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=90
# fc64sel3q: fc64sel3p with ULINK_N28_UACK restored to 3 (TSE hold rows at ulink_n28 on 9/30 routes of fc64sel3p). Every check. Compare with fc64sel3p seed by seed.
set -uo pipefail
export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/collatz64_preeq2.mlir HOLD_VEC=research/data/fifteen/vec_collatz_hold.hex TSE_VEC=research/data/fifteen/vec_collatz.hex
research/tools/fifteen/eval_task.sh fc64sel3q_$TASK collatz64 research/data/collatz64_sizes_T4cdb_h4s3q_bench.vh $TASK research/data/fifteen/vec_collatz.hex research/data/eventgraph/gate/c6414.hex research/data/eventgraph/gate/c6414.exp BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
