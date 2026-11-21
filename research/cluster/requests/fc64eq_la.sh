#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=90
# fc64eq_la: collatz64 item 26 (fc64eq: pre_eq2, h2 sizes, same seeds): every delay line on the loop, line_account.py at worst and nominal (PROGRAM second lead: collatz64). Static + TSE as well.
set -uo pipefail
export STATIC_ONLY=1 LINE_ACCT=1 TSE_VEC=research/data/fifteen/vec_collatz.hex BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/collatz64_preeq2.mlir
research/tools/fifteen/eval_task.sh fc64eq_la_$TASK collatz64 research/data/collatz64_sizes_T4cdb_h2_bench.vh $TASK research/data/fifteen/vec_collatz.hex research/data/eventgraph/gate/c6414.hex research/data/eventgraph/gate/c6414.exp BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
