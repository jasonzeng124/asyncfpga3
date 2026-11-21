#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=90
# fcsel3m_la: collatz item 28 (fcsel3m sizes and seeds): every delay line on the loop, line_account.py at worst and nominal (PROGRAM second lead, on the current candidate). Static + TSE as well.
set -uo pipefail
export STATIC_ONLY=1 LINE_ACCT=1 TSE_VEC=research/data/fifteen/vec_collatz.hex BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/collatz_preeq2.mlir
research/tools/fifteen/eval_task.sh fcsel3m_la_$TASK collatz research/data/collatz_sizes_T3cdb_nl6s3m_bench.vh $TASK research/data/fifteen/vec_collatz.hex research/data/eventgraph/gate/col13.hex research/data/eventgraph/gate/col13.exp BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
