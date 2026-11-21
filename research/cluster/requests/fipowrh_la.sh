#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=90
# fipowrh_la: ipow item 19 (T9s75 sizes, same seeds as fipowrh): every delay line on the loop, line_account.py at worst and nominal (PROGRAM second lead: ipow). Static + TSE as well.
set -uo pipefail
export STATIC_ONLY=1 LINE_ACCT=1 TSE_VEC=research/data/fifteen/vec_ipow.hex
research/tools/fifteen/eval_task.sh fipowrh_la_$TASK ipow research/data/ipow_dsp1_sizes_T9s75_bench.vh $TASK research/data/fifteen/vec_ipow.hex research/data/eventgraph/gate/ipow17.hex research/data/eventgraph/gate/ipow17.exp BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
