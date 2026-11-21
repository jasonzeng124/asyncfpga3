#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=90
# fisel3m: ipow item 29 (h4s3) with the mux delays sized by rule M / A' (h4s3m: umux0 6, umux1 8, umux2 7, umux3 4). Every check incl. rule M. Compare with fisel3 seed by seed.
set -uo pipefail
export HOLD_VEC=research/data/fifteen/vec_ipow_hold.hex TSE_VEC=research/data/fifteen/vec_ipow.hex
research/tools/fifteen/eval_task.sh fisel3m_$TASK ipow research/data/ipow_dsp1_sizes_T9s75_h4s3m_bench.vh $TASK research/data/fifteen/vec_ipow.hex research/data/eventgraph/gate/ipow17.hex research/data/eventgraph/gate/ipow17.exp BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
