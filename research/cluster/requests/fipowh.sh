#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=240
# fipowh: sizes ipow_dsp1_sizes_T9s75_h_bench (the rule H / I pads, hold_pads.py) -- every check (eval.txt now lists H / I rows below 0) + the trace-measured hold check at FAST_MIN (HOLD_VEC research/data/fifteen/vec_ipow_hold.hex, select-flipping sequence).
set -uo pipefail
export HOLD_VEC=research/data/fifteen/vec_ipow_hold.hex
research/tools/fifteen/eval_task.sh fipowh_$TASK ipow research/data/ipow_dsp1_sizes_T9s75_h_bench.vh $TASK research/data/fifteen/vec_ipow.hex research/data/eventgraph/gate/ipow17.hex research/data/eventgraph/gate/ipow17.exp BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
