#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=240
# fipowh3: round 3 of the rule H / I pads (hold_pads_eval.py over the previous round's 32 routes, 300 ps a link). Every check; report_hi_*.txt now returned.
set -uo pipefail
export HOLD_VEC=research/data/fifteen/vec_ipow_hold.hex
research/tools/fifteen/eval_task.sh fipowh3_$TASK ipow research/data/ipow_dsp1_sizes_T9s75_h3_bench.vh $TASK research/data/fifteen/vec_ipow.hex research/data/eventgraph/gate/ipow17.hex research/data/eventgraph/gate/ipow17.exp BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
