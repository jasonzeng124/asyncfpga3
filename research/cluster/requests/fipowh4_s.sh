#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=60
# fipowh4_s: STATIC_ONLY rerun of fipowh4 (same seeds = same routes): eval.txt's static line dropped every rule E row until 2026-11-15 (JOURNAL correction); report_rows_*.txt keeps every row now.
# fipowh4: round 4 of the rule H / I pads (hold_pads_eval.py over the previous round's 32 routes, 300 ps a link). Every check; report_hi_*.txt now returned.
set -uo pipefail
export STATIC_ONLY=1 HOLD_VEC=research/data/fifteen/vec_ipow_hold.hex
research/tools/fifteen/eval_task.sh fipowh4_s_$TASK ipow research/data/ipow_dsp1_sizes_T9s75_h4_bench.vh $TASK research/data/fifteen/vec_ipow.hex research/data/eventgraph/gate/ipow17.hex research/data/eventgraph/gate/ipow17.exp BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
