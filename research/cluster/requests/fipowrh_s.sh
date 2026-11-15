#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=60
# fipowrh_s: STATIC_ONLY rerun of fipowrh (same seeds = same routes): eval.txt's static line dropped every rule E row until 2026-11-15 (JOURNAL correction); report_rows_*.txt keeps every row now.
# fipowrh: every check + the trace-measured hold check at FAST_MIN (HOLD_VEC research/data/fifteen/vec_ipow_hold.hex, select-flipping sequence).
set -uo pipefail
export STATIC_ONLY=1 HOLD_VEC=research/data/fifteen/vec_ipow_hold.hex
research/tools/fifteen/eval_task.sh fipowrh_s_$TASK ipow research/data/ipow_dsp1_sizes_T9s75_bench.vh $TASK research/data/fifteen/vec_ipow.hex research/data/eventgraph/gate/ipow17.hex research/data/eventgraph/gate/ipow17.exp BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
