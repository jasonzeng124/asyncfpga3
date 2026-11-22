#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=240
# fc64h: sizes collatz64_sizes_T4cdb_h_bench (the rule H / I pads, hold_pads.py) -- every check (eval.txt now lists H / I rows below 0) + the trace-measured hold check at FAST_MIN (HOLD_VEC research/data/fifteen/vec_collatz_hold.hex, select-flipping sequence).
set -uo pipefail
export HOLD_VEC=research/data/fifteen/vec_collatz_hold.hex
research/tools/fifteen/eval_task.sh fc64h_$TASK collatz64 research/data/collatz64_sizes_T4cdb_h_bench.vh $TASK research/data/fifteen/vec_collatz.hex research/data/eventgraph/gate/c6414.hex research/data/eventgraph/gate/c6414.exp BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_NO_LINK=ulink_n30__1 > "$OUT/log_eval.txt" 2>&1
