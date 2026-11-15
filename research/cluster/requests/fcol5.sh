#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=240
# fcol5: round 3 of the rule H / I pads (hold_pads_eval.py over the previous round's 32 routes, 300 ps a link). Every check; report_hi_*.txt now returned.
set -uo pipefail
export HOLD_VEC=research/data/fifteen/vec_collatz_hold.hex
research/tools/fifteen/eval_task.sh fcol5_$TASK collatz research/data/collatz_sizes_T3cdb_nl5_bench.vh $TASK research/data/fifteen/vec_collatz.hex research/data/eventgraph/gate/col13.hex research/data/eventgraph/gate/col13.exp BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_NO_LINK=ulink_n28__1 > "$OUT/log_eval.txt" 2>&1
