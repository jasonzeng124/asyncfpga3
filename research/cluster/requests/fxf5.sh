#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=240
# fxf5: item 23 (xf4) with sizes fr4 = fr3 + the rule H / I pads (hold_pads.py). Every check; eval.txt's static lines now
# list rule H / I / F rows below 0 ("hold/close"), which no earlier farm summary showed. Compare with fxf4 / fxf4l.
set -uo pipefail
export HOLD_VEC=research/data/fifteen/vec_xorshift_hold.hex
research/tools/fifteen/eval_task.sh fxf5_$TASK xorshift research/data/xorshift_sizes_T3s50_fr4_bench.vh $TASK research/data/fifteen/vec_xorshift.hex research/data/eventgraph/gate/xor17.hex research/data/eventgraph/gate/xor17.exp BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0,n30__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
