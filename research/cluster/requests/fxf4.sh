#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=240
# fxf4: xf3 (latch on the adder's steer branch) + umux2 2 (fr3 sizes). Every check + the hold check at FAST_MIN.
set -uo pipefail
export HOLD_VEC=research/data/fifteen/vec_xorshift_hold.hex
research/tools/fifteen/eval_task.sh fxf4_$TASK xorshift research/data/xorshift_sizes_T3s50_fr3_bench.vh $TASK research/data/fifteen/vec_xorshift.hex research/data/eventgraph/gate/xor17.hex research/data/eventgraph/gate/xor17.exp BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0,n30__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
