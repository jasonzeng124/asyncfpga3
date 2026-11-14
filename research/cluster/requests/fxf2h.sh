#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=240
# fxf2h: every check plus the trace-measured hold check at FAST_MIN (hold_trace.py, HOLD_VEC = rounds 3, 4, 8, 5 in
# sequence -- the failing pattern of fxf2 seed 1). BDC_FORK_OUT_LINK=n11__0. Expect fxf2h seed 1 to flag
# ulink_n_trueResult_6 (-1850 ps locally).
set -uo pipefail
export HOLD_VEC=research/data/fifteen/vec_xorshift_hold.hex
research/tools/fifteen/eval_task.sh fxf2h_$TASK xorshift research/data/xorshift_sizes_T3s50_fr2_bench.vh $TASK research/data/fifteen/vec_xorshift.hex research/data/eventgraph/gate/xor17.hex research/data/eventgraph/gate/xor17.exp BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
