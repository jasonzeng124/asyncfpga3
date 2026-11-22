#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=240
# fxl5s: fxs5 (fr4 pads + speculative uaddi0) + lever 5 (BDC_NO_LINK=ulink_n30__1), static check with C-element joins (BD_SKEW_AND_JOIN=1, skew.py c26f1566). Compare latency with fxs5 seed by seed. Local seed 10 without the cell: 24.00 ns vs xf5_10 23.15 (ufork8 re-couples to ulink_n7).
set -uo pipefail
export BD_SKEW_AND_JOIN=1
export HOLD_VEC=research/data/fifteen/vec_xorshift_hold.hex SPEC_CASES=uaddi0:4
research/tools/fifteen/eval_task.sh fxl5s_$TASK xorshift research/data/xorshift_sizes_T3s50_fr4_bench.vh $TASK research/data/fifteen/vec_xorshift.hex research/data/eventgraph/gate/xor17.hex research/data/eventgraph/gate/xor17.exp BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0,n30__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_SPEC_INC=uaddi0:4:6 BDC_NO_LINK=ulink_n30__1 > "$OUT/log_eval.txt" 2>&1
