#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=240
# fxf3: fxf2 + a latch on the adder fork's steer branch (BDC_FORK_OUT_LINK=n11__0,n30__0): fxf2 seed 1 failed FAST_MIN on
# an unaudited hold race (counter loop-back pipe fed by the adder through a steer, JOURNAL 2026-11-14). Every check.
set -uo pipefail
research/tools/fifteen/eval_task.sh fxf3_$TASK xorshift research/data/xorshift_sizes_T3s50_fr2_bench.vh $TASK research/data/fifteen/vec_xorshift.hex research/data/eventgraph/gate/xor17.hex research/data/eventgraph/gate/xor17.exp BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0,n30__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
