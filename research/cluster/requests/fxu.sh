#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=90
# fxu: item 27 (fr4) + the missing ack macro ULINK_N7F__1_UACK at 1 (RTL default 6 before; on the critical cycle's fall, rule H margin +3.8 ns at worst on seed 2). Every check incl. hold_bits and TSE (the hold side is what this line is for). Compare latency with fxd seed by seed.
set -uo pipefail
export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/xorshift_predec.mlir HOLD_VEC=research/data/fifteen/vec_xorshift_hold.hex TSE_VEC=research/data/fifteen/vec_xorshift.hex
research/tools/fifteen/eval_task.sh fxu_$TASK xorshift research/data/xorshift_sizes_T3s50_fr4u_bench.vh $TASK research/data/fifteen/vec_xorshift.hex research/data/eventgraph/gate/xor17.hex research/data/eventgraph/gate/xor17.exp BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
