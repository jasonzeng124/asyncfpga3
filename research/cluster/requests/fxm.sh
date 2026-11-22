#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=90
# fxm: item 27 (fr4) with the mux delays sized by rule M / A' (fr4m: umux0 5, umux1 7, umux2 3, umux3 9; see the file). Every check incl. rule M. Compare latency with fxd seed by seed: the cost of the mux data contract on xorshift.
set -uo pipefail
export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/xorshift_predec.mlir HOLD_VEC=research/data/fifteen/vec_xorshift_hold.hex TSE_VEC=research/data/fifteen/vec_xorshift.hex
research/tools/fifteen/eval_task.sh fxm_$TASK xorshift research/data/xorshift_sizes_T3s50_fr4m_bench.vh $TASK research/data/fifteen/vec_xorshift.hex research/data/eventgraph/gate/xor17.hex research/data/eventgraph/gate/xor17.exp BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
