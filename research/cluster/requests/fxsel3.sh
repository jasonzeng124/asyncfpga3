#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=90
# fxsel3: item 27's structure (xorshift lever 8, pre_dec), sizes fr4s3 = fr4 with the four select links at 3 (sized by
# rule E: at 1 E failed to -638 ps on 22/32 routes, fxsel1_s). Every check incl. hold_bits and TSE. Compare latency with fxd seed by seed.
# Submitted 2026-11-16. time = ~2-3x a task.
set -uo pipefail
export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/xorshift_predec.mlir HOLD_VEC=research/data/fifteen/vec_xorshift_hold.hex TSE_VEC=research/data/fifteen/vec_xorshift.hex
research/tools/fifteen/eval_task.sh fxsel3_$TASK xorshift research/data/xorshift_sizes_T3s50_fr4s3_bench.vh $TASK research/data/fifteen/vec_xorshift.hex research/data/eventgraph/gate/xor17.hex research/data/eventgraph/gate/xor17.exp BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
