#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=240
# fxd4: lever 8, sizes fr7d = fr6d + uxori1 7 -> 8 (fxd3 seed 22 A -240 at worst).
set -uo pipefail
export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/xorshift_predec.mlir HOLD_VEC=research/data/fifteen/vec_xorshift_hold.hex
research/tools/fifteen/eval_task.sh fxd4_$TASK xorshift research/data/xorshift_sizes_T3s50_fr7d_bench.vh $TASK research/data/fifteen/vec_xorshift.hex research/data/eventgraph/gate/xor17.hex research/data/eventgraph/gate/xor17.exp BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
