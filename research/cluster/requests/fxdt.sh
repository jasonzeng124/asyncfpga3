#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=60
# fxdt: item 27's structure (xorshift lever 8, pre_dec), sizes fr4, every check of fxd plus step 5 (TSE_VEC: rule H with
# C-element semantics and token counts, tsehold.py, both corners). fr4 = fxd's sizes: TSE status of item 27 on 32 routes.
# Submitted 2026-11-15T17:22Z. fxd tasks took 15-21 min; TSE adds a sim (~10-15 min, parallel); time = ~2-3x.
set -uo pipefail
export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/xorshift_predec.mlir HOLD_VEC=research/data/fifteen/vec_xorshift_hold.hex TSE_VEC=research/data/fifteen/vec_xorshift.hex
research/tools/fifteen/eval_task.sh fxdt_$TASK xorshift research/data/xorshift_sizes_T3s50_fr4_bench.vh $TASK research/data/fifteen/vec_xorshift.hex research/data/eventgraph/gate/xor17.hex research/data/eventgraph/gate/xor17.exp BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
