#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=60
# fxd_ps: STATIC_ONLY rerun of fxd_p (same seeds = same routes) with CA_EXTRA=--shrink-selects: corner_audit may propose mux delays (now checked by rule M, the A'm rows, 2026-11-16) and select links (rule E). Proposals -> per-cell max -> next sizes.
set -uo pipefail
export STATIC_ONLY=1 CA_EXTRA=--shrink-selects STATIC_ONLY=1 BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/xorshift_predec.mlir HOLD_VEC=research/data/fifteen/vec_xorshift_hold.hex
research/tools/fifteen/eval_task.sh fxd_ps_$TASK xorshift research/data/xorshift_sizes_T3s50_fr4_bench.vh $TASK research/data/fifteen/vec_xorshift.hex research/data/eventgraph/gate/xor17.hex research/data/eventgraph/gate/xor17.exp BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
