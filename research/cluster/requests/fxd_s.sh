#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=60
# fxd_s: STATIC_ONLY rerun of fxd (same seeds = same routes): eval.txt's static line dropped every rule E row until 2026-11-15 (JOURNAL correction); report_rows_*.txt keeps every row now.
# fxd: xorshift lever 8, pre_dec alone (research/tools/fifteen/pre_dec.py: the loop test is i < n-1, n-1 computed once before the loop). fr4 sizes (new instances at bdc defaults), item 23's knobs less n30__0 (gone). Static check with C-element joins. Local seed 10 (no spec): latency 414 cycles vs 499 (xf5_10). Compare latency with fxf5 / fxs5 seed by seed.
set -uo pipefail
export STATIC_ONLY=1 BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/xorshift_predec.mlir HOLD_VEC=research/data/fifteen/vec_xorshift_hold.hex
research/tools/fifteen/eval_task.sh fxd_s_$TASK xorshift research/data/xorshift_sizes_T3s50_fr4_bench.vh $TASK research/data/fifteen/vec_xorshift.hex research/data/eventgraph/gate/xor17.hex research/data/eventgraph/gate/xor17.exp BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
