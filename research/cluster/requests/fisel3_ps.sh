#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=60
# fisel3_ps: STATIC_ONLY rerun of fisel3 (same seeds = same routes) with CA_EXTRA=--shrink-selects: corner_audit may propose mux delays (now checked by rule M, the A'm rows, 2026-11-16) and select links (rule E). Proposals -> per-cell max -> next sizes.
set -uo pipefail
export STATIC_ONLY=1 CA_EXTRA=--shrink-selects HOLD_VEC=research/data/fifteen/vec_ipow_hold.hex
research/tools/fifteen/eval_task.sh fisel3_ps_$TASK ipow research/data/ipow_dsp1_sizes_T9s75_h4s3_bench.vh $TASK research/data/fifteen/vec_ipow.hex research/data/eventgraph/gate/ipow17.hex research/data/eventgraph/gate/ipow17.exp BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
