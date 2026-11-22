#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=60
# fipowh4_p: STATIC_ONLY rerun of fipowh4 (same seeds = same routes) with corner_audit's A' fix (2026-11-16: the cell's own request-join C nodes are no longer data peers; they made A' refuse cells whose join takes a reset or a folded constant's request). Proposals -> per-cell max -> next sizes.
set -uo pipefail
export STATIC_ONLY=1 HOLD_VEC=research/data/fifteen/vec_ipow_hold.hex
research/tools/fifteen/eval_task.sh fipowh4_p_$TASK ipow research/data/ipow_dsp1_sizes_T9s75_h4_bench.vh $TASK research/data/fifteen/vec_ipow.hex research/data/eventgraph/gate/ipow17.hex research/data/eventgraph/gate/ipow17.exp BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
