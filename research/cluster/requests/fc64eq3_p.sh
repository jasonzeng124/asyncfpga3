#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=60
# fc64eq3_p: STATIC_ONLY rerun of fc64eq3 (same seeds = same routes) with corner_audit's A' fix (2026-11-16: the cell's own request-join C nodes are no longer data peers; they made A' refuse cells whose join takes a reset or a folded constant's request). Proposals -> per-cell max -> next sizes.
set -uo pipefail
export STATIC_ONLY=1 BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/collatz64_preeq2.mlir
export STATIC_ONLY=1 HOLD_VEC=research/data/fifteen/vec_collatz_hold.hex
research/tools/fifteen/eval_task.sh fc64eq3_p_$TASK collatz64 research/data/collatz64_sizes_T4cdb_h4_bench.vh $TASK research/data/fifteen/vec_collatz.hex research/data/eventgraph/gate/c6414.hex research/data/eventgraph/gate/c6414.exp BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
