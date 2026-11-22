#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=60
# fc64sel3_ps: STATIC_ONLY rerun of fc64sel3 (same seeds = same routes) with CA_EXTRA=--shrink-selects: corner_audit may propose mux delays (now checked by rule M, the A'm rows, 2026-11-16) and select links (rule E). Proposals -> per-cell max -> next sizes.
set -uo pipefail
export STATIC_ONLY=1 CA_EXTRA=--shrink-selects BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/collatz64_preeq2.mlir HOLD_VEC=research/data/fifteen/vec_collatz_hold.hex
research/tools/fifteen/eval_task.sh fc64sel3_ps_$TASK collatz64 research/data/collatz64_sizes_T4cdb_h4s3_bench.vh $TASK research/data/fifteen/vec_collatz.hex research/data/eventgraph/gate/c6414.hex research/data/eventgraph/gate/c6414.exp BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
