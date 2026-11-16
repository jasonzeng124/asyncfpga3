#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=60
# fcsel3m_p: STATIC_ONLY rerun of fcsel3m (collatz item 28; same seeds = same routes) with corner_audit's A' fix (2026-11-16: the cell's own request-join C nodes are no longer data peers; they made A' refuse uselect0, whose join takes the reset flop and the folded constant's request). Local seed 20: uselect0 16 -> 7 proposed (A' +5539 at 16). Proposals -> per-cell max -> next sizes.
set -uo pipefail
export STATIC_ONLY=1 BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/collatz_preeq2.mlir
research/tools/fifteen/eval_task.sh fcsel3m_p_$TASK collatz research/data/collatz_sizes_T3cdb_nl6s3m_bench.vh $TASK research/data/fifteen/vec_collatz.hex research/data/eventgraph/gate/col13.hex research/data/eventgraph/gate/col13.exp BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
