#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=90
# fcsel3a: collatz item 28's structure with uselect0 16 -> 7 and uaddi0 12 -> 9 (nl6s3a: corner_audit's proposal on seed 20 after the A' join-peer fix, 2026-11-16). Every check incl. hold_bits and TSE. Local seed 20: P 21.27 ns (item 28: 25.81), latency 468 vs 566, gates 3 x 13/13, static and hold clean. Compare with fcsel3m seed by seed.
set -uo pipefail
export BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/collatz_preeq2.mlir HOLD_VEC=research/data/fifteen/vec_collatz_hold.hex TSE_VEC=research/data/fifteen/vec_collatz.hex
research/tools/fifteen/eval_task.sh fcsel3a_$TASK collatz research/data/collatz_sizes_T3cdb_nl6s3a_bench.vh $TASK research/data/fifteen/vec_collatz.hex research/data/eventgraph/gate/col13.hex research/data/eventgraph/gate/col13.exp BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
