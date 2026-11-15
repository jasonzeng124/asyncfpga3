#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=60
# fc64eq3_s: STATIC_ONLY rerun of fc64eq3 (same seeds = same routes): eval.txt's static line dropped every rule E row until 2026-11-15 (JOURNAL correction); report_rows_*.txt keeps every row now.
# fc64eq3: fc64eq2 with sizes h4 (ucmpi2 15 -> 16, n7 hold pads from fc64eq2).
set -uo pipefail
export STATIC_ONLY=1 BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/collatz64_preeq2.mlir
export STATIC_ONLY=1 HOLD_VEC=research/data/fifteen/vec_collatz_hold.hex
research/tools/fifteen/eval_task.sh fc64eq3_s_$TASK collatz64 research/data/collatz64_sizes_T4cdb_h4_bench.vh $TASK research/data/fifteen/vec_collatz.hex research/data/eventgraph/gate/c6414.hex research/data/eventgraph/gate/c6414.exp BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
