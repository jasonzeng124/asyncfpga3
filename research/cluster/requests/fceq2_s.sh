#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=60
# fceq2_s: STATIC_ONLY rerun of fceq2 (same seeds = same routes): eval.txt's static line dropped every rule E row until 2026-11-15 (JOURNAL correction); report_rows_*.txt keeps every row now.
# fceq2: fceq (collatz, exit test n == 2) with sizes nl6 = nl5 (pad rounds 1-3 on the old structure) + the pads from fcol5 and fceq rows.
set -uo pipefail
export STATIC_ONLY=1 BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/collatz_preeq2.mlir
export STATIC_ONLY=1 HOLD_VEC=research/data/fifteen/vec_collatz_hold.hex
research/tools/fifteen/eval_task.sh fceq2_s_$TASK collatz research/data/collatz_sizes_T3cdb_nl6_bench.vh $TASK research/data/fifteen/vec_collatz.hex research/data/eventgraph/gate/col13.hex research/data/eventgraph/gate/col13.exp BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
