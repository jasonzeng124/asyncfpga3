#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=60
# fc64eq_s: STATIC_ONLY rerun of fc64eq (same seeds = same routes): eval.txt's static line dropped every rule E row until 2026-11-15 (JOURNAL correction); report_rows_*.txt keeps every row now.
# fc64eq: collatz64, the loop test reads n == 2 instead of n' == 1 (pre_eq2.py), h2 sizes, item 24 knobs less the dropped link (n30 is gone). Static check with C-element joins. Compare with fc64h2 seed by seed.
set -uo pipefail
export STATIC_ONLY=1 BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/collatz64_preeq2.mlir
export STATIC_ONLY=1 HOLD_VEC=research/data/fifteen/vec_collatz_hold.hex
research/tools/fifteen/eval_task.sh fc64eq_s_$TASK collatz64 research/data/collatz64_sizes_T4cdb_h2_bench.vh $TASK research/data/fifteen/vec_collatz.hex research/data/eventgraph/gate/c6414.hex research/data/eventgraph/gate/c6414.exp BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
