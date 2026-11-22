#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=60
# fc64sel0_s: STATIC_ONLY rerun of fc64sel0 (same seeds = same routes): eval.txt's static line dropped every rule E row until 2026-11-15 (JOURNAL correction); report_rows_*.txt keeps every row now.
# fc64sel0: collatz64 item 26's structure (pre_eq2, h4 = fc64eq3) with the select links' DELAY at 0 (collatz64_sizes_T4cdb_h4s0_bench.vh; the select rule is withdrawn, PROGRAM 2026-11-15). Every check incl.
# hold_bits and TSE (step 5). The owner's bar: the select checks must FAIL on a raced select in each kernel family --
# this is that family's attempt; if no route races, it is the gain. Submitted 2026-11-15T17:24Z.
set -uo pipefail
export STATIC_ONLY=1 BD_SKEW_AND_JOIN=1 MLIR_OVERRIDE=research/data/fifteen/collatz64_preeq2.mlir HOLD_VEC=research/data/fifteen/vec_collatz_hold.hex TSE_VEC=research/data/fifteen/vec_collatz.hex
research/tools/fifteen/eval_task.sh fc64sel0_s_$TASK collatz64 research/data/collatz64_sizes_T4cdb_h4s0_bench.vh $TASK research/data/fifteen/vec_collatz.hex research/data/eventgraph/gate/c6414.hex research/data/eventgraph/gate/c6414.exp BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 > "$OUT/log_eval.txt" 2>&1
