#!/bin/bash
#CLUSTER array=1-32 cores=8 mem=32G time=60
# fcolsz2_s: STATIC_ONLY rerun of fcolsz2 (same seeds = same routes): eval.txt's static line dropped every rule E row until 2026-11-15 (JOURNAL correction); report_rows_*.txt keeps every row now.
export STATIC_ONLY=1
# fcolsz2: fcolsz with both control merges back at 2 (7 of 31 fcolsz routes missed rule A on the merge index).
set -uo pipefail
research/tools/fifteen/eval_task.sh fcolsz2_s_$TASK collatz research/data/collatz_sizes_T3cdb_nl2_bench.vh $TASK research/data/fifteen/vec_collatz.hex research/data/eventgraph/gate/col13.hex research/data/eventgraph/gate/col13.exp BDC_CONST_DATA=1 BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_NO_LINK=ulink_n28__1 > "$OUT/log_eval.txt" 2>&1
